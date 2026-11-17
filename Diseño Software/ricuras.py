"""Ricuras: pedidos por QR para el puesto de comida de la universidad.

Compradores: entran por QR a "/", piden sin crear cuenta y conservan sus pedidos
             solo mientras dure la sesión del navegador.
Vendedor:    entra a "/vendedor" con el usuario y la clave guardados en la base
             de datos (tabla vendedores).

Ejecutar:  python ricuras.py
Dependencia obligatoria: Flask. Opcional para el QR: qrcode.
Variables de entorno: VENDEDOR_USUARIO, VENDEDOR_CLAVE, SECRET_KEY, BASE_URL,
                      PORT, COOKIE_SECURE, DATABASE_URL.

Base de datos: si DATABASE_URL está definida (por ejemplo, la cadena de
Supabase/Postgres), la app guarda todo allí. Si no, usa el archivo local
ricuras.db (SQLite). Las credenciales se leen de .env si existe.

Si la tabla vendedores está vacía, el primer arranque crea la cuenta
admin / ricuras123 y la muestra en la consola. Cámbiala en "Mi cuenta".
Si VENDEDOR_USUARIO y VENDEDOR_CLAVE están definidas, se crea o actualiza esa
cuenta. Si SECRET_KEY no está definida, se crea una clave aleatoria persistente
en .ricuras_secret junto a este archivo.
"""

from __future__ import annotations

import csv
import io
import os
import re
import secrets
import sqlite3
import time
from datetime import date, datetime
from functools import wraps
from urllib.parse import urlsplit

from flask import (
    Flask,
    Response,
    abort,
    flash,
    g,
    jsonify,
    redirect,
    render_template,
    request,
    session,
    url_for,
)
from jinja2 import DictLoader
from werkzeug.security import check_password_hash, generate_password_hash

try:
    from dotenv import load_dotenv
except ImportError:  # python-dotenv es opcional
    load_dotenv = None

try:
    import psycopg
    from psycopg.rows import dict_row
except ImportError:  # psycopg solo hace falta si se usa Supabase/Postgres
    psycopg = None
    dict_row = None

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
if load_dotenv is not None:
    load_dotenv(os.path.join(BASE_DIR, ".env"))
DB_PATH = os.path.join(BASE_DIR, "ricuras.db")
SECRET_PATH = os.path.join(BASE_DIR, ".ricuras_secret")
USUARIO_INICIAL = "admin"
CLAVE_INICIAL = "ricuras123"

# Si DATABASE_URL está definida (por ejemplo, la cadena de Supabase), la app
# usa Postgres. Si no, sigue usando el archivo local ricuras.db (SQLite).
DATABASE_URL = os.environ.get("DATABASE_URL", "").strip()
USAR_POSTGRES = bool(DATABASE_URL)
ORDEN_DETALLE = "id" if USAR_POSTGRES else "rowid"


def cargar_secret():
    """Usa SECRET_KEY del entorno o una clave aleatoria persistente local."""
    clave = os.environ.get("SECRET_KEY", "").strip()
    if clave:
        return clave
    try:
        if os.path.exists(SECRET_PATH):
            with open(SECRET_PATH, "r", encoding="utf-8") as archivo:
                guardada = archivo.read().strip()
            if guardada:
                return guardada
        nueva = secrets.token_hex(32)
        with open(SECRET_PATH, "w", encoding="utf-8") as archivo:
            archivo.write(nueva)
        print("SECRET_KEY generada en .ricuras_secret. Define SECRET_KEY en producción.")
        return nueva
    except OSError:
        print("No se pudo guardar .ricuras_secret; la sesión se reiniciará al cerrar.")
        return secrets.token_hex(32)


app = Flask(__name__)
app.secret_key = cargar_secret()
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.environ.get("COOKIE_SECURE", "0") == "1",
    MAX_CONTENT_LENGTH=64 * 1024,
)
app.jinja_env.autoescape = True

ESTADOS = {
    "pago_pendiente": "Pago por confirmar",
    "recibido": "Recibido",
    "preparando": "En preparación",
    "listo": "Listo para recoger",
    "entregado": "Entregado",
    "cancelado": "Cancelado",
}
ESTADOS_ACTIVOS = ("pago_pendiente", "recibido", "preparando", "listo")
SIGUIENTE = {
    "recibido": ("preparando", "Empezar a preparar"),
    "preparando": ("listo", "Marcar listo"),
    "listo": ("entregado", "Entregado"),
}
PASOS = (
    ("recibido", "Recibido"),
    ("preparando", "En preparación"),
    ("listo", "Listo para recoger"),
    ("entregado", "Entregado"),
)
PAGOS = {"efectivo": "Efectivo", "nequi": "Nequi"}
PAGO_ESTADOS = {
    "pendiente": "Pago por confirmar",
    "confirmado": "Pago confirmado",
    "rechazado": "Pago rechazado",
    "no_aplica": "Pago en el puesto",
}
MESES = (
    "enero", "febrero", "marzo", "abril", "mayo", "junio",
    "julio", "agosto", "septiembre", "octubre", "noviembre", "diciembre",
)


class ErrorUsuario(Exception):
    """Error esperado con un mensaje que se puede mostrar tal cual."""

    def __init__(self, mensaje, codigo=400):
        super().__init__(mensaje)
        self.mensaje = mensaje
        self.codigo = codigo


# ---------------------------------------------------------------------------
# Utilidades
# ---------------------------------------------------------------------------


def ahora():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def hoy():
    return date.today().isoformat()


def limpiar_espacios(texto):
    return re.sub(r"\s+", " ", re.sub(r"[\x00-\x1f\x7f]+", " ", texto)).strip()


class Fila(dict):
    """Fila de Postgres con acceso por nombre y por posición, como sqlite3.Row."""

    def __init__(self, datos):
        super().__init__(datos)
        self._valores = tuple(datos.values())

    def __getitem__(self, clave):
        if isinstance(clave, int):
            return self._valores[clave]
        return super().__getitem__(clave)


def adaptar_sql(sql):
    """Traduce el SQL escrito para SQLite al dialecto de Postgres."""
    sql = re.sub(
        r"([A-Za-z_][A-Za-z0-9_.]*)\s*=\s*\?\s+COLLATE\s+NOCASE",
        r"LOWER(\1)=LOWER(?)",
        sql,
        flags=re.IGNORECASE,
    )
    sql = re.sub(r"\s+COLLATE\s+NOCASE", "", sql, flags=re.IGNORECASE)
    if re.match(r"\s*INSERT\s+OR\s+IGNORE\s+", sql, flags=re.IGNORECASE):
        sql = re.sub(
            r"^\s*INSERT\s+OR\s+IGNORE\s+", "INSERT ", sql, flags=re.IGNORECASE
        )
        if "ON CONFLICT" not in sql.upper():
            sql = sql.rstrip().rstrip(";") + " ON CONFLICT DO NOTHING"
    sql = re.sub(r"\bBEGIN\s+IMMEDIATE\b", "BEGIN", sql, flags=re.IGNORECASE)
    return sql.replace("?", "%s")


class CursorPG:
    def __init__(self, cursor):
        self._cursor = cursor

    def fetchone(self):
        fila = self._cursor.fetchone()
        return None if fila is None else Fila(fila)

    def fetchall(self):
        return [Fila(fila) for fila in self._cursor.fetchall()]

    def __iter__(self):
        for fila in self._cursor:
            yield Fila(fila)

    @property
    def rowcount(self):
        return self._cursor.rowcount


class ConexionPG:
    """Envoltura mínima para que psycopg se comporte como sqlite3."""

    def __init__(self, conexion):
        self._conexion = conexion

    def execute(self, sql, parametros=()):
        cursor = self._conexion.cursor()
        cursor.execute(adaptar_sql(sql), parametros)
        return CursorPG(cursor)

    def executemany(self, sql, filas):
        cursor = self._conexion.cursor()
        cursor.executemany(adaptar_sql(sql), filas)

    def commit(self):
        if not self._conexion.autocommit:
            self._conexion.commit()

    def rollback(self):
        if not self._conexion.autocommit:
            self._conexion.rollback()

    def close(self):
        self._conexion.close()


ERRORES_BD = (sqlite3.Error,)
if psycopg is not None:
    ERRORES_BD = (sqlite3.Error, psycopg.Error)


def conectar():
    if USAR_POSTGRES:
        if psycopg is None:
            raise RuntimeError(
                "DATABASE_URL está definida pero psycopg no está instalado. "
                "Ejecuta: pip install \"psycopg[binary]\""
            )
        return ConexionPG(
            psycopg.connect(DATABASE_URL, autocommit=True, row_factory=dict_row)
        )
    conexion = sqlite3.connect(DB_PATH, isolation_level=None, timeout=10)
    conexion.row_factory = sqlite3.Row
    conexion.execute("PRAGMA busy_timeout=10000")
    return conexion


def db():
    if "db" not in g:
        g.db = conectar()
    return g.db


@app.teardown_appcontext
def cerrar_db(_error=None):
    conexion = g.pop("db", None)
    if conexion is not None:
        conexion.close()


def transaccion(accion):
    """Ejecuta una escritura bajo BEGIN IMMEDIATE y garantiza rollback."""
    conexion = db()
    conexion.execute("BEGIN IMMEDIATE")
    try:
        resultado = accion(conexion)
        conexion.execute("COMMIT")
        return resultado
    except Exception:
        try:
            conexion.execute("ROLLBACK")
        except ERRORES_BD:
            pass
        raise


def insertar_id(conexion, sql, parametros):
    """Inserta y devuelve el id generado, en SQLite o en Postgres."""
    if USAR_POSTGRES:
        fila = conexion.execute(sql + " RETURNING id", parametros).fetchone()
        return fila["id"]
    return conexion.execute(sql, parametros).lastrowid


def obtener_ajuste(clave, por_defecto=""):
    fila = db().execute(
        "SELECT valor FROM ajustes WHERE clave=?", (clave,)
    ).fetchone()
    return fila["valor"] if fila else por_defecto


def guardar_ajuste(clave, valor):
    db().execute(
        "INSERT INTO ajustes(clave, valor) VALUES(?, ?) "
        "ON CONFLICT(clave) DO UPDATE SET valor=excluded.valor",
        (clave, valor),
    )


def csrf_token():
    token = session.get("csrf")
    if not token:
        token = secrets.token_urlsafe(32)
        session["csrf"] = token
    return token


def validar_csrf():
    esperado = session.get("csrf", "")
    recibido = request.form.get("csrf", "")
    if not esperado or not recibido or not secrets.compare_digest(esperado, recibido):
        abort(
            400,
            description=(
                "El formulario expiró o no es válido. Recarga la página y vuelve "
                "a intentarlo."
            ),
        )


def solo_vendedor(funcion):
    @wraps(funcion)
    def envoltura(*args, **kwargs):
        if not session.get("vendedor"):
            return redirect(url_for("login", next=request.path))
        return funcion(*args, **kwargs)

    return envoltura


def puede_ver(pid):
    if session.get("vendedor"):
        return True
    pedidos = session.get("pedidos", [])
    return isinstance(pedidos, list) and pid in pedidos


def recordar_pedido(pid):
    pedidos = session.get("pedidos", [])
    if not isinstance(pedidos, list):
        pedidos = []
    pedidos = [p for p in pedidos if isinstance(p, int)]
    if pid not in pedidos:
        pedidos.append(pid)
    session["pedidos"] = pedidos[-30:]


def devolver_stock(conexion, pedido_id):
    filas = conexion.execute(
        "SELECT item_id, cantidad FROM detalle WHERE pedido_id=?", (pedido_id,)
    ).fetchall()
    for fila in filas:
        if fila["item_id"] is not None and fila["cantidad"]:
            conexion.execute(
                "UPDATE items SET stock=stock+? WHERE id=?",
                (fila["cantidad"], fila["item_id"]),
            )


def leer_entero(valor, etiqueta, minimo, maximo):
    texto = (valor or "").strip() if isinstance(valor, str) else ""
    if not re.fullmatch(r"\d{1,9}", texto):
        raise ErrorUsuario(
            f"{etiqueta} debe ser un número entero, sin puntos ni comas, "
            f"entre {minimo} y {maximo}."
        )
    numero = int(texto)
    if numero < minimo or numero > maximo:
        raise ErrorUsuario(
            f"{etiqueta} debe estar entre {minimo} y {maximo}. Corrige el valor."
        )
    return numero


def validar_producto_formulario(form):
    nombre = limpiar_espacios(form.get("nombre", "") if isinstance(form.get("nombre"), str) else "")
    if not 1 <= len(nombre) <= 60:
        raise ErrorUsuario(
            "El nombre del producto debe tener entre 1 y 60 caracteres. "
            "Escríbelo de nuevo."
        )
    precio = leer_entero(form.get("precio", ""), "El precio", 0, 10_000_000)
    stock = leer_entero(form.get("stock", ""), "Las unidades", 0, 100_000)
    return nombre, precio, stock, 1 if form.get("activo") else 0


def fecha_iso(valor):
    try:
        return date.fromisoformat(valor).isoformat()
    except (TypeError, ValueError):
        return None


def huella_panel():
    fila = db().execute(
        "SELECT COUNT(*) AS n, COALESCE(MAX(actualizado), '') AS u "
        "FROM pedidos WHERE estado IN (?, ?, ?, ?)",
        ESTADOS_ACTIVOS,
    ).fetchone()
    return f"{fila['n']}|{fila['u']}"


def qrcode_disponible():
    try:
        import qrcode  # noqa: F401
        import qrcode.image.svg  # noqa: F401

        return True
    except Exception:
        return False


def url_publica():
    base = os.environ.get("BASE_URL", "").strip()
    if not base:
        return request.url_root.rstrip("/")
    if not re.match(r"^https?://", base, re.I):
        base = "http://" + base
    return base.rstrip("/")


def es_url_local(url):
    host = (urlsplit(url).hostname or "").lower()
    return host in {"localhost", "127.0.0.1", "0.0.0.0", "::1"}


def celda_csv(valor):
    texto = "" if valor is None else str(valor)
    if texto.startswith(("=", "+", "-", "@", "\t", "\r")):
        return "'" + texto
    return texto


# ---------------------------------------------------------------------------
# Base de datos y migración
# ---------------------------------------------------------------------------


ESQUEMA_POSTGRES = (
    """CREATE TABLE IF NOT EXISTS items(
        id SERIAL PRIMARY KEY,
        nombre TEXT NOT NULL,
        precio INTEGER NOT NULL,
        stock INTEGER NOT NULL DEFAULT 0,
        activo INTEGER NOT NULL DEFAULT 1
    )""",
    """CREATE TABLE IF NOT EXISTS pedidos(
        id SERIAL PRIMARY KEY,
        turno INTEGER NOT NULL,
        fecha TEXT NOT NULL,
        cliente TEXT NOT NULL DEFAULT 'Sin nombre',
        estado TEXT NOT NULL DEFAULT 'recibido',
        total INTEGER NOT NULL,
        creado TEXT NOT NULL DEFAULT '',
        pago TEXT NOT NULL DEFAULT 'efectivo',
        pago_estado TEXT NOT NULL DEFAULT 'no_aplica',
        comprobante TEXT,
        nequi_numero TEXT,
        actualizado TEXT
    )""",
    """CREATE TABLE IF NOT EXISTS detalle(
        id BIGSERIAL PRIMARY KEY,
        pedido_id INTEGER NOT NULL,
        item_id INTEGER NOT NULL,
        nombre TEXT NOT NULL,
        cantidad INTEGER NOT NULL,
        precio INTEGER NOT NULL
    )""",
    """CREATE TABLE IF NOT EXISTS ajustes(
        clave TEXT PRIMARY KEY,
        valor TEXT NOT NULL
    )""",
    """CREATE TABLE IF NOT EXISTS vendedores(
        id SERIAL PRIMARY KEY,
        usuario TEXT NOT NULL UNIQUE,
        clave_hash TEXT NOT NULL,
        activo INTEGER NOT NULL DEFAULT 1,
        clave_inicial INTEGER NOT NULL DEFAULT 0,
        creado TEXT NOT NULL DEFAULT ''
    )""",
    "CREATE INDEX IF NOT EXISTS idx_pedidos_fecha ON pedidos(fecha)",
    "CREATE INDEX IF NOT EXISTS idx_pedidos_estado ON pedidos(estado)",
    "CREATE INDEX IF NOT EXISTS idx_detalle_pedido ON detalle(pedido_id)",
    "CREATE UNIQUE INDEX IF NOT EXISTS idx_vendedores_usuario "
    "ON vendedores(LOWER(usuario))",
)

SEMILLA_ITEMS = [
    ("Salchipapa", 10000, 8),
    ("Empanada", 3500, 20),
    ("Arepa de huevo", 3500, 15),
    ("Patacón", 3500, 15),
    ("Jugo natural", 4000, 10),
    ("Gaseosa", 3000, 24),
    ("Dedito de queso", 2500, 15),
    ("Papa rellena", 3500, 15),
]


def normalizar_datos(conexion):
    """Completa filas viejas y siembra el menú si la base está vacía."""
    conexion.execute(
        "UPDATE pedidos SET cliente='Sin nombre' "
        "WHERE cliente IS NULL OR TRIM(cliente)=''"
    )
    conexion.execute("UPDATE pedidos SET estado='recibido' WHERE estado='nuevo'")
    conexion.execute("UPDATE pedidos SET pago='efectivo' WHERE pago IS NULL OR pago=''")
    conexion.execute(
        "UPDATE pedidos SET pago_estado='no_aplica' "
        "WHERE pago_estado IS NULL OR pago_estado=''"
    )
    conexion.execute(
        "UPDATE pedidos SET actualizado=COALESCE(creado, ?) WHERE actualizado IS NULL",
        (ahora(),),
    )
    conexion.execute("UPDATE detalle SET nombre='Producto' WHERE nombre IS NULL")
    if conexion.execute("SELECT COUNT(*) FROM items").fetchone()[0] == 0:
        conexion.executemany(
            "INSERT INTO items(nombre, precio, stock, activo) VALUES(?, ?, ?, 1)",
            SEMILLA_ITEMS,
        )
    conexion.execute(
        "INSERT OR IGNORE INTO ajustes(clave, valor) VALUES('nequi_numero', '')"
    )


def init_db_postgres():
    conexion = conectar()
    try:
        for sentencia in ESQUEMA_POSTGRES:
            conexion.execute(sentencia)

        for nombre, definicion in (
            ("pago", "TEXT NOT NULL DEFAULT 'efectivo'"),
            ("pago_estado", "TEXT NOT NULL DEFAULT 'no_aplica'"),
            ("comprobante", "TEXT"),
            ("nequi_numero", "TEXT"),
            ("actualizado", "TEXT"),
        ):
            conexion.execute(
                f"ALTER TABLE pedidos ADD COLUMN IF NOT EXISTS {nombre} {definicion}"
            )
        conexion.execute(
            "ALTER TABLE vendedores ADD COLUMN IF NOT EXISTS "
            "clave_inicial INTEGER NOT NULL DEFAULT 0"
        )

        normalizar_datos(conexion)
        conexion.commit()
    finally:
        conexion.close()


def init_db():
    if USAR_POSTGRES:
        init_db_postgres()
    else:
        init_db_sqlite()


def init_db_sqlite():
    conexion = sqlite3.connect(DB_PATH, timeout=10)
    conexion.row_factory = sqlite3.Row
    try:
        conexion.execute("PRAGMA journal_mode=WAL")
        conexion.executescript(
            """
            CREATE TABLE IF NOT EXISTS items(
                id INTEGER PRIMARY KEY,
                nombre TEXT NOT NULL,
                precio INTEGER NOT NULL,
                stock INTEGER NOT NULL DEFAULT 0,
                activo INTEGER NOT NULL DEFAULT 1
            );
            CREATE TABLE IF NOT EXISTS pedidos(
                id INTEGER PRIMARY KEY,
                turno INTEGER NOT NULL,
                fecha TEXT NOT NULL,
                cliente TEXT NOT NULL DEFAULT 'Sin nombre',
                estado TEXT NOT NULL DEFAULT 'recibido',
                total INTEGER NOT NULL,
                creado TEXT NOT NULL DEFAULT '',
                pago TEXT NOT NULL DEFAULT 'efectivo',
                pago_estado TEXT NOT NULL DEFAULT 'no_aplica',
                comprobante TEXT,
                nequi_numero TEXT,
                actualizado TEXT
            );
            CREATE TABLE IF NOT EXISTS detalle(
                pedido_id INTEGER NOT NULL,
                item_id INTEGER NOT NULL,
                nombre TEXT NOT NULL,
                cantidad INTEGER NOT NULL,
                precio INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS ajustes(
                clave TEXT PRIMARY KEY,
                valor TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS vendedores(
                id INTEGER PRIMARY KEY,
                usuario TEXT NOT NULL UNIQUE COLLATE NOCASE,
                clave_hash TEXT NOT NULL,
                activo INTEGER NOT NULL DEFAULT 1,
                clave_inicial INTEGER NOT NULL DEFAULT 0,
                creado TEXT NOT NULL DEFAULT ''
            );
            CREATE INDEX IF NOT EXISTS idx_pedidos_fecha ON pedidos(fecha);
            CREATE INDEX IF NOT EXISTS idx_pedidos_estado ON pedidos(estado);
            CREATE INDEX IF NOT EXISTS idx_detalle_pedido ON detalle(pedido_id);
            """
        )

        columnas = {fila["name"] for fila in conexion.execute("PRAGMA table_info(pedidos)")}
        nuevas = (
            ("pago", "TEXT NOT NULL DEFAULT 'efectivo'"),
            ("pago_estado", "TEXT NOT NULL DEFAULT 'no_aplica'"),
            ("comprobante", "TEXT"),
            ("nequi_numero", "TEXT"),
            ("actualizado", "TEXT"),
        )
        for nombre, definicion in nuevas:
            if nombre not in columnas:
                conexion.execute(f"ALTER TABLE pedidos ADD COLUMN {nombre} {definicion}")

        columnas_v = {
            fila["name"] for fila in conexion.execute("PRAGMA table_info(vendedores)")
        }
        if "clave_inicial" not in columnas_v:
            conexion.execute(
                "ALTER TABLE vendedores ADD COLUMN clave_inicial INTEGER NOT NULL DEFAULT 0"
            )

        normalizar_datos(conexion)
        conexion.commit()
    finally:
        conexion.close()


def configurar_vendedor():
    """Crea la cuenta inicial del vendedor si no hay ninguna en la base."""
    conexion = conectar()
    try:
        usuario_entorno = os.environ.get("VENDEDOR_USUARIO", "").strip()
        clave_entorno = os.environ.get("VENDEDOR_CLAVE", "")

        if usuario_entorno and clave_entorno:
            if not re.fullmatch(r"[A-Za-z0-9._-]{3,30}", usuario_entorno):
                print(
                    "Aviso: VENDEDOR_USUARIO debe tener entre 3 y 30 caracteres "
                    "y solo letras, números, punto, guion o guion bajo."
                )
            elif len(clave_entorno) < 8:
                print("Aviso: VENDEDOR_CLAVE debe tener al menos 8 caracteres.")
            else:
                fila = conexion.execute(
                    "SELECT id, clave_hash FROM vendedores "
                    "WHERE usuario=? COLLATE NOCASE",
                    (usuario_entorno,),
                ).fetchone()
                if fila is None:
                    conexion.execute(
                        "INSERT INTO vendedores(usuario, clave_hash, activo, "
                        "clave_inicial, creado) VALUES(?, ?, 1, 0, ?)",
                        (
                            usuario_entorno,
                            generate_password_hash(clave_entorno),
                            ahora(),
                        ),
                    )
                    print(
                        f"Usuario del vendedor “{usuario_entorno}” creado "
                        "desde el entorno."
                    )
                elif not check_password_hash(fila["clave_hash"], clave_entorno):
                    conexion.execute(
                        "UPDATE vendedores SET clave_hash=?, clave_inicial=0 "
                        "WHERE id=?",
                        (generate_password_hash(clave_entorno), fila["id"]),
                    )
                    print(
                        f"Clave del usuario “{usuario_entorno}” actualizada "
                        "desde el entorno."
                    )
                conexion.commit()

        total = conexion.execute("SELECT COUNT(*) FROM vendedores").fetchone()[0]
        if total == 0:
            conexion.execute(
                "INSERT INTO vendedores(usuario, clave_hash, activo, "
                "clave_inicial, creado) VALUES(?, ?, 1, 1, ?)",
                (
                    USUARIO_INICIAL,
                    generate_password_hash(CLAVE_INICIAL),
                    ahora(),
                ),
            )
            conexion.commit()
            print("=" * 62)
            print("  Cuenta inicial del vendedor creada:")
            print(f"  Usuario: {USUARIO_INICIAL}")
            print(f"  Clave:   {CLAVE_INICIAL}")
            print("  Cámbiala en el panel: Mi cuenta.")
            print("=" * 62)

        conexion.execute("DELETE FROM ajustes WHERE clave='pin_hash'")
        conexion.commit()
    finally:
        conexion.close()


# ---------------------------------------------------------------------------
# Comprador
# ---------------------------------------------------------------------------


@app.get("/")
def menu():
    items = db().execute(
        "SELECT id, nombre, precio, stock FROM items "
        "WHERE activo=1 ORDER BY id"
    ).fetchall()
    return render_template("menu.html", items=items, nequi=obtener_ajuste("nequi_numero"))


@app.post("/api/pedir")
def pedir():
    datos = request.get_json(silent=True)
    if not isinstance(datos, dict):
        return jsonify(ok=False, error="Envía el pedido en formato JSON."), 400

    pago = datos.get("pago")
    if pago not in PAGOS:
        return jsonify(ok=False, error="Elige un método de pago válido: efectivo o Nequi."), 400

    nombre_crudo = datos.get("cliente", "")
    if nombre_crudo is None:
        nombre_crudo = ""
    if not isinstance(nombre_crudo, str):
        return jsonify(ok=False, error="El nombre debe ser texto."), 400
    nombre = limpiar_espacios(nombre_crudo)
    if len(nombre) > 40:
        return jsonify(
            ok=False,
            error="El nombre no puede superar los 40 caracteres. Acórtalo e inténtalo de nuevo.",
        ), 400
    if not nombre:
        nombre = "Sin nombre"

    items_crudos = datos.get("items")
    if not isinstance(items_crudos, list) or not items_crudos:
        return jsonify(ok=False, error="Agrega al menos un producto al pedido."), 400
    if len(items_crudos) > 30:
        return jsonify(ok=False, error="El pedido tiene demasiados productos distintos."), 400

    pedido = {}
    for linea in items_crudos:
        if not isinstance(linea, dict):
            return jsonify(ok=False, error="Revisa los productos del pedido."), 400
        item_id = linea.get("id")
        cantidad = linea.get("cant")
        if type(item_id) is not int or type(cantidad) is not int:
            return jsonify(ok=False, error="Revisa las cantidades del pedido."), 400
        if item_id <= 0 or cantidad < 1 or cantidad > 50:
            return jsonify(
                ok=False,
                error="Cada producto debe llevar entre 1 y 50 unidades.",
            ), 400
        pedido[item_id] = pedido.get(item_id, 0) + cantidad
        if pedido[item_id] > 50:
            return jsonify(
                ok=False, error="No puedes pedir más de 50 unidades del mismo producto."
            ), 400

    def accion(conexion):
        nequi = obtener_ajuste("nequi_numero")
        if pago == "nequi" and not nequi:
            raise ErrorUsuario(
                "El vendedor todavía no configuró el número Nequi. Elige efectivo "
                "o avísale para que lo configure.",
                409,
            )

        total = 0
        lineas = []
        for item_id, cantidad in pedido.items():
            item = conexion.execute(
                "SELECT id, nombre, precio FROM items WHERE id=? AND activo=1",
                (item_id,),
            ).fetchone()
            if item is None:
                raise ErrorUsuario(
                    "Uno de los productos ya no está disponible. Actualiza el menú "
                    "y vuelve a armar el pedido.",
                    409,
                )
            actualizado = conexion.execute(
                "UPDATE items SET stock=stock-? "
                "WHERE id=? AND activo=1 AND stock>=?",
                (cantidad, item_id, cantidad),
            )
            if actualizado.rowcount != 1:
                unidad = "unidad disponible" if cantidad == 1 else "unidades disponibles"
                raise ErrorUsuario(
                    f"{item['nombre']} ya no tiene {cantidad} {unidad}. "
                    "Revisa las unidades que quedan y ajusta tu carrito.",
                    409,
                )
            lineas.append((item["id"], item["nombre"], cantidad, item["precio"]))
            total += cantidad * item["precio"]

        fecha = hoy()
        turno = conexion.execute(
            "SELECT COALESCE(MAX(turno), 0) + 1 FROM pedidos WHERE fecha=?",
            (fecha,),
        ).fetchone()[0]
        estado = "pago_pendiente" if pago == "nequi" else "recibido"
        pago_estado = "pendiente" if pago == "nequi" else "no_aplica"
        creado = ahora()
        pedido_id = insertar_id(
            conexion,
            "INSERT INTO pedidos(turno, fecha, cliente, estado, total, creado, "
            "pago, pago_estado, comprobante, nequi_numero, actualizado) "
            "VALUES(?, ?, ?, ?, ?, ?, ?, ?, NULL, ?, ?)",
            (
                turno, fecha, nombre, estado, total, creado,
                pago, pago_estado, nequi if pago == "nequi" else None, creado,
            ),
        )
        conexion.executemany(
            "INSERT INTO detalle(pedido_id, item_id, nombre, cantidad, precio) "
            "VALUES(?, ?, ?, ?, ?)",
            [(pedido_id, *linea) for linea in lineas],
        )
        return pedido_id, turno

    try:
        pedido_id, turno = transaccion(accion)
    except ErrorUsuario as error:
        return jsonify(ok=False, error=error.mensaje), error.codigo
    except ERRORES_BD:
        return jsonify(
            ok=False,
            error="El puesto está recibiendo muchos pedidos a la vez. "
            "Espera un momento e inténtalo otra vez.",
        ), 503

    recordar_pedido(pedido_id)
    return jsonify(
        ok=True,
        url=url_for("ver_pedido", pid=pedido_id),
        turno=turno,
    )


@app.get("/pedido/<int:pid>")
def ver_pedido(pid):
    if not puede_ver(pid):
        abort(404)
    conexion = db()
    pedido = conexion.execute("SELECT * FROM pedidos WHERE id=?", (pid,)).fetchone()
    if pedido is None:
        abort(404)
    detalle = conexion.execute(
        f"SELECT nombre, cantidad, precio FROM detalle WHERE pedido_id=? "
        f"ORDER BY {ORDEN_DETALLE}",
        (pid,),
    ).fetchall()
    claves = [clave for clave, _ in PASOS]
    indice = claves.index(pedido["estado"]) if pedido["estado"] in claves else -1
    return render_template(
        "pedido.html",
        p=pedido,
        det=detalle,
        estados=ESTADOS,
        pago_estados=PAGO_ESTADOS,
        pasos=PASOS,
        indice=indice,
        nequi_actual=obtener_ajuste("nequi_numero"),
    )


@app.get("/api/pedido/<int:pid>")
def estado_pedido(pid):
    if not puede_ver(pid):
        abort(404)
    pedido = db().execute(
        "SELECT estado, pago, pago_estado, actualizado FROM pedidos WHERE id=?",
        (pid,),
    ).fetchone()
    if pedido is None:
        abort(404)
    return jsonify(
        estado=pedido["estado"],
        estado_texto=ESTADOS.get(pedido["estado"], pedido["estado"]),
        pago=pedido["pago"],
        pago_estado=pedido["pago_estado"],
        pago_texto=PAGO_ESTADOS.get(pedido["pago_estado"], pedido["pago_estado"]),
        final=pedido["estado"] in {"entregado", "cancelado"},
        actualizado=pedido["actualizado"],
    )


@app.post("/pedido/<int:pid>/comprobante")
def guardar_comprobante(pid):
    if not puede_ver(pid):
        abort(404)
    validar_csrf()
    comprobante = request.form.get("comprobante", "")
    if not isinstance(comprobante, str):
        abort(400, description="El comprobante debe ser texto.")
    comprobante = re.sub(r"\s+", "", comprobante)
    if not re.fullmatch(r"[A-Za-z0-9-]{4,30}", comprobante):
        flash(
            "El comprobante debe tener entre 4 y 30 letras, números o guiones, "
            "sin espacios. Revísalo e inténtalo de nuevo.",
            "error",
        )
        return redirect(url_for("ver_pedido", pid=pid))

    def accion(conexion):
        pedido = conexion.execute(
            "SELECT estado, pago, pago_estado FROM pedidos WHERE id=?", (pid,)
        ).fetchone()
        if pedido is None:
            raise ErrorUsuario("Ese pedido ya no existe.", 404)
        if (
            pedido["pago"] != "nequi"
            or pedido["pago_estado"] != "pendiente"
            or pedido["estado"] != "pago_pendiente"
        ):
            raise ErrorUsuario(
                "Este pedido ya no admite cambios de comprobante porque el pago "
                "ya fue revisado.",
                409,
            )
        conexion.execute(
            "UPDATE pedidos SET comprobante=?, actualizado=? WHERE id=?",
            (comprobante, ahora(), pid),
        )

    try:
        transaccion(accion)
    except ErrorUsuario as error:
        flash(error.mensaje, "error")
        return redirect(url_for("ver_pedido", pid=pid))
    flash(
        "Comprobante guardado. El vendedor lo revisará y confirmará el pago.",
        "ok",
    )
    return redirect(url_for("ver_pedido", pid=pid) + "#pago")


@app.get("/mis-pedidos")
def mis_pedidos():
    ids = [p for p in session.get("pedidos", []) if isinstance(p, int)]
    pedidos = []
    if ids:
        ids = ids[-30:]
        marcas = ",".join("?" for _ in ids)
        pedidos = db().execute(
            f"SELECT id, turno, fecha, total, estado, pago FROM pedidos "
            f"WHERE id IN ({marcas}) ORDER BY fecha DESC, id DESC",
            ids,
        ).fetchall()
    return render_template(
        "mis_pedidos.html", pedidos=pedidos, estados=ESTADOS, pagos=PAGOS
    )


# ---------------------------------------------------------------------------
# Vendedor
# ---------------------------------------------------------------------------


@app.route("/vendedor/login", methods=["GET", "POST"])
def login():
    if session.get("vendedor"):
        return redirect(url_for("panel"))
    error = None
    if request.method == "POST":
        validar_csrf()
        usuario = request.form.get("usuario", "")
        clave = request.form.get("clave", "")
        if (
            not isinstance(usuario, str)
            or not isinstance(clave, str)
            or not usuario.strip()
            or not clave
            or len(usuario) > 30
            or len(clave) > 128
        ):
            error = "Escribe tu usuario y tu clave para entrar."
        else:
            fila = db().execute(
                "SELECT usuario, clave_hash, activo, clave_inicial "
                "FROM vendedores WHERE usuario=? COLLATE NOCASE",
                (usuario.strip(),),
            ).fetchone()
            if (
                fila is not None
                and fila["activo"]
                and check_password_hash(fila["clave_hash"], clave)
            ):
                session["vendedor"] = fila["usuario"]
                session["csrf"] = secrets.token_urlsafe(32)
                if fila["clave_inicial"]:
                    flash(
                        "Estás usando la clave inicial. Cámbiala en Mi cuenta.",
                        "error",
                    )
                destino = request.args.get("next", "")
                if (
                    not destino.startswith("/")
                    or destino.startswith("//")
                    or "\\" in destino
                ):
                    destino = url_for("panel")
                flash("Sesión iniciada. Ya puedes gestionar el puesto.", "ok")
                return redirect(destino)
            time.sleep(0.4)
            error = "Usuario o clave incorrectos. Revísalos e inténtalo de nuevo."
    return render_template("login.html", error=error)


@app.get("/vendedor/salir")
def salir():
    session.pop("vendedor", None)
    flash("Sesión del vendedor cerrada.", "ok")
    return redirect(url_for("menu"))


@app.route("/vendedor/cuenta", methods=["GET", "POST"])
@solo_vendedor
def cuenta():
    conexion = db()
    fila = conexion.execute(
        "SELECT id, usuario, clave_hash, clave_inicial FROM vendedores "
        "WHERE usuario=?",
        (session.get("vendedor"),),
    ).fetchone()
    if fila is None:
        session.pop("vendedor", None)
        flash("Tu cuenta ya no existe. Inicia sesión de nuevo.", "error")
        return redirect(url_for("login"))

    if request.method == "POST":
        validar_csrf()
        usuario_crudo = request.form.get("usuario", "")
        if not isinstance(usuario_crudo, str):
            usuario_crudo = ""
        usuario = limpiar_espacios(usuario_crudo)
        actual = request.form.get("clave_actual", "")
        nueva = request.form.get("clave_nueva", "")
        confirmar = request.form.get("clave_confirmar", "")
        if not isinstance(actual, str):
            actual = ""
        if not isinstance(nueva, str):
            nueva = ""
        if not isinstance(confirmar, str):
            confirmar = ""

        error = None
        if not re.fullmatch(r"[A-Za-z0-9._-]{3,30}", usuario):
            error = (
                "El usuario debe tener entre 3 y 30 caracteres: letras, "
                "números, punto, guion o guion bajo."
            )
        elif not check_password_hash(fila["clave_hash"], actual):
            error = "La clave actual no es correcta."
        elif nueva and len(nueva) < 8:
            error = "La nueva clave debe tener al menos 8 caracteres."
        elif len(nueva) > 128:
            error = "La nueva clave no puede superar los 128 caracteres."
        elif nueva and nueva != confirmar:
            error = "La confirmación no coincide con la nueva clave."

        if error:
            flash(error, "error")
            return redirect(url_for("cuenta"))

        def guardar(con):
            if usuario.lower() != fila["usuario"].lower():
                ocupado = con.execute(
                    "SELECT id FROM vendedores "
                    "WHERE usuario=? COLLATE NOCASE AND id<>?",
                    (usuario, fila["id"]),
                ).fetchone()
                if ocupado is not None:
                    raise ErrorUsuario("Ese usuario ya está en uso. Elige otro.")
            if nueva:
                con.execute(
                    "UPDATE vendedores SET usuario=?, clave_hash=?, "
                    "clave_inicial=0 WHERE id=?",
                    (usuario, generate_password_hash(nueva), fila["id"]),
                )
            else:
                con.execute(
                    "UPDATE vendedores SET usuario=? WHERE id=?",
                    (usuario, fila["id"]),
                )

        try:
            transaccion(guardar)
        except ErrorUsuario as exc:
            flash(exc.mensaje, "error")
            return redirect(url_for("cuenta"))

        session["vendedor"] = usuario
        if nueva:
            flash("Cuenta actualizada. La nueva clave ya está activa.", "ok")
        else:
            flash("Usuario actualizado.", "ok")
        return redirect(url_for("cuenta"))

    return render_template(
        "cuenta.html",
        usuario=fila["usuario"],
        clave_inicial=bool(fila["clave_inicial"]),
    )


@app.get("/vendedor")
@solo_vendedor
def panel():
    conexion = db()
    pedidos = conexion.execute(
        "SELECT * FROM pedidos WHERE estado IN (?, ?, ?, ?) "
        "ORDER BY CASE estado "
        "WHEN 'pago_pendiente' THEN 0 WHEN 'listo' THEN 1 "
        "WHEN 'preparando' THEN 2 ELSE 3 END, turno",
        ESTADOS_ACTIVOS,
    ).fetchall()
    detalle = {
        pedido["id"]: conexion.execute(
            "SELECT nombre, cantidad, precio FROM detalle "
            f"WHERE pedido_id=? ORDER BY {ORDEN_DETALLE}",
            (pedido["id"],),
        ).fetchall()
        for pedido in pedidos
    }
    pendientes = sum(1 for p in pedidos if p["estado"] == "pago_pendiente")
    listos = sum(1 for p in pedidos if p["estado"] == "listo")
    cocina = sum(1 for p in pedidos if p["estado"] in {"recibido", "preparando"})
    cuenta_actual = conexion.execute(
        "SELECT clave_inicial FROM vendedores WHERE usuario=?",
        (session.get("vendedor"),),
    ).fetchone()
    return render_template(
        "panel.html",
        pedidos=pedidos,
        det=detalle,
        estados=ESTADOS,
        pagos=PAGOS,
        pago_estados=PAGO_ESTADOS,
        sig=SIGUIENTE,
        pendientes=pendientes,
        listos=listos,
        cocina=cocina,
        nequi=obtener_ajuste("nequi_numero"),
        clave_inicial=bool(cuenta_actual and cuenta_actual["clave_inicial"]),
        fp=huella_panel(),
    )


@app.get("/vendedor/actualizaciones")
@solo_vendedor
def panel_actualizaciones():
    respuesta = jsonify(fp=huella_panel())
    respuesta.headers["Cache-Control"] = "no-store"
    return respuesta


@app.post("/vendedor/pedido/<int:pid>/confirmar-pago")
@solo_vendedor
def confirmar_pago(pid):
    validar_csrf()

    def accion(conexion):
        pedido = conexion.execute("SELECT * FROM pedidos WHERE id=?", (pid,)).fetchone()
        if pedido is None:
            raise ErrorUsuario("No encontramos ese pedido.", 404)
        if (
            pedido["pago"] != "nequi"
            or pedido["pago_estado"] != "pendiente"
            or pedido["estado"] != "pago_pendiente"
        ):
            raise ErrorUsuario(
                "Ese pedido no tiene un pago Nequi pendiente por confirmar.", 409
            )
        if not (pedido["comprobante"] or "").strip():
            raise ErrorUsuario(
                "Falta el comprobante del comprador. Pídeselo antes de confirmar "
                "el pago.",
                409,
            )
        conexion.execute(
            "UPDATE pedidos SET estado='recibido', pago_estado='confirmado', "
            "actualizado=? WHERE id=?",
            (ahora(), pid),
        )
        return pedido["turno"]

    try:
        turno = transaccion(accion)
    except ErrorUsuario as error:
        flash(error.mensaje, "error")
        return redirect(url_for("panel") + f"#pedido-{pid}")
    flash(f"Turno {turno}: pago Nequi confirmado.", "ok")
    return redirect(url_for("panel") + f"#pedido-{pid}")


@app.post("/vendedor/pedido/<int:pid>/rechazar-pago")
@solo_vendedor
def rechazar_pago(pid):
    validar_csrf()

    def accion(conexion):
        pedido = conexion.execute("SELECT * FROM pedidos WHERE id=?", (pid,)).fetchone()
        if pedido is None:
            raise ErrorUsuario("No encontramos ese pedido.", 404)
        if (
            pedido["pago"] != "nequi"
            or pedido["pago_estado"] != "pendiente"
            or pedido["estado"] != "pago_pendiente"
        ):
            raise ErrorUsuario(
                "Ese pedido no tiene un pago Nequi pendiente por rechazar.", 409
            )
        devolver_stock(conexion, pid)
        conexion.execute(
            "UPDATE pedidos SET estado='cancelado', pago_estado='rechazado', "
            "actualizado=? WHERE id=?",
            (ahora(), pid),
        )
        return pedido["turno"]

    try:
        turno = transaccion(accion)
    except ErrorUsuario as error:
        flash(error.mensaje, "error")
        return redirect(url_for("panel") + f"#pedido-{pid}")
    flash(
        f"Turno {turno}: pago rechazado y unidades devueltas al inventario.",
        "ok",
    )
    return redirect(url_for("panel"))


@app.post("/vendedor/pedido/<int:pid>/estado/<nuevo>")
@solo_vendedor
def cambiar_estado(pid, nuevo):
    validar_csrf()
    if nuevo not in {"preparando", "listo", "entregado"}:
        abort(400, description="Ese cambio de estado no es válido.")

    def accion(conexion):
        pedido = conexion.execute("SELECT * FROM pedidos WHERE id=?", (pid,)).fetchone()
        if pedido is None:
            raise ErrorUsuario("No encontramos ese pedido.", 404)
        siguiente = SIGUIENTE.get(pedido["estado"])
        if not siguiente or siguiente[0] != nuevo:
            raise ErrorUsuario(
                "Ese cambio ya no es válido. Actualiza la página y revisa el "
                "estado actual del pedido.",
                409,
            )
        if pedido["pago"] == "nequi" and pedido["pago_estado"] != "confirmado":
            raise ErrorUsuario(
                "El pago Nequi todavía no está confirmado. Confírmalo antes de "
                "mover el pedido.",
                409,
            )
        conexion.execute(
            "UPDATE pedidos SET estado=?, actualizado=? WHERE id=?",
            (nuevo, ahora(), pid),
        )
        return pedido["turno"]

    try:
        turno = transaccion(accion)
    except ErrorUsuario as error:
        flash(error.mensaje, "error")
        return redirect(url_for("panel") + f"#pedido-{pid}")
    flash(f"Turno {turno}: ahora está en “{ESTADOS[nuevo]}”.", "ok")
    return redirect(url_for("panel") + f"#pedido-{pid}")


@app.post("/vendedor/pedido/<int:pid>/cancelar")
@solo_vendedor
def cancelar_pedido(pid):
    validar_csrf()

    def accion(conexion):
        pedido = conexion.execute("SELECT * FROM pedidos WHERE id=?", (pid,)).fetchone()
        if pedido is None:
            raise ErrorUsuario("No encontramos ese pedido.", 404)
        if pedido["estado"] in {"entregado", "cancelado", "pago_pendiente"}:
            raise ErrorUsuario(
                "Solo puedes cancelar pedidos recibidos, en preparación o listos. "
                "Un pago pendiente se rechaza desde su botón.",
                409,
            )
        devolver_stock(conexion, pid)
        conexion.execute(
            "UPDATE pedidos SET estado='cancelado', actualizado=? WHERE id=?",
            (ahora(), pid),
        )
        return pedido["turno"]

    try:
        turno = transaccion(accion)
    except ErrorUsuario as error:
        flash(error.mensaje, "error")
        return redirect(url_for("panel") + f"#pedido-{pid}")
    flash(f"Turno {turno}: pedido cancelado y unidades devueltas.", "ok")
    return redirect(url_for("panel"))


@app.post("/vendedor/nequi")
@solo_vendedor
def guardar_nequi():
    validar_csrf()
    numero = request.form.get("nequi_numero", "")
    if not isinstance(numero, str):
        abort(400, description="El número Nequi debe ser texto.")
    numero = re.sub(r"[\s-]+", "", numero)
    if numero and not re.fullmatch(r"\d{7,15}", numero):
        flash(
            "El número Nequi debe tener entre 7 y 15 dígitos. Escríbelo solo "
            "con números.",
            "error",
        )
    else:
        guardar_ajuste("nequi_numero", numero)
        if numero:
            flash("Número Nequi actualizado. Ya se muestra a los compradores.", "ok")
        else:
            flash(
                "Número Nequi borrado. Los pedidos nuevos por Nequi quedan "
                "desactivados.",
                "ok",
            )
    return redirect(url_for("panel") + "#nequi")


@app.route("/vendedor/inventario", methods=["GET", "POST"])
@solo_vendedor
def inventario():
    if request.method == "POST":
        validar_csrf()
        accion_form = request.form.get("accion", "actualizar")

        def guardar(conexion):
            nombre, precio, stock, activo = validar_producto_formulario(request.form)
            if accion_form == "nuevo":
                conexion.execute(
                    "INSERT INTO items(nombre, precio, stock, activo) VALUES(?, ?, ?, ?)",
                    (nombre, precio, stock, activo),
                )
                return f"Producto “{nombre}” agregado."
            if accion_form != "actualizar":
                raise ErrorUsuario("La acción del formulario no es válida.")
            try:
                item_id = int(request.form.get("id", ""))
            except (TypeError, ValueError):
                raise ErrorUsuario("No se identificó el producto que quieres guardar.")
            if item_id <= 0:
                raise ErrorUsuario("No se identificó el producto que quieres guardar.")
            existe = conexion.execute(
                "SELECT id FROM items WHERE id=?", (item_id,)
            ).fetchone()
            if existe is None:
                raise ErrorUsuario(
                    "Ese producto ya no existe. Recarga la página y vuelve a intentarlo.",
                    404,
                )
            conexion.execute(
                "UPDATE items SET nombre=?, precio=?, stock=?, activo=? WHERE id=?",
                (nombre, precio, stock, activo, item_id),
            )
            return f"Cambios guardados en “{nombre}”."

        try:
            mensaje = transaccion(guardar)
        except ErrorUsuario as error:
            flash(error.mensaje, "error")
            return redirect(url_for("inventario"))
        flash(mensaje, "ok")
        return redirect(url_for("inventario"))

    items = db().execute("SELECT * FROM items ORDER BY id").fetchall()
    return render_template("inventario.html", items=items)


def _datos_historial(fecha):
    conexion = db()
    resumen = conexion.execute(
        "SELECT "
        "COUNT(*) AS total_pedidos, "
        "COALESCE(SUM(CASE WHEN estado='entregado' THEN 1 ELSE 0 END), 0) AS entregados, "
        "COALESCE(SUM(CASE WHEN estado='cancelado' THEN 1 ELSE 0 END), 0) AS cancelados, "
        "COALESCE(SUM(CASE WHEN estado IN ('pago_pendiente','recibido','preparando','listo') "
        "THEN 1 ELSE 0 END), 0) AS abiertos, "
        "COALESCE(SUM(CASE WHEN estado='entregado' THEN total ELSE 0 END), 0) AS vendido, "
        "COALESCE(SUM(CASE WHEN estado='entregado' AND pago='efectivo' THEN total ELSE 0 END), 0) AS efectivo, "
        "COALESCE(SUM(CASE WHEN estado='entregado' AND pago='nequi' THEN total ELSE 0 END), 0) AS nequi "
        "FROM pedidos WHERE fecha=?",
        (fecha,),
    ).fetchone()
    top = conexion.execute(
        "SELECT d.nombre, SUM(d.cantidad) AS unidades, "
        "SUM(d.cantidad * d.precio) AS ingresos "
        "FROM detalle d JOIN pedidos p ON p.id=d.pedido_id "
        "WHERE p.fecha=? AND p.estado='entregado' "
        "GROUP BY d.item_id, d.nombre "
        "ORDER BY unidades DESC, ingresos DESC LIMIT 8",
        (fecha,),
    ).fetchall()
    maximo = max((fila["unidades"] for fila in top), default=0)
    top = [
        {
            "nombre": fila["nombre"],
            "unidades": fila["unidades"],
            "ingresos": fila["ingresos"],
            "porcentaje": round(fila["unidades"] * 100 / maximo) if maximo else 0,
        }
        for fila in top
    ]
    pedidos = conexion.execute(
        "SELECT * FROM pedidos WHERE fecha=? ORDER BY turno DESC", (fecha,)
    ).fetchall()
    detalle = {
        pedido["id"]: conexion.execute(
            "SELECT nombre, cantidad, precio FROM detalle "
            f"WHERE pedido_id=? ORDER BY {ORDEN_DETALLE}",
            (pedido["id"],),
        ).fetchall()
        for pedido in pedidos
    }
    return resumen, top, pedidos, detalle


@app.get("/vendedor/historial")
@solo_vendedor
def historial():
    solicitada = request.args.get("fecha", "")
    fecha = fecha_iso(solicitada)
    if solicitada and not fecha:
        flash("La fecha no es válida. Usa el formato año-mes-día.", "error")
    if not fecha:
        fecha = hoy()
    resumen, top, pedidos, detalle = _datos_historial(fecha)
    return render_template(
        "historial.html",
        fecha=fecha,
        resumen=resumen,
        top=top,
        pedidos=pedidos,
        det=detalle,
        estados=ESTADOS,
        pagos=PAGOS,
        pago_estados=PAGO_ESTADOS,
    )


@app.get("/vendedor/historial.csv")
@solo_vendedor
def historial_csv():
    solicitada = request.args.get("fecha", "")
    fecha = fecha_iso(solicitada) if solicitada else hoy()
    if not fecha:
        abort(400, description="La fecha no es válida. Usa el formato año-mes-día.")
    _resumen, _top, pedidos, detalle = _datos_historial(fecha)

    salida = io.StringIO()
    salida.write("\ufeff")
    escritor = csv.writer(
        salida, delimiter=";", lineterminator="\r\n", quoting=csv.QUOTE_MINIMAL
    )
    escritor.writerow(
        [
            "Fecha", "Turno", "Hora", "Cliente", "Estado", "Método de pago",
            "Estado del pago", "Comprobante", "Total", "Productos",
        ]
    )
    for pedido in pedidos:
        productos = " | ".join(
            f"{linea['cantidad']} x {linea['nombre']}" for linea in detalle[pedido["id"]]
        )
        hora = pedido["creado"][11:16] if pedido["creado"] else ""
        escritor.writerow(
            [
                celda_csv(pedido["fecha"]),
                pedido["turno"],
                celda_csv(hora),
                celda_csv(pedido["cliente"]),
                celda_csv(ESTADOS.get(pedido["estado"], pedido["estado"])),
                celda_csv(PAGOS.get(pedido["pago"], pedido["pago"])),
                celda_csv(
                    PAGO_ESTADOS.get(pedido["pago_estado"], pedido["pago_estado"])
                ),
                celda_csv(pedido["comprobante"] or ""),
                pedido["total"],
                celda_csv(productos),
            ]
        )
    contenido = salida.getvalue().encode("utf-8")
    return Response(
        contenido,
        mimetype="text/csv; charset=utf-8",
        headers={
            "Content-Disposition": f'attachment; filename="ricuras-historial-{fecha}.csv"',
            "Cache-Control": "no-store",
        },
    )


@app.get("/vendedor/qr")
@solo_vendedor
def qr_pagina():
    url = url_publica()
    return render_template(
        "qr.html",
        url=url,
        qr_ok=qrcode_disponible(),
        es_local=es_url_local(url),
    )


@app.get("/qr.svg")
def qr_svg():
    try:
        import qrcode
        import qrcode.image.svg
    except Exception:
        return Response(
            "La generación de QR no está disponible. Instala qrcode con: "
            "pip install qrcode",
            status=501,
            mimetype="text/plain; charset=utf-8",
        )
    try:
        imagen = qrcode.make(
            url_publica(),
            image_factory=qrcode.image.svg.SvgPathImage,
            box_size=12,
            border=2,
        )
        datos = imagen.to_string()
        if isinstance(datos, bytes):
            datos = datos.decode("utf-8")
        respuesta = Response(datos, mimetype="image/svg+xml")
        respuesta.headers["Cache-Control"] = "no-store"
        return respuesta
    except Exception:
        app.logger.exception("No se pudo generar el código QR")
        return Response(
            "No se pudo generar el código QR. Revisa la variable BASE_URL.",
            status=500,
            mimetype="text/plain; charset=utf-8",
        )


# ---------------------------------------------------------------------------
# Filtros, cabeceras y errores
# ---------------------------------------------------------------------------


@app.template_filter("cop")
def filtro_cop(valor):
    try:
        numero = int(valor)
    except (TypeError, ValueError):
        numero = 0
    return "$" + f"{numero:,}".replace(",", ".")


@app.template_filter("hora")
def filtro_hora(valor):
    if isinstance(valor, str) and len(valor) >= 16:
        return valor[11:16]
    return ""


@app.template_filter("fecha_larga")
def filtro_fecha_larga(valor):
    fecha = fecha_iso(valor)
    if not fecha:
        return valor
    objeto = date.fromisoformat(fecha)
    return f"{objeto.day} de {MESES[objeto.month - 1]} de {objeto.year}"


app.jinja_env.globals["csrf_token"] = csrf_token


@app.after_request
def cabeceras(respuesta):
    respuesta.headers.setdefault("X-Content-Type-Options", "nosniff")
    respuesta.headers.setdefault("X-Frame-Options", "DENY")
    respuesta.headers.setdefault("Referrer-Policy", "same-origin")
    respuesta.headers.setdefault(
        "Content-Security-Policy",
        "default-src 'self'; base-uri 'self'; form-action 'self'; "
        "frame-ancestors 'none'; img-src 'self' data:; "
        "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
        "font-src https://fonts.gstatic.com; script-src 'self' 'unsafe-inline'; "
        "connect-src 'self'",
    )
    if (
        request.path.startswith("/api/")
        or request.path.startswith("/vendedor")
        or request.path.endswith("/comprobante")
    ):
        respuesta.headers["Cache-Control"] = "no-store"
    return respuesta


@app.errorhandler(400)
def error_400(error):
    return (
        render_template(
            "error.html",
            codigo=400,
            titulo="No pudimos procesar la solicitud",
            mensaje=getattr(
                error,
                "description",
                "Revisa los datos e inténtalo de nuevo.",
            ),
        ),
        400,
    )


@app.errorhandler(403)
def error_403(_error):
    return (
        render_template(
            "error.html",
            codigo=403,
            titulo="Acceso no permitido",
            mensaje="No tienes permiso para abrir esta página.",
        ),
        403,
    )


@app.errorhandler(404)
def error_404(_error):
    return (
        render_template(
            "error.html",
            codigo=404,
            titulo="No encontramos esa página",
            mensaje=(
                "Si buscabas un pedido, ábrelo desde el mismo navegador donde lo "
                "hiciste o revisa Mis pedidos."
            ),
        ),
        404,
    )


@app.errorhandler(413)
def error_413(_error):
    return (
        render_template(
            "error.html",
            codigo=413,
            titulo="El pedido es demasiado grande",
            mensaje="Reduce la cantidad de productos e inténtalo de nuevo.",
        ),
        413,
    )


@app.errorhandler(500)
def error_500(_error):
    return (
        render_template(
            "error.html",
            codigo=500,
            titulo="Algo falló en el puesto",
            mensaje=(
                "No se guardó ningún cambio. Recarga la página y vuelve a intentarlo. "
                "Si sigue pasando, avisa al vendedor."
            ),
        ),
        500,
    )


BASE = """<!doctype html>
<html lang="es">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="color-scheme" content="only light">
<meta name="theme-color" content="#142033">
<title>{% block titulo %}Ricuras{% endblock %}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:wght@600;800&family=DM+Sans:wght@400;500;700&display=swap" rel="stylesheet">
<style>
:root{
--tinta:#12263A; --mango:#FFB400; --chile:#D62839; --fondo:#F2F5F9;
--blanco:#FFFFFF; --linea:#D5DDE6; --tinta-suave:#4A5F73;
--ok:#1E8E5A; --ok-fondo:#E4F4EC; --mal-fondo:#FBE7E9;
--sombra:0 12px 30px rgba(18,38,58,.09);
}
*{box-sizing:border-box}
html{scroll-behavior:smooth}
body{
margin:0; min-height:100vh; background:var(--fondo); color:var(--tinta);
font-family:"DM Sans",system-ui,-apple-system,"Segoe UI",sans-serif;
font-size:1rem; line-height:1.55;
}
h1,h2,h3,.turno-numero,.marca,.marca-clara,.marca-enlace{
font-family:"Bricolage Grotesque","DM Sans",system-ui,sans-serif;
font-weight:800; line-height:1.05; letter-spacing:-.025em; margin:0;
}
p{margin:.4rem 0}
a{color:var(--tinta); text-underline-offset:.2em}
img{max-width:100%; height:auto}
button,input{font:inherit}
button{cursor:pointer}
button:disabled{cursor:not-allowed}
.contenedor{width:100%; max-width:44rem; margin:0 auto; padding:0 1rem}
.pagina-angosta{max-width:36rem}
#contenido{scroll-margin-top:1rem}
.saltar{
position:absolute; left:-999px; top:0; z-index:60; background:var(--mango);
color:var(--tinta); padding:.7rem 1rem; font-weight:700;
}
.saltar:focus{left:.5rem; top:.5rem}
:focus-visible{outline:3px solid var(--chile); outline-offset:2px}
.hero :focus-visible,.top-panel :focus-visible,.barra :focus-visible,
.top-simple :focus-visible{outline-color:var(--mango)}
.avisos{max-width:44rem; margin:1rem auto 0; padding:0 1rem; display:grid; gap:.5rem}
.aviso{
margin:0; padding:.75rem 1rem; border-radius:.6rem; background:#E8EEF5;
border-left:4px solid var(--tinta);
}
.aviso.error{background:var(--mal-fondo); border-color:var(--chile); color:#7A1420}
.aviso.ok{background:var(--ok-fondo); border-color:var(--ok); color:#0F5C3A}
.btn{
display:inline-flex; align-items:center; justify-content:center; gap:.4rem;
min-height:46px; padding:.7rem 1.1rem; border-radius:.65rem;
border:1px solid var(--tinta); background:var(--mango); color:var(--tinta);
font-weight:700; text-decoration:none; line-height:1.2;
transition:transform .15s ease, box-shadow .15s ease;
}
.btn:hover{box-shadow:0 4px 0 rgba(18,38,58,.18)}
.btn:active{transform:translateY(1px)}
.btn-sec{background:var(--blanco); border-color:var(--linea)}
.btn-ok{background:var(--ok); border-color:var(--ok); color:#fff}
.btn-peligro{background:var(--blanco); border-color:var(--chile); color:#A51E2D}
.btn-peligro-suave{background:transparent; border-color:var(--linea); color:#7A1420}
.btn-pequeno{min-height:38px; padding:.45rem .8rem; font-size:.9rem}
.btn:disabled{
background:#E4E9EF; border-color:var(--linea); color:#7A8B9B;
box-shadow:none; transform:none;
}
label{display:block; font-weight:700; margin:.9rem 0 .3rem}
input[type=text],input[type=number],input[type=password],input[type=date],input[type=tel]{
width:100%; min-height:46px; padding:.65rem .75rem; border:1px solid #A9B8C7;
border-radius:.55rem; background:#fff; color:var(--tinta); font-size:1rem;
}
input::placeholder{color:#7A8B9B}
fieldset{border:0; padding:0; margin:0; min-width:0}
legend{font-weight:700; padding:0}
.error{color:#A51E2D; font-weight:700; min-height:1.5rem; margin:.5rem 0}
.nota{color:var(--tinta-suave); font-size:.88rem}
.nota-error{
background:var(--mal-fondo); color:#8A1B28; padding:.7rem .8rem;
border-radius:.5rem; font-weight:600;
}
.nota-ok{
background:var(--ok-fondo); color:#0F5C3A; padding:.7rem .8rem;
border-radius:.5rem; font-weight:600;
}
.pie{text-align:center; font-size:.85rem; color:var(--tinta-suave); padding:2rem 0 1rem}
.pie a{color:var(--tinta-suave)}
.estado{
display:inline-flex; align-items:center; gap:.35rem; padding:.25rem .65rem;
border-radius:99px; font-size:.78rem; font-weight:700; line-height:1.2;
white-space:nowrap;
}
.estado::before{
content:""; width:.45rem; height:.45rem; border-radius:50%;
background:currentColor; flex:0 0 auto;
}
.estado-pago_pendiente{background:#FFF2CC; color:#7A4D00}
.estado-recibido{background:#E6EDF4; color:#1D3A55}
.estado-preparando{background:#FFE1B3; color:#7A4D00}
.estado-listo{background:#DDF3E8; color:#0F5C3A}
.estado-entregado{background:var(--tinta); color:#fff}
.estado-cancelado{background:var(--mal-fondo); color:#8A1B28}
.hero{
background:var(--tinta); color:#fff; position:relative; overflow:hidden;
padding:2.2rem 0 2.5rem;
}
.hero::after{
content:""; position:absolute; right:-4rem; bottom:-5rem; width:16rem;
height:16rem; border-radius:50%; pointer-events:none;
background:radial-gradient(circle at 30% 30%, rgba(255,180,0,.28), transparent 65%);
}
.hero-interior{position:relative; z-index:1}
.marca{font-size:1.1rem; color:var(--mango); letter-spacing:.01em}
.hero h1{font-size:clamp(2.6rem,11vw,4.6rem); color:#fff; margin:.8rem 0 0; max-width:12ch}
.hero h1 span{color:var(--mango)}
.hero p{max-width:34rem; color:#DCE6F0; font-size:1.05rem}
.hero-pista{
display:inline-flex; align-items:center; gap:.5rem; margin-top:1rem;
font-size:.9rem; color:#CBD8E5;
}
.punto{
width:.55rem; height:.55rem; border-radius:50%; background:var(--mango);
box-shadow:0 0 0 4px rgba(255,180,0,.18);
}
.pagina-menu{padding-top:1.5rem; padding-bottom:8.5rem}
.titulo-seccion{
display:flex; justify-content:space-between; align-items:flex-end;
gap:1rem; flex-wrap:wrap; margin-bottom:.5rem;
}
.titulo-seccion h2{font-size:clamp(1.6rem,6vw,2rem)}
.titulo-seccion p{color:var(--tinta-suave); font-size:.95rem; margin:.2rem 0 0}
.enlace-suave{font-weight:700; font-size:.92rem; white-space:nowrap}
.menu{list-style:none; margin:1rem 0 0; padding:0; border-top:2px solid var(--tinta)}
.producto{
display:grid; grid-template-columns:minmax(0,1fr) auto; align-items:center;
gap:1rem; padding:1.1rem 0; border-bottom:1px solid var(--linea);
}
.producto h3{font-size:1.3rem; letter-spacing:-.02em}
.producto-meta{display:flex; flex-wrap:wrap; align-items:center; gap:.5rem .7rem; margin:.35rem 0 0}
.precio{font-weight:700; font-size:1rem}
.stock{
font-size:.82rem; color:var(--tinta-suave); background:#E7EDF4;
padding:.18rem .55rem; border-radius:99px;
}
.stock-poco,.stock-cero{color:#7A1420; background:var(--mal-fondo)}
.producto.agotado h3{color:#7A8B9B}
.agotado-texto{
font-size:.85rem; color:var(--chile); font-weight:700; white-space:nowrap;
}
.contador{
display:flex; align-items:center; gap:.3rem; background:var(--blanco);
border:1px solid var(--linea); border-radius:99px; padding:.2rem;
}
.contador button{
width:2.6rem; height:2.6rem; border:0; border-radius:50%;
background:var(--tinta); color:#fff; font-size:1.35rem; line-height:1;
font-weight:700;
}
.contador button:disabled{background:transparent; color:#9AAFBF}
.cantidad{
min-width:1.6rem; text-align:center; font-weight:700;
font-variant-numeric:tabular-nums;
}
.vacio{padding:2rem 0; color:var(--tinta-suave)}
.barra{
position:fixed; left:0; right:0; bottom:0; z-index:20; background:var(--tinta);
color:#fff; padding:.8rem 0 calc(.8rem + env(safe-area-inset-bottom));
box-shadow:0 -10px 30px rgba(18,38,58,.18);
}
.barra[hidden]{display:none}
.barra-interior{display:flex; align-items:center; justify-content:space-between; gap:1rem}
.barra-cantidad{display:block; font-size:.82rem; color:#C6D4E2}
.barra strong{font-size:1.2rem}
dialog{
border:0; padding:0; background:transparent; width:min(32rem,calc(100% - 1rem));
max-height:calc(100dvh - 1rem);
}
dialog::backdrop{background:rgba(18,38,58,.65)}
.dialogo{
background:var(--fondo); border-radius:1.1rem; padding:1.25rem;
max-height:calc(100dvh - 1rem); overflow:auto;
}
.dialogo-cabecera{display:flex; justify-content:space-between; align-items:flex-start; gap:1rem}
.dialogo-cabecera h2{font-size:1.6rem}
.cerrar{
width:2.6rem; height:2.6rem; border:0; border-radius:50%;
background:#E3EAF1; font-size:1.5rem; line-height:1; color:var(--tinta);
flex:0 0 auto;
}
.resumen-lista{list-style:none; margin:1rem 0; padding:0; display:grid; gap:.5rem}
.resumen-lista li{
display:flex; justify-content:space-between; gap:.75rem;
border-bottom:1px dashed var(--linea); padding-bottom:.5rem;
}
.resumen-lista li span:first-child{color:var(--tinta-suave)}
.resumen-lista strong{white-space:nowrap}
.total-linea{
display:flex; justify-content:space-between; font-size:1.2rem;
border-top:2px solid var(--tinta); padding-top:.75rem; margin-top:.5rem;
}
.pago-opciones{margin:1rem 0 0}
.opcion{
display:flex; gap:.65rem; align-items:flex-start; border:1px solid var(--linea);
background:#fff; border-radius:.6rem; padding:.75rem; margin:.5rem 0; cursor:pointer;
}
.opcion:has(input:checked){border-color:var(--tinta); box-shadow:inset 0 0 0 1px var(--tinta)}
.opcion input{
margin-top:.3rem; accent-color:var(--tinta); width:1.15rem; height:1.15rem;
flex:0 0 auto;
}
.opcion strong,.opcion small{display:block}
.opcion small{color:var(--tinta-suave); font-weight:400; font-size:.87rem}
.opcion.deshabilitada{opacity:.55}
.nequi-aviso{
background:#FFF2CC; border-left:4px solid var(--mango); padding:.7rem .8rem;
border-radius:.4rem; margin-top:.75rem; font-size:.9rem;
}
.acciones-dialogo{
display:flex; gap:.6rem; flex-wrap:wrap; margin-top:.75rem;
justify-content:flex-end;
}
.top-simple{background:var(--tinta); color:#fff; padding:1rem 0}
.top-fila{display:flex; justify-content:space-between; align-items:center; gap:1rem}
.marca-enlace{color:var(--mango); font-size:1.3rem; text-decoration:none}
.enlace-claro{color:#DCE6F0; font-size:.9rem; font-weight:500}
.seguimiento{padding-top:1.25rem; padding-bottom:3rem; max-width:38rem}
.turno-panel{
background:var(--mango); border-radius:1.2rem; padding:1.2rem 1.25rem 1.25rem;
position:relative; overflow:hidden; box-shadow:var(--sombra);
}
.turno-panel::after{
content:""; position:absolute; right:-3rem; top:-3rem; width:10rem;
height:10rem; border-radius:50%; background:rgba(18,38,58,.09);
}
.etiqueta-turno{font-size:.9rem; font-weight:700; margin:0}
.turno-numero{
font-size:clamp(6rem,30vw,10rem); line-height:.8; letter-spacing:-.07em;
margin:.35rem 0 .5rem; font-variant-numeric:tabular-nums;
}
.turno-pie{
display:flex; justify-content:space-between; align-items:center; gap:1rem;
flex-wrap:wrap; font-size:.85rem; position:relative; z-index:1;
}
.turno-pie .estado{background:var(--tinta); color:#fff}
.pasos{list-style:none; margin:1.5rem 0; padding:0; display:grid; gap:0}
.paso{
position:relative; display:flex; align-items:center; gap:.75rem;
color:#8A9BAB; font-weight:500; padding:.45rem 0;
}
.paso-punto{
width:1rem; height:1rem; border-radius:50%; border:2px solid #B8C5D2;
background:var(--fondo); flex:0 0 auto; position:relative; z-index:1;
}
.paso:not(:last-child)::after{
content:""; position:absolute; left:.47rem; top:1.55rem; bottom:-.45rem;
width:2px; background:var(--linea);
}
.paso.completo{color:var(--tinta); font-weight:700}
.paso.completo .paso-punto{background:var(--ok); border-color:var(--ok)}
.paso.actual{color:var(--tinta); font-weight:700}
.paso.actual .paso-punto{
background:var(--mango); border-color:var(--tinta);
box-shadow:0 0 0 4px rgba(255,180,0,.25);
}
.caja-pago,.resumen-pedido{
background:#fff; border:1px solid var(--linea); border-radius:1rem;
padding:1.1rem; margin:1rem 0;
}
.caja-pago h2,.resumen-pedido h2{font-size:1.35rem}
.caja-pendiente{border-color:#E3B54A; background:#FFFBF0}
.caja-ok{border-color:#A9D6BE; background:#F2FBF7}
.caja-mal{border-color:#EBB3B9; background:#FFF6F7}
.comprobante{
background:var(--fondo); padding:.5rem .7rem; border-radius:.4rem;
font-size:.9rem; overflow-wrap:anywhere;
}
.form-comprobante{margin-top:.75rem}
.aviso-cancelado{
background:var(--mal-fondo); color:#8A1B28; border-radius:.8rem;
padding:.9rem 1rem; font-weight:600; margin:1rem 0;
}
.lineas{list-style:none; margin:.75rem 0; padding:0}
.lineas li{
display:flex; justify-content:space-between; gap:1rem; padding:.5rem 0;
border-bottom:1px dashed var(--linea);
}
.lineas li span{min-width:0; overflow-wrap:anywhere}
.total-final{
display:flex; justify-content:space-between; font-size:1.15rem;
font-weight:700; padding-top:.75rem;
}
.acciones-pedido{display:flex; gap:.6rem; flex-wrap:wrap; margin:1.25rem 0}
.conexion{
min-height:1.3rem; color:var(--tinta-suave); font-size:.85rem;
text-align:center;
}
.titulo-pagina{font-size:clamp(2rem,8vw,3rem); margin:1.5rem 0 .4rem}
.subtitulo{color:var(--tinta-suave); max-width:34rem}
.lista-mis{list-style:none; margin:1.5rem 0; padding:0; display:grid; gap:.75rem}
.mi-pedido{
display:grid; grid-template-columns:auto minmax(0,1fr) auto;
align-items:center; gap:.9rem; background:#fff; border:1px solid var(--linea);
border-radius:.8rem; padding:.8rem; text-decoration:none;
}
.mi-turno{
width:3rem; height:3rem; border-radius:.6rem; background:var(--mango);
display:grid; place-items:center; font-family:"Bricolage Grotesque",sans-serif;
font-weight:800; font-size:1.4rem;
}
.mi-datos strong,.mi-datos small{display:block}
.mi-datos small{color:var(--tinta-suave)}
.login-caja{
display:grid; grid-template-columns:1.1fr .9fr; gap:0; background:#fff;
border:1px solid var(--linea); border-radius:1.2rem; overflow:hidden;
margin:1.5rem 0;
}
.login-intro{background:var(--tinta); color:#fff; padding:1.5rem}
.login-intro h1{color:var(--mango); font-size:clamp(2rem,7vw,3rem); margin:.5rem 0}
.login-intro p{color:#DCE6F0}
.login-caja .formulario{padding:1.5rem}
.sobrelinea{font-size:.8rem; font-weight:700; color:var(--tinta-suave); margin:0}
.login-intro .sobrelinea{color:var(--mango)}
.top-panel{background:var(--tinta); color:#fff; padding:1rem 0 0}
.panel-barra{display:flex; justify-content:space-between; align-items:center; gap:1rem}
.marca-clara{color:var(--mango); font-size:1.5rem; text-decoration:none}
.marca-clara span{
font-size:.8rem; color:#C6D4E2; font-family:"DM Sans",sans-serif;
font-weight:500; margin-left:.25rem; letter-spacing:0;
}
.panel-nav{display:flex; gap:.25rem; overflow-x:auto; margin-top:.75rem}
.panel-nav a{
color:#C6D4E2; text-decoration:none; padding:.7rem; border-bottom:3px solid transparent;
white-space:nowrap; font-size:.9rem;
}
.panel-nav a[aria-current=page]{color:var(--mango); border-color:var(--mango); font-weight:700}
.pagina-panel{padding-top:1.25rem; padding-bottom:3rem; max-width:48rem}
.panel-resumen{display:grid; grid-template-columns:repeat(3,1fr); gap:.75rem; margin-bottom:1rem}
.resumen-item{
background:#fff; border:1px solid var(--linea); border-radius:.8rem;
padding:.8rem; display:flex; flex-direction:column; gap:.15rem;
}
.resumen-num{
font-family:"Bricolage Grotesque",sans-serif; font-weight:800;
font-size:2rem; line-height:1;
}
.resumen-pendiente{border-color:#E3B54A; background:#FFFBF0}
.resumen-listo{border-color:#A9D6BE; background:#F2FBF7}
.resumen-item span:last-child{font-size:.8rem; color:var(--tinta-suave)}
.config-nequi{
background:#fff; border:1px solid var(--linea); border-radius:1rem;
padding:1rem; margin:1rem 0;
}
.form-nequi{display:grid; grid-template-columns:minmax(0,1fr) auto; gap:.6rem 1rem; align-items:end}
.form-nequi h2{font-size:1.2rem}
.form-nequi p{color:var(--tinta-suave); font-size:.88rem}
.form-nequi > div{grid-column:1/-1}
.form-nequi label{grid-column:1/-1; margin:0}
.form-nequi input{grid-column:1}
.form-nequi button{grid-column:2}
.panel-encabezado{
display:flex; justify-content:space-between; align-items:flex-end;
gap:1rem; flex-wrap:wrap; margin:1.5rem 0 .75rem;
}
.panel-encabezado h1{font-size:clamp(1.7rem,6vw,2.2rem)}
.panel-encabezado p{color:var(--tinta-suave); margin:.2rem 0}
.lista-pedidos{display:grid; gap:.9rem}
.pedido-card{
display:grid; grid-template-columns:5rem minmax(0,1fr); background:#fff;
border:1px solid var(--linea); border-left:5px solid var(--linea);
border-radius:.9rem; overflow:hidden;
}
.pedido-card.estado-pago_pendiente{border-left-color:#E3B54A; background:#FFFCF5}
.pedido-card.estado-listo{border-left-color:var(--ok); background:#FBFFFD}
.pedido-card.estado-preparando{border-left-color:var(--mango)}
.pedido-card.estado-recibido{border-left-color:#7A8B9B}
.pedido-turno{
background:var(--mango); display:flex; flex-direction:column;
align-items:center; justify-content:center; padding:.75rem .4rem; text-align:center;
}
.pedido-turno span{font-size:.7rem; font-weight:700}
.pedido-turno strong{
font-family:"Bricolage Grotesque",sans-serif; font-weight:800;
font-size:2.6rem; line-height:.9;
}
.pedido-cuerpo{padding:.9rem; min-width:0}
.pedido-cabecera{
display:flex; justify-content:space-between; align-items:flex-start;
gap:.6rem; flex-wrap:wrap;
}
.pedido-cabecera h2{font-size:1.25rem; overflow-wrap:anywhere}
.pedido-hora{font-size:.78rem; color:var(--tinta-suave); margin:0}
.pedido-pago{font-size:.88rem; color:var(--tinta-suave); margin:.4rem 0}
.pedido-lineas{list-style:none; margin:.5rem 0; padding:0; font-size:.92rem}
.pedido-lineas li{display:flex; justify-content:space-between; gap:1rem; padding:.18rem 0}
.pedido-lineas li span:first-child{min-width:0; overflow-wrap:anywhere}
.comprobante-linea{
font-size:.88rem; background:var(--fondo); padding:.45rem .6rem;
border-radius:.4rem; overflow-wrap:anywhere;
}
.falta{color:#8A1B28; font-weight:700}
.pedido-acciones{display:flex; gap:.5rem; flex-wrap:wrap; margin-top:.75rem}
.pedido-acciones form{margin:0}
.pedido-acciones .btn{min-height:40px; padding:.5rem .75rem; font-size:.9rem}
.panel-vacio{
background:#fff; border:1px dashed #B8C5D2; border-radius:.9rem;
padding:1.5rem; text-align:center; color:var(--tinta-suave);
}
.tabla-inventario{display:grid; gap:.75rem}
.fila-inventario{
display:grid; grid-template-columns:minmax(0,1.4fr) .8fr .8fr auto auto;
gap:.6rem; align-items:end; background:#fff; border:1px solid var(--linea);
border-radius:.8rem; padding:.8rem; margin:0;
}
.fila-inventario.inactivo{background:#F7F9FB; border-style:dashed}
.fila-inventario label{margin:0 0 .2rem; font-size:.8rem; color:var(--tinta-suave)}
.fila-inventario .check{
display:flex; gap:.45rem; align-items:center; font-weight:600;
color:var(--tinta); font-size:.85rem; min-height:46px;
}
.fila-inventario .check input{width:1.1rem; height:1.1rem; accent-color:var(--tinta)}
.agregar-producto{
background:#fff; border:1px solid var(--linea); border-radius:1rem;
padding:1rem; margin:1.75rem 0;
}
.agregar-producto h2{font-size:1.3rem; margin-bottom:.75rem}
.filtro-fecha{
display:flex; gap:.6rem; align-items:flex-end; flex-wrap:wrap;
background:#fff; border:1px solid var(--linea); border-radius:.9rem;
padding:.8rem; margin:1rem 0;
}
.filtro-fecha label{margin:0}
.filtro-fecha input{width:auto; min-width:10rem}
.totales{display:grid; grid-template-columns:1.6fr 1fr 1fr; gap:.75rem; margin:1rem 0}
.total-grande{
background:var(--tinta); color:#fff; border-radius:1rem; padding:1.1rem;
grid-row:span 1;
}
.total-grande p{color:#C6D4E2; margin:0; font-size:.85rem}
.total-grande strong{
display:block; font-family:"Bricolage Grotesque",sans-serif;
font-size:clamp(2rem,7vw,3.2rem); line-height:1; color:var(--mango);
margin:.3rem 0;
}
.total-grande small{color:#DCE6F0; font-size:.8rem; line-height:1.3; display:block}
.total-metodo{
background:#fff; border:1px solid var(--linea); border-radius:.9rem;
padding:.9rem; display:flex; flex-direction:column; justify-content:center;
}
.total-metodo span{font-size:.82rem; color:var(--tinta-suave)}
.total-metodo strong{font-family:"Bricolage Grotesque",sans-serif; font-size:1.4rem}
.mas-vendidos{margin:1.5rem 0}
.mas-vendidos h2{font-size:1.3rem}
.top-lista{list-style:none; margin:.75rem 0; padding:0; display:grid; gap:.55rem}
.top-lista li{
display:grid; grid-template-columns:minmax(0,1fr) 2fr auto;
gap:.6rem; align-items:center; font-size:.9rem;
}
.top-nombre{font-weight:600; overflow-wrap:anywhere}
.barra-top{height:.6rem; background:#E3EAF1; border-radius:99px; overflow:hidden}
.barra-top span{display:block; height:100%; background:var(--mango); border-radius:99px}
.historial-lista{display:grid; gap:.6rem; margin-top:.75rem}
.historial-item{
background:#fff; border:1px solid var(--linea); border-left:4px solid var(--linea);
border-radius:.7rem; overflow:hidden;
}
.historial-item.estado-entregado{border-left-color:var(--ok)}
.historial-item.estado-cancelado{border-left-color:var(--chile)}
.historial-item.estado-pago_pendiente{border-left-color:#E3B54A}
.historial-item summary{
display:grid; grid-template-columns:auto minmax(0,1fr) auto auto auto;
gap:.6rem; align-items:center; padding:.7rem .8rem; cursor:pointer;
list-style:none;
}
.historial-item summary::-webkit-details-marker{display:none}
.hist-turno{font-weight:700; font-size:.85rem; white-space:nowrap}
.hist-cliente{overflow-wrap:anywhere}
.hist-pago{font-size:.82rem; color:var(--tinta-suave)}
.hist-total{font-weight:700; white-space:nowrap}
.hist-detalle{padding:0 .8rem .8rem; border-top:1px dashed var(--linea)}
.hist-detalle ul{list-style:none; margin:.5rem 0 0; padding:0}
.hist-detalle li{display:flex; justify-content:space-between; gap:1rem; padding:.2rem 0}
.qr-caja{
display:grid; grid-template-columns:minmax(0,1fr) minmax(0,1fr);
gap:1.25rem; align-items:center; background:#fff; border:1px solid var(--linea);
border-radius:1rem; padding:1.25rem; margin:1rem 0;
}
.qr-imagen{width:100%; max-width:20rem; margin:0 auto; display:block; border:1px solid var(--linea); border-radius:.6rem}
.qr-falta{background:var(--mal-fondo); padding:1rem; border-radius:.6rem; color:#8A1B28}
.qr-falta code{display:inline-block; background:#fff; padding:.2rem .4rem; border-radius:.3rem}
.url-publica{
font-family:ui-monospace,SFMono-Regular,Consolas,monospace;
background:var(--fondo); padding:.5rem .6rem; border-radius:.4rem;
overflow-wrap:anywhere; font-size:.9rem;
}
.error-pagina{
background:#fff; border:1px solid var(--linea); border-radius:1rem;
padding:1.5rem; margin:1.5rem 0;
}
.error-codigo{
font-family:"Bricolage Grotesque",sans-serif; font-size:4rem; line-height:1;
color:var(--mango); font-weight:800;
}
@media (max-width:34rem){
.login-caja{grid-template-columns:1fr}
.qr-caja{grid-template-columns:1fr}
.totales{grid-template-columns:1fr 1fr}
.total-grande{grid-column:1/-1}
.fila-inventario{grid-template-columns:1fr 1fr}
.fila-inventario .campo-nombre{grid-column:1/-1}
.fila-inventario .btn{grid-column:1/-1}
.historial-item summary{grid-template-columns:auto minmax(0,1fr) auto}
.hist-pago{grid-column:2}
.hist-total{grid-column:3; grid-row:1}
.historial-item summary .estado{grid-column:2}
}
@media (max-width:30rem){
.panel-resumen{grid-template-columns:1fr 1fr}
.panel-resumen .resumen-item:last-child{grid-column:1/-1}
.pedido-card{grid-template-columns:4rem minmax(0,1fr)}
.pedido-turno strong{font-size:2.1rem}
.form-nequi{grid-template-columns:1fr}
.form-nequi input,.form-nequi button{grid-column:1}
}
@media (max-width:25rem){
.producto{grid-template-columns:1fr; gap:.6rem}
.contador{justify-self:start}
.agotado-texto{justify-self:start}
.mi-pedido{grid-template-columns:auto minmax(0,1fr)}
.mi-pedido .estado{grid-column:2}
.top-lista li{grid-template-columns:minmax(0,1fr) auto}
.barra-top{display:none}
}
@media (prefers-reduced-motion:reduce){
html{scroll-behavior:auto}
*,*::before,*::after{
animation-duration:.01ms !important;
animation-iteration-count:1 !important;
transition-duration:.01ms !important;
}
.btn:active{transform:none}
}
@media (prefers-reduced-motion:no-preference){
.turno-panel{animation:aparece .45s ease-out}
@keyframes aparece{from{transform:scale(.97); opacity:.85}to{transform:none; opacity:1}}
}

/* RICURAS CONTRASTE V2 */
:root{color-scheme:only light;--tinta:#142033;--mango:#ffb648;--chile:#ad2424;
--fondo:#f1f5f9;--blanco:#ffffff;--linea:#cbd5e1;--tinta-suave:#475569;
--ok:#166534;--ok-fondo:#e8f5eb;--mal-fondo:#fff0f0;
--sombra:0 8px 24px #1420330c}
html{color-scheme:only light!important;background:#f1f5f9!important}
body{color-scheme:only light!important;background:#f1f5f9!important;color:#142033!important;
-webkit-font-smoothing:antialiased}
::selection{background:#ffb648;color:#142033}
.contenedor{max-width:74rem;padding-inline:clamp(1rem,4vw,3rem)}
.pagina-panel{max-width:74rem;padding-top:2rem;padding-bottom:4rem}
.pagina-angosta{max-width:60rem}.seguimiento{max-width:42rem}
.avisos{max-width:74rem}.aviso{border-radius:12px}
h1,h2,h3{letter-spacing:-.035em}
.hero{padding:3rem 0 3.5rem;background:#142033!important;color:#fff!important}
.hero::before,.hero::after,.marca::before,.marca-clara::before,.marca-enlace::before{
content:none!important;display:none!important}
.hero-interior{min-height:0;padding-right:clamp(1rem,4vw,3rem)}
.hero .sobrelinea{color:#ffb648;font-size:.82rem;font-weight:700;letter-spacing:.17em;text-transform:uppercase}
.hero h1{font-size:clamp(4.3rem,11vw,8rem);line-height:1;letter-spacing:-.055em;
margin:.7rem 0 1rem;max-width:none;color:#fff!important}
.hero p{color:#e2e8f0;font-size:1.05rem;max-width:40rem;line-height:1.65}
.hero-pista{color:#e2e8f0!important;font-size:.9rem!important;margin-top:1.2rem}
.punto{background:#ffb648;box-shadow:0 0 0 4px #ffb64822}
.marca,.marca-clara,.marca-enlace{font-size:2.15rem!important;font-weight:800;color:#fff!important;
letter-spacing:-.04em;text-decoration:none}
.marca-clara span{font-size:.75rem;color:#e2e8f0;margin-left:.7rem;letter-spacing:.05em;
border:1px solid #94a3b866;border-radius:99px;padding:.25rem .6rem;vertical-align:middle}
.top-panel,.top-simple{background:#142033!important;color:#fff!important}
.top-panel{padding-top:1.3rem}.top-panel>.contenedor{max-width:74rem}
.enlace-claro{color:#fff!important;font-weight:600}
.panel-nav{gap:.35rem;margin-top:1.1rem;padding-bottom:.8rem}
.panel-nav a{color:#e2e8f0!important;border:0;border-radius:9px;padding:.7rem .9rem}
.panel-nav a:hover{background:#ffffff15}
.panel-nav a[aria-current=page]{color:#142033!important;background:#ffb648;border:0;font-weight:700}
.btn{background:#ffb648!important;color:#142033!important;border:1px solid #d99028;
border-radius:10px;min-height:48px;padding:.8rem 1.2rem;font-weight:700;
transition:background .15s,box-shadow .15s}
.btn:hover{background:#ffca7b!important;box-shadow:0 4px 14px #14203318}
.btn-sec{background:#fff!important;color:#142033!important;border-color:#94a3b8}
.btn-sec:hover{background:#e9eff5!important}
.btn-ok{background:#166534!important;color:#fff!important;border-color:#166534}
.btn-ok:hover{background:#14532d!important}
.btn-peligro,.btn-peligro-suave{background:#fff!important;color:#991b1b!important;border-color:#c66a6a}
.btn-peligro:hover,.btn-peligro-suave:hover{background:#fff0f0!important}
.btn:disabled{background:#e2e8f0!important;color:#64748b!important;border-color:#cbd5e1;box-shadow:none}
.btn-pequeno{min-height:40px}.btn-pequeno:hover{transform:none}
input[type=text],input[type=number],input[type=password],input[type=date],input[type=tel]{
color-scheme:only light;background:#fff!important;color:#142033!important;border:1px solid #94a3b8;
border-radius:9px;min-height:48px}
input::placeholder{color:#64748b!important}
input:focus{border-color:#142033;box-shadow:0 0 0 3px #14203312}
:focus-visible{outline:3px solid #b45309;outline-offset:3px}
.pagina-menu{padding-top:2.5rem;padding-bottom:10rem}
.titulo-seccion{align-items:center;margin-bottom:1.5rem;gap:1rem}
.titulo-seccion h2{font-size:2rem;color:#142033}
.titulo-seccion p{color:#475569;font-size:.9rem;margin-top:.5rem}
.enlace-suave{border:1px solid #94a3b8;padding:.6rem 1rem;border-radius:99px;text-decoration:none}
.enlace-suave:hover{background:#fff}
.menu{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:1rem;border:0;margin-top:0}
.producto{background:#fff!important;color:#142033!important;border:1px solid #cbd5e1;border-radius:16px;
padding:1.5rem;min-height:142px;box-shadow:var(--sombra);gap:1rem}
.producto:hover{border-color:#64748b}
.producto-texto{min-width:0;padding:0;border:0}
.producto h3{color:#142033!important;font-size:1.4rem;line-height:1.2;overflow-wrap:anywhere}
.producto-meta{gap:.5rem .75rem;margin-top:.75rem}
.precio{color:#142033!important;font-size:1.2rem;font-variant-numeric:tabular-nums}
.stock{background:#e8eef5!important;color:#334155!important;font-size:.8rem;padding:.25rem .6rem}
.stock-poco,.stock-cero{background:#fff0e6!important;color:#8a3100!important}
.producto.agotado{background:#f8fafc!important}.producto.agotado h3{color:#64748b!important}
.contador{background:#f1f5f9!important;color:#142033!important;border:1px solid #cbd5e1;
border-radius:11px;padding:.25rem;gap:.25rem}
.cantidad{color:#142033!important;font-size:1rem;min-width:1.6rem}
.contador button{background:#142033!important;color:#fff!important;border-radius:8px;width:2.4rem;height:2.5rem}
.contador button:disabled{background:#e2e8f0!important;color:#64748b!important}
.contador button:hover:not(:disabled){background:#334155!important}
.barra{left:50%;right:auto;bottom:1rem;transform:translateX(-50%);width:min(68rem,calc(100% - 2rem));
background:#142033!important;color:#fff!important;border-radius:16px;padding:1rem 0;box-shadow:0 12px 30px #14203333}
.barra .contenedor{padding-inline:1.5rem}.barra strong{color:#fff!important;font-size:1.4rem}
.barra-cantidad{color:#e2e8f0!important}
.dialogo{background:#f1f5f9!important;color:#142033!important;border-radius:20px;padding:1.5rem}
dialog::backdrop{background:#142033b8}.cerrar{background:#e2e8f0;color:#142033}
.opcion{background:#fff!important;color:#142033!important;border-radius:12px;padding:1rem}
.opcion:has(input:checked){border-color:#142033;box-shadow:inset 0 0 0 1px #142033}
.opcion small,.nota,.subtitulo{color:#475569}
.panel-resumen{gap:1rem;margin-bottom:1.5rem}
.resumen-item{background:#fff!important;color:#142033!important;border:1px solid #cbd5e1;
border-radius:16px;padding:1.4rem;gap:.6rem}
.resumen-num{font-size:2.7rem}.resumen-item span:last-child{color:#334155;font-size:.9rem}
.resumen-pendiente{background:#fff5e0!important;border-color:#d2a34e}
.resumen-listo{background:#edf8ed!important;border-color:#79a984}
.config-nequi,.agregar-producto,.caja-pago,.resumen-pedido,.qr-caja,.error-pagina,.total-metodo{
background:#fff!important;color:#142033!important;border:1px solid #cbd5e1;border-radius:16px;
padding:1.5rem;box-shadow:var(--sombra)}
.form-nequi h2{font-size:1.4rem}.panel-encabezado{margin:2rem 0 1.25rem;align-items:center}
.panel-encabezado h1{font-size:2.3rem}.panel-encabezado p{color:#475569;margin-top:.5rem}
.lista-pedidos{gap:1.25rem}
.pedido-card{background:#fff!important;color:#142033!important;border-radius:16px;
grid-template-columns:5rem minmax(0,1fr);box-shadow:var(--sombra)}
.pedido-turno{background:#ffb648!important;color:#142033!important}.pedido-turno strong{font-size:2.8rem}
.pedido-cuerpo{padding:1.3rem}.pedido-cabecera h2{color:#142033!important;font-size:1.35rem}
.pedido-lineas{border-top:1px solid #e2e8f0;border-bottom:1px solid #e2e8f0;padding:.65rem 0}
.pedido-lineas li{padding:.25rem 0}.pedido-acciones{gap:.6rem}
.panel-vacio{background:#fff!important;color:#475569;border-radius:16px;padding:2.5rem 1rem}
.fila-inventario{background:#fff!important;color:#142033;border:1px solid #cbd5e1;border-radius:12px;padding:1rem;gap:1rem}
.fila-inventario label{color:#334155;margin-bottom:.4rem}.fila-inventario.inactivo{background:#f8fafc!important}
.filtro-fecha{background:#fff!important;border-radius:12px;padding:1rem;gap:.8rem}
.total-grande{background:#142033!important;border-radius:16px;padding:1.5rem}
.total-grande strong{color:#ffb648!important}.total-grande p,.total-grande small{color:#e2e8f0!important}
.historial-item{background:#fff!important;color:#142033!important;border-radius:12px}
.historial-item summary{padding:1rem}.historial-item summary:hover{background:#f1f5f9}
.hist-detalle{padding:1rem}.hist-cliente,.hist-total{color:#142033}.hist-pago{color:#475569}
.qr-imagen{background:#fff!important;filter:none!important;mix-blend-mode:normal;
padding:1rem;border:1px solid #cbd5e1;border-radius:12px}
.url-publica{background:#e8eef5!important;color:#142033!important;padding:.8rem;font-size:.95rem;border-radius:8px}
.nota-error{background:#fff0f0!important;color:#991b1b!important}
.login-caja{background:#fff;border-radius:20px;box-shadow:var(--sombra);margin:2.5rem 0}
.login-intro{background:#142033!important;padding:2rem}.login-intro h1{color:#fff!important;font-size:2.8rem;line-height:1.1}
.login-intro .sobrelinea{color:#ffb648}.login-intro p{color:#e2e8f0}
.login-caja .formulario{padding:2rem}.login-caja .formulario>.btn{width:100%;margin-top:1.25rem}
.turno-panel{background:#ffb648!important;color:#142033!important;border-radius:20px;padding:1.5rem}
.mi-pedido{background:#fff!important;color:#142033!important;border-radius:12px;padding:1rem}
.mi-turno{background:#ffb648!important;color:#142033!important}.pie{color:#475569}
@media(min-width:70rem){.lista-pedidos{grid-template-columns:repeat(2,minmax(0,1fr))}}
@media(max-width:46rem){
.menu{grid-template-columns:1fr}.hero{padding:2.2rem 0}.hero h1{font-size:clamp(4rem,17vw,6rem)}
.hero p{font-size:1rem}.producto{padding:1.2rem;min-height:120px}.producto h3{font-size:1.25rem}
.resumen-item{padding:1rem}.resumen-num{font-size:2.2rem}.resumen-item span:last-child{font-size:.8rem}
.login-caja{grid-template-columns:1fr}.login-intro,.login-caja .formulario{padding:1.5rem}
.fila-inventario{grid-template-columns:1fr 1fr;gap:.75rem}
.fila-inventario .campo-nombre,.fila-inventario .btn{grid-column:1/-1}
.historial-item summary{grid-template-columns:auto minmax(0,1fr) auto}
.hist-pago{grid-column:2}.hist-total{grid-column:3;grid-row:1}.historial-item summary .estado{grid-column:2}
}
@media(max-width:30rem){
.producto{gap:.75rem}.contador button{width:2.1rem}.producto h3{font-size:1.2rem}
.marca-clara,.marca-enlace{font-size:1.8rem!important}.panel-nav a{padding:.6rem .8rem}
.pedido-card{grid-template-columns:3.5rem minmax(0,1fr)}.pedido-cuerpo{padding:1rem}
.config-nequi,.qr-caja{padding:1rem}.barra{width:calc(100% - 1rem);bottom:.5rem}
.barra .contenedor{padding-inline:1rem}.barra .btn{padding:.7rem .9rem}
}


/* RICURAS ANCHO AMPLIADO */
.hero .contenedor,.contenedor.pagina-menu,.contenedor.pagina-panel,
.top-panel>.contenedor,.top-simple>.contenedor{
width:94%;max-width:100rem;margin-inline:auto;padding-inline:0;
}
.hero-interior{padding-right:0;min-height:0}
.hero h1{max-width:24ch}
.hero p{max-width:64rem}
.hero .marca{font-size:clamp(2rem,3.5vw,3rem)!important;line-height:1.15;margin-bottom:1rem}
.avisos{width:94%;max-width:100rem;padding-inline:0}
.barra{width:min(94%,100rem);max-width:none}
.barra .contenedor{max-width:none;width:100%;padding-inline:1.5rem}
@media(min-width:60rem){
.menu{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));column-gap:2rem;row-gap:1rem}
.producto{min-width:0}
}
@media(max-width:46rem){
.hero .contenedor,.contenedor.pagina-menu,.contenedor.pagina-panel,
.top-panel>.contenedor,.top-simple>.contenedor{width:100%;padding-inline:1rem}
.hero h1{max-width:100%}
.avisos{width:100%;padding-inline:1rem}
.barra{width:calc(100% - 1rem)}
.barra .contenedor{padding-inline:1rem}
}


/* RICURAS MARCA AMARILLA */
.hero .marca,.top-panel .marca-clara,.top-simple .marca-enlace{
color:#ffbe20!important;
}

</style>
</head>
<body>
<a class="saltar" href="#contenido">Saltar al contenido</a>
{% with mensajes = get_flashed_messages(with_categories=true) %}
{% if mensajes %}
<div class="avisos">
{% for categoria, mensaje in mensajes %}
<p class="aviso {{ categoria }}" role="{{ 'alert' if categoria == 'error' else 'status' }}">{{ mensaje }}</p>
{% endfor %}
</div>
{% endif %}
{% endwith %}
{% block cuerpo %}{% endblock %}
</body>
</html>"""

NAV_VENDEDOR = """<header class="top-panel">
<div class="contenedor">
<div class="panel-barra">
<a class="marca-clara" href="{{ url_for('panel') }}">Ricuras <span>panel</span></a>
<a class="enlace-claro" href="{{ url_for('salir') }}">Salir</a>
</div>
<nav class="panel-nav" aria-label="Secciones del panel">
<a href="{{ url_for('panel') }}" {% if request.endpoint == 'panel' %}aria-current="page"{% endif %}>Pedidos</a>
<a href="{{ url_for('inventario') }}" {% if request.endpoint == 'inventario' %}aria-current="page"{% endif %}>Inventario</a>
<a href="{{ url_for('historial') }}" {% if request.endpoint == 'historial' %}aria-current="page"{% endif %}>Historial</a>
<a href="{{ url_for('qr_pagina') }}" {% if request.endpoint == 'qr_pagina' %}aria-current="page"{% endif %}>Código QR</a>
<a href="{{ url_for('cuenta') }}" {% if request.endpoint == 'cuenta' %}aria-current="page"{% endif %}>Mi cuenta</a>
<a href="{{ url_for('menu') }}">Ver menú</a>
</nav>
</div>
</header>"""

MENU = """{% extends "base.html" %}
{% block titulo %}Pedir en Ricuras{% endblock %}
{% block cuerpo %}
<header class="hero">
<div class="contenedor hero-interior">
<p class="marca">Ricuras</p>
<h1 style="font-size:clamp(2.8rem,6vw,5.2rem)">El antojo <span>ya tiene turno.</span></h1>
<p>Pide desde tu celular, paga en efectivo o por Nequi y recoge cuando esté listo.</p>
<p class="hero-pista"><span class="punto" aria-hidden="true"></span> Sin cuenta. Sin filas para pedir.</p>
</div>
</header>
<main id="contenido" class="contenedor pagina-menu">
<div class="titulo-seccion">
<div>
<h2>Menú de hoy</h2>
<p>Las unidades disponibles se descuentan al confirmar tu pedido.</p>
</div>
<a class="enlace-suave" href="{{ url_for('mis_pedidos') }}">Mis pedidos</a>
</div>

<noscript>
<p class="aviso error">Activa JavaScript para armar y enviar tu pedido.</p>
</noscript>

<ul class="menu">
{% for i in items %}
<li class="producto {% if i.stock <= 0 %}agotado{% endif %}"
data-id="{{ i.id }}" data-precio="{{ i.precio }}" data-max="{{ i.stock }}">
<div class="producto-texto">
<h3>{{ i.nombre }}</h3>
<p class="producto-meta">
<span class="precio">{{ i.precio|cop }}</span>
{% if i.stock <= 0 %}
<span class="stock stock-cero">Agotado</span>
{% elif i.stock <= 3 %}
<span class="stock stock-poco">Quedan {{ i.stock }}</span>
{% else %}
<span class="stock">Quedan {{ i.stock }}</span>
{% endif %}
</p>
</div>
{% if i.stock > 0 %}
<div class="contador">
<button type="button" class="menos" aria-label="Quitar una unidad de {{ i.nombre }}" disabled>−</button>
<span class="cantidad" aria-live="polite">0</span>
<button type="button" class="mas" aria-label="Agregar una unidad de {{ i.nombre }}">+</button>
</div>
{% else %}
<span class="agotado-texto">Sin unidades por ahora</span>
{% endif %}
</li>
{% else %}
<li class="vacio">Hoy todavía no hay productos publicados. Vuelve más tarde.</li>
{% endfor %}
</ul>

<p class="nota">Los precios están en pesos colombianos. Si un producto se agota mientras eliges, te avisamos al confirmar.</p>
<footer class="pie">
<a href="{{ url_for('login') }}">Acceso del vendedor</a>
</footer>
</main>

<div class="barra" id="barra" hidden>
<div class="contenedor barra-interior">
<div>
<span class="barra-cantidad" id="resumen">0 productos</span>
<strong id="total-barra">$0</strong>
</div>
<button class="btn" type="button" id="abrir">Revisar pedido</button>
</div>
</div>

<dialog id="carrito" aria-labelledby="carrito-titulo" data-nequi="{{ 1 if nequi else 0 }}">
<div class="dialogo">
<div class="dialogo-cabecera">
<h2 id="carrito-titulo">Confirma tu pedido</h2>
<button type="button" class="cerrar" id="cerrar" aria-label="Cerrar">×</button>
</div>
<ul class="resumen-lista" id="lista"></ul>
<div class="total-linea"><span>Total</span><strong id="total-dialogo">$0</strong></div>

<label for="cliente">Tu nombre (opcional)</label>
<input type="text" id="cliente" name="cliente" maxlength="40" autocomplete="given-name" placeholder="Ej. Ana">

<fieldset class="pago-opciones">
<legend>¿Cómo vas a pagar?</legend>
<label class="opcion">
<input type="radio" name="pago" value="efectivo" checked>
<span><strong>Efectivo</strong><small>Pagas al recoger en el puesto.</small></span>
</label>
<label class="opcion {% if not nequi %}deshabilitada{% endif %}">
<input type="radio" name="pago" value="nequi" {% if not nequi %}disabled{% endif %}>
<span>
<strong>Nequi</strong>
{% if nequi %}
<small>Transfieres y el vendedor confirma tu comprobante.</small>
{% else %}
<small>El vendedor aún no configuró el número Nequi.</small>
{% endif %}
</span>
</label>
</fieldset>

<div class="nequi-aviso" id="nequi-aviso" hidden>
<p><strong>Pago por confirmar.</strong> Al enviar el pedido verás el número Nequi, el monto exacto y tu turno como referencia. Después registras el comprobante.</p>
</div>

<p class="error" id="error" role="alert"></p>
<div class="acciones-dialogo">
<button type="button" class="btn btn-sec" id="seguir">Seguir eligiendo</button>
<button type="button" class="btn" id="enviar">Enviar pedido</button>
</div>
</div>
</dialog>

<script>
(function () {
var filas = Array.prototype.slice.call(document.querySelectorAll('.producto[data-id]'));
var barra = document.getElementById('barra');
var dialogo = document.getElementById('carrito');
var lista = document.getElementById('lista');
var totalDialogo = document.getElementById('total-dialogo');
var botonEnviar = document.getElementById('enviar');
var avisoNequi = document.getElementById('nequi-aviso');
var cajaError = document.getElementById('error');
var cliente = document.getElementById('cliente');
var carrito = {};
try {
carrito = JSON.parse(sessionStorage.getItem('ricuras-carrito') || '{}') || {};
} catch (e) {
carrito = {};
}

function formato(valor) {
return '$' + Number(valor).toLocaleString('es-CO');
}

function guardarCarrito() {
try {
sessionStorage.setItem('ricuras-carrito', JSON.stringify(carrito));
} catch (e) {}
}

function pintar() {
var cantidadTotal = 0;
var total = 0;
filas.forEach(function (fila) {
var id = fila.dataset.id;
var maximo = Number(fila.dataset.max) || 0;
var precio = Number(fila.dataset.precio) || 0;
var cantidad = Number(carrito[id]) || 0;
if (!Number.isInteger(cantidad) || cantidad < 0) cantidad = 0;
cantidad = Math.min(cantidad, maximo);
if (cantidad > 0) carrito[id] = cantidad;
else delete carrito[id];
var etiqueta = fila.querySelector('.cantidad');
var menos = fila.querySelector('.menos');
var mas = fila.querySelector('.mas');
if (etiqueta) etiqueta.textContent = cantidad;
if (menos) menos.disabled = cantidad <= 0;
if (mas) mas.disabled = cantidad >= maximo;
cantidadTotal += cantidad;
total += cantidad * precio;
});
barra.hidden = cantidadTotal === 0;
document.getElementById('resumen').textContent =
cantidadTotal === 1 ? '1 producto' : cantidadTotal + ' productos';
document.getElementById('total-barra').textContent = formato(total);
totalDialogo.textContent = formato(total);
guardarCarrito();
}

function actualizarAvisoPago() {
var elegido = document.querySelector('input[name="pago"]:checked');
avisoNequi.hidden = !elegido || elegido.value !== 'nequi';
}

function abrirDialogo() {
var elegidos = filas.filter(function (fila) {
return (Number(carrito[fila.dataset.id]) || 0) > 0;
});
if (!elegidos.length) return;
lista.innerHTML = '';
elegidos.forEach(function (fila) {
var cantidad = Number(carrito[fila.dataset.id]);
var precio = Number(fila.dataset.precio);
var elemento = document.createElement('li');
var descripcion = document.createElement('span');
var nombre = document.createElement('span');
nombre.textContent = cantidad + ' × ' + fila.querySelector('h3').textContent;
descripcion.appendChild(nombre);
var subtotal = document.createElement('strong');
subtotal.textContent = formato(cantidad * precio);
elemento.appendChild(descripcion);
elemento.appendChild(subtotal);
lista.appendChild(elemento);
});
cajaError.textContent = '';
botonEnviar.disabled = false;
botonEnviar.textContent = 'Enviar pedido';
actualizarAvisoPago();
if (typeof dialogo.showModal === 'function') dialogo.showModal();
else dialogo.setAttribute('open', '');
cliente.focus();
}

function cerrarDialogo() {
if (typeof dialogo.close === 'function') dialogo.close();
else dialogo.removeAttribute('open');
}

filas.forEach(function (fila) {
var id = fila.dataset.id;
var menos = fila.querySelector('.menos');
var mas = fila.querySelector('.mas');
if (!menos || !mas) return;
menos.addEventListener('click', function () {
carrito[id] = Math.max(0, (Number(carrito[id]) || 0) - 1);
pintar();
});
mas.addEventListener('click', function () {
carrito[id] = (Number(carrito[id]) || 0) + 1;
pintar();
});
});

document.getElementById('abrir').addEventListener('click', abrirDialogo);
document.getElementById('cerrar').addEventListener('click', cerrarDialogo);
document.getElementById('seguir').addEventListener('click', cerrarDialogo);
dialogo.addEventListener('click', function (evento) {
if (evento.target === dialogo) cerrarDialogo();
});
Array.prototype.forEach.call(
document.querySelectorAll('input[name="pago"]'),
function (radio) {
radio.addEventListener('change', actualizarAvisoPago);
}
);

botonEnviar.addEventListener('click', async function () {
var seleccion = [];
filas.forEach(function (fila) {
var cantidad = Number(carrito[fila.dataset.id]) || 0;
if (cantidad > 0) {
seleccion.push({ id: Number(fila.dataset.id), cant: cantidad });
}
});
if (!seleccion.length) {
cajaError.textContent = 'Agrega al menos un producto al pedido.';
return;
}
var elegido = document.querySelector('input[name="pago"]:checked');
var pago = elegido ? elegido.value : 'efectivo';
if (pago === 'nequi' && dialogo.dataset.nequi !== '1') {
cajaError.textContent = 'El vendedor todavía no configuró Nequi. Elige efectivo.';
return;
}

botonEnviar.disabled = true;
botonEnviar.textContent = 'Enviando…';
cajaError.textContent = '';
try {
var respuesta = await fetch('{{ url_for("pedir") }}', {
method: 'POST',
headers: { 'Content-Type': 'application/json', 'Accept': 'application/json' },
body: JSON.stringify({ cliente: cliente.value, pago: pago, items: seleccion })
});
var datos = null;
try { datos = await respuesta.json(); } catch (e) { datos = null; }
if (respuesta.ok && datos && datos.ok) {
try { sessionStorage.removeItem('ricuras-carrito'); } catch (e) {}
window.location.href = datos.url;
return;
}
cajaError.textContent = (datos && datos.error) ||
'No pudimos enviar el pedido. Revisa tu conexión e inténtalo de nuevo.';
} catch (e) {
cajaError.textContent = 'No hay conexión. Revisa tu internet e inténtalo de nuevo.';
}
botonEnviar.disabled = false;
botonEnviar.textContent = 'Enviar pedido';
});

pintar();
})();
</script>
{% endblock %}"""

MIS_PEDIDOS = """{% extends "base.html" %}
{% block titulo %}Mis pedidos · Ricuras{% endblock %}
{% block cuerpo %}
<header class="top-simple">
<div class="contenedor top-fila">
<a class="marca-enlace" href="{{ url_for('menu') }}">Ricuras</a>
<a class="enlace-claro" href="{{ url_for('menu') }}">Volver al menú</a>
</div>
</header>
<main id="contenido" class="contenedor pagina-angosta">
<h1 class="titulo-pagina">Mis pedidos</h1>
<p class="subtitulo">Estos son los pedidos hechos desde este navegador. La sesión se borra al cerrar el navegador, así que guarda el enlace de tu pedido si lo necesitas.</p>

{% if pedidos %}
<ul class="lista-mis">
{% for p in pedidos %}
<li>
<a class="mi-pedido" href="{{ url_for('ver_pedido', pid=p.id) }}">
<span class="mi-turno" aria-hidden="true">{{ p.turno }}</span>
<span class="mi-datos">
<strong>Turno {{ p.turno }}</strong>
<small>{{ p.fecha }} · {{ pagos[p.pago] if pagos is defined else p.pago }} · {{ p.total|cop }}</small>
</span>
<span class="estado estado-{{ p.estado }}">{{ estados[p.estado] }}</span>
</a>
</li>
{% endfor %}
</ul>
{% else %}
<div class="panel-vacio">
<p>Todavía no hay pedidos en este navegador.</p>
<p><a class="btn" href="{{ url_for('menu') }}">Ver el menú</a></p>
</div>
{% endif %}

<div class="acciones-pedido">
<a class="btn" href="{{ url_for('menu') }}">Pedir algo más</a>
</div>
<footer class="pie"><a href="{{ url_for('login') }}">Acceso del vendedor</a></footer>
</main>
{% endblock %}"""

PEDIDO = """{% extends "base.html" %}
{% block titulo %}Turno {{ p.turno }} · Ricuras{% endblock %}
{% block cuerpo %}
<header class="top-simple">
<div class="contenedor top-fila">
<a class="marca-enlace" href="{{ url_for('menu') }}">Ricuras</a>
<a class="enlace-claro" href="{{ url_for('mis_pedidos') }}">Mis pedidos</a>
</div>
</header>
<main id="contenido" class="contenedor seguimiento">
<section class="turno-panel">
<p class="etiqueta-turno">Tu turno de hoy</p>
<div class="turno-numero">{{ p.turno }}</div>
<div class="turno-pie">
<span class="estado estado-{{ p.estado }}" id="estado" aria-live="polite">{{ estados[p.estado] }}</span>
<span>{{ p.fecha }} · {{ p.creado|hora }}</span>
</div>
</section>

{% if p.estado == 'cancelado' %}
<div class="aviso-cancelado">
Este pedido fue cancelado y las unidades volvieron al inventario.
{% if p.pago == 'nequi' and p.pago_estado == 'confirmado' %}
Si ya pagaste, acércate al puesto para coordinar la devolución.
{% endif %}
</div>
{% endif %}

{% if p.pago == 'nequi' %}
<section class="caja-pago {% if p.pago_estado == 'pendiente' %}caja-pendiente{% elif p.pago_estado == 'confirmado' %}caja-ok{% elif p.pago_estado == 'rechazado' %}caja-mal{% endif %}" id="pago">
<div class="pedido-cabecera">
<h2>Pago por Nequi</h2>
<span class="estado {% if p.pago_estado == 'pendiente' %}estado-pago_pendiente{% elif p.pago_estado == 'confirmado' %}estado-listo{% else %}estado-cancelado{% endif %}" id="pago-estado">
{{ pago_estados[p.pago_estado] }}
</span>
</div>

{% if p.pago_estado == 'pendiente' %}
<p>Transfiere <strong>{{ p.total|cop }}</strong> al Nequi
<strong>{{ p.nequi_numero or nequi_actual or 'sin configurar' }}</strong>
y escribe <strong>turno {{ p.turno }}</strong> como referencia.</p>
<p class="nota">Tu pedido queda en “Pago por confirmar” hasta que el vendedor verifique el comprobante. Las unidades ya están reservadas.</p>

{% if p.comprobante %}
<p class="comprobante">Comprobante registrado: <strong>{{ p.comprobante }}</strong></p>
{% else %}
<p class="nota-error">Aún no has registrado el comprobante. El vendedor no puede confirmar el pago sin él.</p>
{% endif %}

<form method="post" action="{{ url_for('guardar_comprobante', pid=p.id) }}" class="form-comprobante">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<label for="comprobante">{{ 'Corrige el código del comprobante' if p.comprobante else 'Código o últimos dígitos del comprobante' }}</label>
<input id="comprobante" name="comprobante" maxlength="30" required autocomplete="off"
value="{{ p.comprobante or '' }}" placeholder="Ej. 1234567890">
<p class="nota">Usa entre 4 y 30 letras, números o guiones, sin espacios.</p>
<button class="btn" type="submit">Guardar comprobante</button>
</form>

{% elif p.pago_estado == 'confirmado' %}
<p class="nota-ok">Pago confirmado. Ya estamos preparando tu pedido.</p>
{% elif p.pago_estado == 'rechazado' %}
<p class="nota-error">El vendedor no pudo verificar el pago. El pedido fue cancelado y las unidades volvieron al inventario. Acércate al puesto para resolverlo.</p>
{% endif %}
</section>
{% else %}
<section class="caja-pago">
<h2>Pago en efectivo</h2>
<p>Paga <strong>{{ p.total|cop }}</strong> en el puesto cuando reclames tu turno. No necesitas pagar ahora.</p>
</section>
{% endif %}

{% if p.estado != 'cancelado' %}
<ol class="pasos" aria-label="Estado del pedido">
{% for clave, texto in pasos %}
<li class="paso {% if loop.index0 < indice %}completo{% endif %} {% if loop.index0 == indice %}actual{% endif %}">
<span class="paso-punto" aria-hidden="true"></span>
<span>{{ texto }}</span>
</li>
{% endfor %}
</ol>
{% endif %}

<section class="resumen-pedido">
<div class="pedido-cabecera">
<h2>Tu pedido</h2>
<span class="nota">{{ p.pago == 'nequi' and 'Nequi' or 'Efectivo' }}</span>
</div>
<ul class="lineas">
{% for d in det %}
<li>
<span>{{ d.cantidad }} × {{ d.nombre }}</span>
<strong>{{ (d.cantidad * d.precio)|cop }}</strong>
</li>
{% endfor %}
</ul>
<div class="total-final"><span>Total</span><strong>{{ p.total|cop }}</strong></div>
<p class="nota">A nombre de {{ p.cliente }}.</p>
</section>

<div class="acciones-pedido">
<a class="btn" href="{{ url_for('menu') }}">Pedir algo más</a>
<a class="btn btn-sec" href="{{ url_for('mis_pedidos') }}">Ver mis pedidos</a>
</div>
<p class="conexion" id="conexion" role="status" aria-live="polite"></p>
</main>

{% if p.estado not in ['entregado', 'cancelado'] %}
<script>
(function () {
var actual = {{ p.estado|tojson }};
var urlEstado = {{ url_for('estado_pedido', pid=p.id)|tojson }};
var conexion = document.getElementById('conexion');
var revisando = false;
var vivo = true;

async function revisar() {
if (!vivo || revisando || document.hidden) return;
revisando = true;
try {
var respuesta = await fetch(urlEstado, {
headers: { 'Accept': 'application/json' },
cache: 'no-store'
});
if (!respuesta.ok) throw new Error('sin respuesta');
var datos = await respuesta.json();
conexion.textContent = '';
if (datos.estado !== actual) {
var activo = document.activeElement;
var escribiendo = activo && (
activo.tagName === 'INPUT' ||
activo.tagName === 'TEXTAREA' ||
activo.tagName === 'SELECT'
);
if (!escribiendo) {
vivo = false;
window.location.reload();
return;
}
}
} catch (e) {
conexion.textContent = 'No podemos actualizar el estado. Revisa tu conexión.';
}
revisando = false;
}

setInterval(revisar, 5000);
document.addEventListener('visibilitychange', function () {
if (!document.hidden) revisar();
});
revisar();
})();
</script>
{% endif %}
{% endblock %}"""

LOGIN = """{% extends "base.html" %}
{% block titulo %}Acceso del vendedor · Ricuras{% endblock %}
{% block cuerpo %}
<header class="top-simple">
<div class="contenedor top-fila">
<a class="marca-enlace" href="{{ url_for('menu') }}">Ricuras</a>
<a class="enlace-claro" href="{{ url_for('menu') }}">Volver al menú</a>
</div>
</header>
<main id="contenido" class="contenedor pagina-angosta">
<div class="login-caja">
<div class="login-intro">
<p class="sobrelinea">Panel del vendedor</p>
<h1>Todo el puesto, en orden.</h1>
<p>Ingresa con tu usuario y tu clave para manejar pedidos, pagos e inventario.</p>
</div>
<form method="post" class="formulario">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<label for="usuario">Usuario</label>
<input id="usuario" name="usuario" type="text" autocomplete="username" maxlength="30" required autofocus>
<label for="clave">Clave</label>
<input id="clave" name="clave" type="password" autocomplete="current-password" required>
{% if error %}<p class="error" role="alert">{{ error }}</p>{% endif %}
<button class="btn" type="submit">Entrar</button>
<p class="nota">La cuenta se guarda en la base de datos del puesto. Si no tienes una, pídesela al administrador.</p>
</form>
</div>
<footer class="pie"><a href="{{ url_for('menu') }}">Volver a Ricuras</a></footer>
</main>
{% endblock %}"""

CUENTA = """{% extends "base.html" %}
{% block titulo %}Mi cuenta · Panel Ricuras{% endblock %}
{% block cuerpo %}
{% include "nav_vendedor" %}
<main id="contenido" class="contenedor pagina-panel">
<div class="panel-encabezado">
<div>
<h1>Mi cuenta</h1>
<p>Cambia el usuario o la clave con los que entras al panel.</p>
</div>
</div>

{% if clave_inicial %}
<p class="nota-error">Estás usando la clave inicial. Cámbiala ahora para proteger el panel.</p>
{% endif %}

<section class="config-nequi">
<form method="post" class="formulario">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<label for="usuario">Usuario</label>
<input id="usuario" name="usuario" value="{{ usuario }}" maxlength="30" required autocomplete="username">
<label for="clave_actual">Clave actual</label>
<input id="clave_actual" name="clave_actual" type="password" required autocomplete="current-password">
<label for="clave_nueva">Nueva clave (opcional)</label>
<input id="clave_nueva" name="clave_nueva" type="password" minlength="8" maxlength="128" autocomplete="new-password">
<label for="clave_confirmar">Repite la nueva clave</label>
<input id="clave_confirmar" name="clave_confirmar" type="password" minlength="8" maxlength="128" autocomplete="new-password">
<p class="nota">La clave debe tener al menos 8 caracteres. Si dejas la nueva clave vacía, solo se cambia el usuario.</p>
<button class="btn" type="submit">Guardar cambios</button>
</form>
</section>

<footer class="pie"><a href="{{ url_for('panel') }}">Volver a pedidos</a></footer>
</main>
{% endblock %}"""

ERROR = """{% extends "base.html" %}
{% block titulo %}{{ codigo }} · Ricuras{% endblock %}
{% block cuerpo %}
<header class="top-simple">
<div class="contenedor top-fila">
<a class="marca-enlace" href="{{ url_for('menu') }}">Ricuras</a>
<a class="enlace-claro" href="{{ url_for('menu') }}">Volver al menú</a>
</div>
</header>
<main id="contenido" class="contenedor pagina-angosta">
<div class="error-pagina">
<p class="error-codigo">{{ codigo }}</p>
<h1 class="titulo-pagina">{{ titulo }}</h1>
<p>{{ mensaje }}</p>
<div class="acciones-pedido">
<a class="btn" href="{{ url_for('menu') }}">Ir al menú</a>
<a class="btn btn-sec" href="{{ url_for('mis_pedidos') }}">Mis pedidos</a>
</div>
</div>
</main>
{% endblock %}"""

PANEL = """{% extends "base.html" %}
{% block titulo %}Pedidos · Panel Ricuras{% endblock %}
{% block cuerpo %}
{% include "nav_vendedor" %}
<main id="contenido" class="contenedor pagina-panel" data-fp="{{ fp }}">
{% if clave_inicial %}
<p class="nota-error">Estás usando la clave inicial. <a href="{{ url_for('cuenta') }}">Cámbiala en Mi cuenta</a>.</p>
{% endif %}
<section class="panel-resumen" aria-label="Resumen de pedidos activos">
<div class="resumen-item resumen-pendiente">
<span class="resumen-num">{{ pendientes }}</span>
<span>pagos por confirmar</span>
</div>
<div class="resumen-item">
<span class="resumen-num">{{ cocina }}</span>
<span>en cocina</span>
</div>
<div class="resumen-item resumen-listo">
<span class="resumen-num">{{ listos }}</span>
<span>listos para entregar</span>
</div>
</section>

<section class="config-nequi" id="nequi">
<form method="post" action="{{ url_for('guardar_nequi') }}" class="form-nequi">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<div>
<h2>Cobros por Nequi</h2>
<p>Este número se muestra al comprador al elegir Nequi. Cámbialo cuando quieras.</p>
</div>
<label for="nequi_numero">Número Nequi</label>
<input id="nequi_numero" name="nequi_numero" value="{{ nequi }}" inputmode="numeric"
pattern="[0-9]*" maxlength="15" placeholder="Ej. 3001234567">
<button class="btn btn-sec" type="submit">Guardar número</button>
</form>
{% if not nequi %}
<p class="nota-error">Sin número Nequi, los pedidos nuevos con ese método quedan desactivados.</p>
{% endif %}
</section>

<div class="panel-encabezado">
<div>
<h1>Pedidos activos</h1>
<p>Los pagos por confirmar aparecen primero.</p>
</div>
<a class="btn btn-sec btn-pequeno" href="{{ url_for('panel') }}">Actualizar</a>
</div>

{% if pedidos %}
<div class="lista-pedidos">
{% for p in pedidos %}
<article class="pedido-card estado-{{ p.estado }}" id="pedido-{{ p.id }}">
<div class="pedido-turno">
<span>Turno</span>
<strong>{{ p.turno }}</strong>
</div>
<div class="pedido-cuerpo">
<header class="pedido-cabecera">
<div>
<h2>{{ p.cliente }}</h2>
<p class="pedido-hora">{{ p.creado|hora }} · {{ p.fecha }}</p>
</div>
<span class="estado estado-{{ p.estado }}">{{ estados[p.estado] }}</span>
</header>

<p class="pedido-pago">
<strong>{{ pagos[p.pago] }}</strong>
{% if p.pago == 'nequi' %} · {{ pago_estados[p.pago_estado] }}{% endif %}
· {{ p.total|cop }}
</p>

<ul class="pedido-lineas">
{% for d in det[p.id] %}
<li><span>{{ d.cantidad }} × {{ d.nombre }}</span><strong>{{ (d.cantidad * d.precio)|cop }}</strong></li>
{% endfor %}
</ul>

{% if p.pago == 'nequi' %}
<p class="comprobante-linea">
{% if p.comprobante %}
Comprobante: <strong>{{ p.comprobante }}</strong>
{% else %}
<span class="falta">Falta el comprobante del comprador.</span>
{% endif %}
</p>
{% endif %}

<div class="pedido-acciones">
{% if p.estado == 'pago_pendiente' %}
{% if p.comprobante %}
<form method="post" action="{{ url_for('confirmar_pago', pid=p.id) }}">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<button class="btn btn-ok" type="submit">Pago confirmado</button>
</form>
{% else %}
<button class="btn" type="button" disabled>Pago confirmado</button>
{% endif %}
<form method="post" action="{{ url_for('rechazar_pago', pid=p.id) }}"
data-confirmar="¿Rechazar este pago? Las unidades volverán al inventario y el pedido quedará cancelado.">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<button class="btn btn-peligro" type="submit">Pago rechazado</button>
</form>
{% else %}
{% if p.estado in sig %}
<form method="post" action="{{ url_for('cambiar_estado', pid=p.id, nuevo=sig[p.estado][0]) }}">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<button class="btn {% if sig[p.estado][0] == 'entregado' %}btn-ok{% endif %}" type="submit">
{{ sig[p.estado][1] }}
</button>
</form>
{% endif %}
<form method="post" action="{{ url_for('cancelar_pedido', pid=p.id) }}"
data-confirmar="¿Cancelar este pedido? Las unidades volverán al inventario.">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<button class="btn btn-peligro-suave" type="submit">Cancelar pedido</button>
</form>
{% endif %}
</div>
</div>
</article>
{% endfor %}
</div>
{% else %}
<div class="panel-vacio">
<p>No hay pedidos activos.</p>
<p>Cuando entre uno, aparecerá aquí. La página revisa si hay novedades cada pocos segundos.</p>
</div>
{% endif %}

<p class="conexion" id="conexion" role="status" aria-live="polite"></p>
<footer class="pie"><a href="{{ url_for('menu') }}">Ver menú del comprador</a></footer>
</main>

<script>
(function () {
var main = document.querySelector('.pagina-panel');
if (!main) return;
var huella = main.dataset.fp;
var url = {{ url_for('panel_actualizaciones')|tojson }};
var conexion = document.getElementById('conexion');
var revisando = false;

async function revisar() {
if (revisando || document.hidden) return;
var activo = document.activeElement;
if (activo && activo.closest && activo.closest('form')) return;
revisando = true;
try {
var respuesta = await fetch(url, {
headers: { 'Accept': 'application/json' },
cache: 'no-store'
});
if (!respuesta.ok) throw new Error('sin respuesta');
var datos = await respuesta.json();
conexion.textContent = '';
if (datos.fp !== huella) {
window.location.reload();
return;
}
} catch (e) {
conexion.textContent = 'No podemos revisar novedades. Usa el botón Actualizar.';
}
revisando = false;
}

Array.prototype.forEach.call(
document.querySelectorAll('form[data-confirmar]'),
function (formulario) {
formulario.addEventListener('submit', function (evento) {
if (!window.confirm(formulario.dataset.confirmar)) {
evento.preventDefault();
}
});
}
);

setInterval(revisar, 10000);
document.addEventListener('visibilitychange', function () {
if (!document.hidden) revisar();
});
})();
</script>
{% endblock %}"""

INVENTARIO = """{% extends "base.html" %}
{% block titulo %}Inventario · Panel Ricuras{% endblock %}
{% block cuerpo %}
{% include "nav_vendedor" %}
<main id="contenido" class="contenedor pagina-panel">
<div class="panel-encabezado">
<div>
<h1>Inventario</h1>
<p>Define precio, unidades disponibles y visibilidad en el menú.</p>
</div>
<a class="btn btn-sec btn-pequeno" href="{{ url_for('panel') }}">Ver pedidos</a>
</div>

<p class="nota">Al guardar unidades reemplazas el stock actual. Los pedidos ya hechos no cambian. Los productos no se borran para conservar el historial.</p>

<div class="tabla-inventario">
{% for i in items %}
<form method="post" class="fila-inventario {% if not i.activo %}inactivo{% endif %}"
aria-label="Editar {{ i.nombre }}">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<input type="hidden" name="accion" value="actualizar">
<input type="hidden" name="id" value="{{ i.id }}">

<div class="campo campo-nombre">
<label for="nombre-{{ i.id }}">Producto</label>
<input id="nombre-{{ i.id }}" name="nombre" value="{{ i.nombre }}" maxlength="60" required>
</div>
<div class="campo">
<label for="precio-{{ i.id }}">Precio</label>
<input id="precio-{{ i.id }}" name="precio" type="number" min="0" max="10000000"
step="1" inputmode="numeric" value="{{ i.precio }}" required>
</div>
<div class="campo">
<label for="stock-{{ i.id }}">Unidades</label>
<input id="stock-{{ i.id }}" name="stock" type="number" min="0" max="100000"
step="1" inputmode="numeric" value="{{ i.stock }}" required>
</div>
<label class="check" for="activo-{{ i.id }}">
<input id="activo-{{ i.id }}" type="checkbox" name="activo" {% if i.activo %}checked{% endif %}>
Mostrar en el menú
</label>
<button class="btn btn-sec" type="submit">Guardar</button>
</form>
{% else %}
<div class="panel-vacio">Todavía no hay productos. Agrega el primero abajo.</div>
{% endfor %}
</div>

<section class="agregar-producto">
<h2>Agregar producto</h2>
<form method="post" class="fila-inventario">
<input type="hidden" name="csrf" value="{{ csrf_token() }}">
<input type="hidden" name="accion" value="nuevo">
<div class="campo campo-nombre">
<label for="nuevo-nombre">Producto</label>
<input id="nuevo-nombre" name="nombre" maxlength="60" required placeholder="Ej. Arepa de queso">
</div>
<div class="campo">
<label for="nuevo-precio">Precio</label>
<input id="nuevo-precio" name="precio" type="number" min="0" max="10000000"
step="1" inputmode="numeric" required>
</div>
<div class="campo">
<label for="nuevo-stock">Unidades</label>
<input id="nuevo-stock" name="stock" type="number" min="0" max="100000"
step="1" inputmode="numeric" value="0" required>
</div>
<label class="check" for="nuevo-activo">
<input id="nuevo-activo" type="checkbox" name="activo" checked>
Mostrar en el menú
</label>
<button class="btn" type="submit">Agregar</button>
</form>
</section>
</main>
{% endblock %}"""

HISTORIAL = """{% extends "base.html" %}
{% block titulo %}Historial · Panel Ricuras{% endblock %}
{% block cuerpo %}
{% include "nav_vendedor" %}
<main id="contenido" class="contenedor pagina-panel">
<div class="panel-encabezado">
<div>
<h1>Historial</h1>
<p>Consulta lo vendido por fecha, método de pago y producto.</p>
</div>
</div>

<form method="get" class="filtro-fecha">
<div>
<label for="fecha">Fecha</label>
<input id="fecha" name="fecha" type="date" value="{{ fecha }}" required>
</div>
<button class="btn btn-sec" type="submit">Ver fecha</button>
<a class="btn" href="{{ url_for('historial_csv', fecha=fecha) }}">Descargar CSV</a>
</form>

<section class="totales" aria-label="Totales de la fecha">
<div class="total-grande">
<p>Total vendido</p>
<strong>{{ resumen["vendido"]|cop }}</strong>
<small>{{ resumen["entregados"] }} pedido(s) entregado(s) · {{ fecha|fecha_larga }}</small>
</div>
<div class="total-metodo">
<span>Efectivo</span>
<strong>{{ resumen["efectivo"]|cop }}</strong>
</div>
<div class="total-metodo">
<span>Nequi</span>
<strong>{{ resumen["nequi"]|cop }}</strong>
</div>
</section>
<p class="nota">El total vendido cuenta solo pedidos entregados. En esta fecha hay {{ resumen["cancelados"] }} cancelado(s) y {{ resumen["abiertos"] }} pedido(s) todavía abierto(s).</p>

<section class="mas-vendidos">
<h2>Productos más vendidos</h2>
{% if top %}
<ol class="top-lista">
{% for t in top %}
<li>
<span class="top-nombre">{{ t.nombre }}</span>
<span class="barra-top" aria-hidden="true"><span style="width: {{ t.porcentaje }}%"></span></span>
<strong>{{ t.unidades }}</strong>
</li>
{% endfor %}
</ol>
{% else %}
<p class="nota">Aún no hay pedidos entregados en esta fecha.</p>
{% endif %}
</section>

<section class="pedidos-fecha">
<h2>Pedidos de la fecha</h2>
{% if pedidos %}
<div class="historial-lista">
{% for p in pedidos %}
<details class="historial-item estado-{{ p.estado }}">
<summary>
<span class="hist-turno">Turno {{ p.turno }}</span>
<span class="hist-cliente">{{ p.cliente }}</span>
<span class="hist-pago">{{ pagos[p.pago] }} · {{ pago_estados[p.pago_estado] }}</span>
<span class="hist-total">{{ p.total|cop }}</span>
<span class="estado estado-{{ p.estado }}">{{ estados[p.estado] }}</span>
</summary>
<div class="hist-detalle">
<p class="nota">
{{ p.creado|hora }} · {{ p.fecha }}
{% if p.comprobante %} · Comprobante {{ p.comprobante }}{% endif %}
</p>
<ul>
{% for d in det[p.id] %}
<li><span>{{ d.cantidad }} × {{ d.nombre }}</span><strong>{{ (d.cantidad * d.precio)|cop }}</strong></li>
{% endfor %}
</ul>
</div>
</details>
{% endfor %}
</div>
{% else %}
<div class="panel-vacio">
<p>No hay pedidos registrados en esta fecha.</p>
</div>
{% endif %}
</section>

<footer class="pie"><a href="{{ url_for('panel') }}">Volver a pedidos</a></footer>
</main>
{% endblock %}"""

QR = """{% extends "base.html" %}
{% block titulo %}Código QR · Panel Ricuras{% endblock %}
{% block cuerpo %}
{% include "nav_vendedor" %}
<main id="contenido" class="contenedor pagina-panel">
<div class="panel-encabezado">
<div>
<h1>Código QR</h1>
<p>Este es el enlace que abre el menú en el celular del comprador.</p>
</div>
</div>

<div class="qr-caja">
{% if qr_ok %}
<img class="qr-imagen" src="{{ url_for('qr_svg') }}"
alt="Código QR para abrir el menú de Ricuras" width="320" height="320">
{% else %}
<div class="qr-falta" role="alert">
<p><strong>La generación de QR no está instalada.</strong></p>
<p>Instala la dependencia opcional con <code>pip install qrcode</code> y reinicia la aplicación.</p>
<p>El resto de Ricuras sigue funcionando; puedes compartir el enlace de abajo.</p>
</div>
{% endif %}

<div>
<p class="sobrelinea">Enlace público</p>
<p class="url-publica">{{ url }}</p>
{% if es_local %}
<p class="nota-error">Este enlace apunta a tu computador. Para que los celulares puedan abrirlo, define BASE_URL con la dirección de red o el dominio público y reinicia la app.</p>
{% endif %}
<p class="nota">Imprime el QR o compártelo. Si cambias BASE_URL, el código se genera de nuevo.</p>
</div>
</div>

<footer class="pie"><a href="{{ url_for('panel') }}">Volver a pedidos</a></footer>
</main>
{% endblock %}"""


app.jinja_loader = DictLoader(
    {
        "base.html": BASE,
        "nav_vendedor": NAV_VENDEDOR,
        "menu.html": MENU,
        "pedido.html": PEDIDO,
        "mis_pedidos.html": MIS_PEDIDOS,
        "login.html": LOGIN,
        "cuenta.html": CUENTA,
        "panel.html": PANEL,
        "inventario.html": INVENTARIO,
        "historial.html": HISTORIAL,
        "qr.html": QR,
        "error.html": ERROR,
    }
)

init_db()
configurar_vendedor()
if USAR_POSTGRES:
    print("Base de datos: Postgres/Supabase (DATABASE_URL).")
else:
    print("Base de datos: SQLite local (ricuras.db).")


if __name__ == "__main__":
    puerto = int(os.environ.get("PORT", "5000"))
    app.run(host="0.0.0.0", port=puerto, debug=False)
