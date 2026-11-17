"""Copia los datos de ricuras.db (SQLite) a Supabase / Postgres.

Antes de ejecutarlo:
  1. Crea el proyecto en https://supabase.com
  2. Copia la cadena "Session pooler" en DATABASE_URL dentro de .env
  3. Ejecuta:  .venv\\Scripts\\python.exe migrar_a_supabase.py

El script no borra nada sin permiso. Si la base de Supabase ya tiene datos,
se detiene y te pide usar --reemplazar (eso sí vacía las tablas de la app).
"""

from __future__ import annotations

import os
import sqlite3
import sys

try:
    from dotenv import load_dotenv
except ImportError:
    load_dotenv = None

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
if load_dotenv is not None:
    load_dotenv(os.path.join(BASE_DIR, ".env"))

DB_PATH = os.path.join(BASE_DIR, "ricuras.db")
DATABASE_URL = os.environ.get("DATABASE_URL", "").strip()

ESQUEMA = (
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

TABLAS = ("detalle", "pedidos", "items", "ajustes", "vendedores")


def main():
    if not DATABASE_URL:
        print("ERROR: falta DATABASE_URL en el archivo .env")
        print("Copia la cadena 'Session pooler' de Supabase y pégala ahí.")
        return 1
    if not os.path.exists(DB_PATH):
        print(f"ERROR: no encontré {DB_PATH}")
        return 1

    try:
        import psycopg
    except ImportError:
        print("ERROR: falta psycopg. Ejecuta:")
        print('  .venv\\Scripts\\python.exe -m pip install "psycopg[binary]"')
        return 1

    reemplazar = "--reemplazar" in sys.argv

    origen = sqlite3.connect(DB_PATH)
    origen.row_factory = sqlite3.Row
    items = origen.execute("SELECT * FROM items ORDER BY id").fetchall()
    pedidos = origen.execute("SELECT * FROM pedidos ORDER BY id").fetchall()
    detalle = origen.execute("SELECT * FROM detalle ORDER BY rowid").fetchall()
    ajustes = origen.execute("SELECT * FROM ajustes").fetchall()
    vendedores = origen.execute("SELECT * FROM vendedores ORDER BY id").fetchall()
    origen.close()

    print(
        f"Origen: {len(items)} productos, {len(pedidos)} pedidos, "
        f"{len(detalle)} líneas, {len(vendedores)} vendedores, "
        f"{len(ajustes)} ajustes."
    )

    with psycopg.connect(DATABASE_URL) as destino:
        with destino.cursor() as cur:
            for sentencia in ESQUEMA:
                cur.execute(sentencia)

            cur.execute("SELECT COUNT(*) FROM pedidos")
            hay_pedidos = cur.fetchone()[0] > 0
            cur.execute("SELECT COUNT(*) FROM items")
            hay_items = cur.fetchone()[0] > 0
            if (hay_pedidos or hay_items) and not reemplazar:
                print("\nLa base de Supabase ya tiene datos.")
                print("Si quieres reemplazarlos por los de ricuras.db, ejecuta:")
                print("  .venv\\Scripts\\python.exe migrar_a_supabase.py --reemplazar")
                return 2
            if reemplazar:
                print("Vaciando tablas de Supabase (--reemplazar)...")
                cur.execute(
                    "TRUNCATE " + ", ".join(TABLAS) + " RESTART IDENTITY CASCADE"
                )

            cur.executemany(
                "INSERT INTO items(id, nombre, precio, stock, activo) "
                "VALUES(%s, %s, %s, %s, %s) ON CONFLICT (id) DO NOTHING",
                [
                    (f["id"], f["nombre"], f["precio"], f["stock"], f["activo"])
                    for f in items
                ],
            )
            cur.executemany(
                "INSERT INTO pedidos(id, turno, fecha, cliente, estado, total, "
                "creado, pago, pago_estado, comprobante, nequi_numero, actualizado) "
                "VALUES(%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s) "
                "ON CONFLICT (id) DO NOTHING",
                [
                    (
                        f["id"], f["turno"], f["fecha"], f["cliente"], f["estado"],
                        f["total"], f["creado"], f["pago"], f["pago_estado"],
                        f["comprobante"], f["nequi_numero"], f["actualizado"],
                    )
                    for f in pedidos
                ],
            )
            cur.executemany(
                "INSERT INTO detalle(pedido_id, item_id, nombre, cantidad, precio) "
                "VALUES(%s, %s, %s, %s, %s)",
                [
                    (f["pedido_id"], f["item_id"], f["nombre"], f["cantidad"], f["precio"])
                    for f in detalle
                ],
            )
            cur.executemany(
                "INSERT INTO ajustes(clave, valor) VALUES(%s, %s) "
                "ON CONFLICT (clave) DO UPDATE SET valor=excluded.valor",
                [(f["clave"], f["valor"]) for f in ajustes],
            )
            cur.executemany(
                "INSERT INTO vendedores(id, usuario, clave_hash, activo, "
                "clave_inicial, creado) VALUES(%s, %s, %s, %s, %s, %s) "
                "ON CONFLICT (id) DO NOTHING",
                [
                    (
                        f["id"], f["usuario"], f["clave_hash"], f["activo"],
                        f["clave_inicial"], f["creado"],
                    )
                    for f in vendedores
                ],
            )

            for tabla in ("items", "pedidos", "detalle", "vendedores"):
                cur.execute(
                    f"SELECT setval(pg_get_serial_sequence('{tabla}', 'id'), "
                    f"COALESCE((SELECT MAX(id) FROM {tabla}), 1), "
                    f"(SELECT COUNT(*) FROM {tabla}) > 0)"
                )

        destino.commit()

        with destino.cursor() as cur:
            print("\nResultado en Supabase:")
            for tabla in TABLAS:
                cur.execute(f"SELECT COUNT(*) FROM {tabla}")
                print(f"  {tabla}: {cur.fetchone()[0]} filas")

    print("\nMigración terminada. Reinicia ricuras.py y prueba el panel.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
