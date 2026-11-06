"""Real SQLite and PostgreSQL adapters for the database comparison suite.

Every public write returns only after its statement or explicit transaction has
committed. PostgreSQL runs in a private cluster managed by the caller; this
module never starts or changes a system service.
"""
from __future__ import annotations

from pathlib import Path
import re
import sqlite3


def quote(identifier: str) -> str:
    if not isinstance(identifier, str) or not re.fullmatch(r"[a-z_][a-z0-9_]*", identifier):
        raise ValueError(f"Invalid SQL identifier: {identifier!r}")
    return '"' + identifier + '"'


def _statements(scenario: dict, engine: str) -> list[str]:
    if engine not in ("sqlite", "postgresql"):
        raise ValueError(f"Unsupported SQL engine: {engine}")
    statements = []
    for table in scenario["tables"]:
        columns = []
        for column in table["columns"]:
            name, kind = quote(column["name"]), column["type"]
            if kind == "text":
                sql_type = "TEXT"
            elif kind == "integer":
                sql_type = "BIGINT" if engine == "postgresql" else "INTEGER"
            elif kind == "boolean":
                sql_type = "BOOLEAN" if engine == "postgresql" else "INTEGER"
            else:
                raise ValueError(f"Unsupported column type: {kind}")
            declaration = f"{name} {sql_type} NOT NULL"
            if column["name"] == "id":
                declaration += " PRIMARY KEY"
            if kind == "boolean" and engine == "sqlite":
                declaration += f" CHECK ({name} IN (0, 1))"
            if "references" in column:
                parent, parent_column = column["references"].split(".")
                declaration += f" REFERENCES {quote(parent)} ({quote(parent_column)})"
            columns.append(declaration)
        suffix = " STRICT" if engine == "sqlite" else ""
        statements.append(f"CREATE TABLE {quote(table['name'])} (\n  " + ",\n  ".join(columns) + f"\n){suffix}")
    return statements


def ddl(scenario: dict, engine: str) -> str:
    """Return executable schema DDL, including the actual reference constraints."""
    return ";\n\n".join(_statements(scenario, engine)) + ";\n"


class SQL:
    def __init__(self, engine: str, scenario: dict, folder: Path, pg_dsn: str | None):
        if engine not in ("sqlite", "postgresql"):
            raise ValueError(f"Unsupported SQL engine: {engine}")
        self.engine, self.scenario, self.folder = engine, scenario, Path(folder)
        self.folder.mkdir(parents=True, exist_ok=True)
        self.tables = {t["name"]: t for t in scenario["tables"]}
        self.placeholder = "?" if engine == "sqlite" else "%s"
        self.path = self.folder / "database.sqlite"
        self.pg_dsn = pg_dsn
        self.conn = None
        if engine == "sqlite":
            if self.path.exists():
                raise FileExistsError(f"Refusing to reuse an existing SQLite database: {self.path}")
        else:
            if not pg_dsn:
                raise ValueError("PostgreSQL requires the caller's private cluster DSN")
            import psycopg
            from psycopg.conninfo import make_conninfo

            database = "cmp_" + re.sub(r"[^a-z0-9_]", "_", scenario["id"].lower())
            if len(database.encode("utf-8")) > 63:
                raise ValueError("PostgreSQL database name would be truncated")
            with psycopg.connect(pg_dsn, autocommit=True) as admin:
                admin.execute("CREATE DATABASE " + quote(database))
            self.pg_dsn = make_conninfo(pg_dsn, dbname=database)
        self._connect()
        try:
            for statement in _statements(scenario, engine):
                self.conn.execute(statement)
        except BaseException:
            self.close()
            raise
        (self.folder / "schema.sql").write_text(ddl(scenario, engine))

    def _connect(self):
        if self.engine == "sqlite":
            self.conn = sqlite3.connect(self.path, isolation_level=None)
            self.conn.execute("PRAGMA foreign_keys=ON")
            self.conn.execute("PRAGMA journal_mode=WAL")
            self.conn.execute("PRAGMA synchronous=FULL")
        else:
            import psycopg

            self.conn = psycopg.connect(self.pg_dsn, autocommit=True, prepare_threshold=0)

    def _table(self, table: str) -> dict:
        return self.tables[table]

    def _column(self, table: str, column: str) -> dict:
        return next(c for c in self._table(table)["columns"] if c["name"] == column)

    def _normalize(self, table: str, column: str, value):
        if value is not None and self._column(table, column)["type"] == "boolean":
            return bool(value)
        return value

    def put(self, table: str, row: dict):
        columns = [c["name"] for c in self._table(table)["columns"]]
        if set(columns) != set(row):
            raise ValueError("Inserted row must contain every declared column exactly once")
        self.conn.execute(
            f"INSERT INTO {quote(table)} (" + ", ".join(map(quote, columns)) + ") VALUES ("
            + ", ".join([self.placeholder] * len(columns)) + ")",
            tuple(row[c] for c in columns),
        )
        return True

    def get(self, table: str, key: str, column: str):
        self._column(table, column)
        row = self.conn.execute(
            f"SELECT {quote(column)} FROM {quote(table)} WHERE id={self.placeholder}", (key,)
        ).fetchone()
        return None if row is None else self._normalize(table, column, row[0])

    def keys(self, table: str) -> list[str]:
        self._table(table)
        return [r[0] for r in self.conn.execute(f"SELECT id FROM {quote(table)} ORDER BY id").fetchall()]

    def update(self, table: str, key: str, column: str, value):
        self._column(table, column)
        self.conn.execute(
            f"UPDATE {quote(table)} SET {quote(column)}={self.placeholder} WHERE id={self.placeholder}",
            (value, key),
        )
        return True

    def delete(self, table: str, key: str):
        self._table(table)
        self.conn.execute(f"DELETE FROM {quote(table)} WHERE id={self.placeholder}", (key,))
        return True

    def batch(self, updates: list[tuple]):
        self.conn.execute("BEGIN")
        try:
            for table, key, column, value in updates:
                self.update(table, key, column, value)
            self.conn.execute("COMMIT")
        except BaseException:
            self.conn.execute("ROLLBACK")
            raise
        return True

    def aggregate(self, table: str, column: str) -> int:
        if self._column(table, column)["type"] != "integer":
            raise ValueError("SUM workload requires an integer column")
        return int(self.conn.execute(
            f"SELECT COALESCE(SUM({quote(column)}), 0) FROM {quote(table)}"
        ).fetchone()[0])

    def join(self, spec: dict) -> list[list]:
        child, parent = spec["from_table"], spec["to_table"]
        self._column(child, spec["fk"])
        self._column(parent, spec["column"])
        rows = self.conn.execute(
            f"SELECT c.id, p.{quote(spec['column'])} FROM {quote(child)} AS c "
            f"JOIN {quote(parent)} AS p ON c.{quote(spec['fk'])}=p.id ORDER BY c.id"
        ).fetchall()
        return [[r[0], self._normalize(parent, spec["column"], r[1])] for r in rows]

    def dump(self) -> dict[str, list[dict]]:
        result = {}
        for table, definition in self.tables.items():
            columns = [c["name"] for c in definition["columns"]]
            rows = self.conn.execute(
                "SELECT " + ", ".join(map(quote, columns)) + f" FROM {quote(table)} ORDER BY id"
            ).fetchall()
            result[table] = [
                {c: self._normalize(table, c, value) for c, value in zip(columns, row, strict=True)}
                for row in rows
            ]
        return result

    def close(self):
        if self.conn is not None:
            self.conn.close()
            self.conn = None

    def reopen(self):
        self.close()
        self._connect()

    def size_bytes(self) -> int:
        if self.engine == "sqlite":
            return sum(p.stat().st_size for p in (
                self.path, Path(str(self.path) + "-wal"), Path(str(self.path) + "-shm")
            ) if p.exists())
        return int(self.conn.execute("SELECT pg_database_size(current_database())").fetchone()[0])
