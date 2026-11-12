-- Recursive SQL only: seeds, simulation, aggregate, and upsert stay in SQLite.
WITH RECURSIVE
  indices(i) AS (VALUES(0) UNION ALL SELECT i+1 FROM indices WHERE i+1 < :paths),
  walk(i, step, rng, value, drift, vol) AS (
    SELECT i, 0, (seed+i*747796405) & 4294967295, 1000000,
      drift % 65536, volatility % 32768 FROM indices CROSS JOIN scenarios WHERE id=:who
    UNION ALL
    SELECT i, step+1, (rng*1664525+1013904223) & 4294967295,
      (value+drift+((((rng*1664525+1013904223) & 4294967295) >> 16) % (2*vol+1))-vol) & 4294967295,
      drift, vol FROM walk WHERE step < :steps
  )
INSERT INTO results
SELECT :who, sum(value) & 4294967295, max(value), sum(value > 1000000), :paths
  FROM walk WHERE step=:steps
ON CONFLICT(id) DO UPDATE SET sum=excluded.sum, max=excluded.max,
  above=excluded.above, paths=excluded.paths
RETURNING sum, max, above, paths;
