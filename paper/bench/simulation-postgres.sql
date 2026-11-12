-- All loops, parameter reads and writes execute inside PostgreSQL, no UDF host.
CREATE FUNCTION simulate(who text, depth integer, steps integer)
RETURNS TABLE(sum bigint, max bigint, above bigint, paths bigint)
LANGUAGE plpgsql AS $$
DECLARE
  seed bigint; drift bigint; vol bigint; rng bigint; value bigint;
  total bigint := 0; largest bigint := 0; hits bigint := 0;
  count integer := 1 << depth;
BEGIN
  SELECT s.seed, s.drift % 65536, s.volatility % 32768 INTO STRICT seed, drift, vol
    FROM scenarios s WHERE s.id = who;
  FOR i IN 0..count-1 LOOP
    rng := (seed + i::bigint * 747796405) & 4294967295;
    value := 1000000;
    FOR j IN 1..steps LOOP
      rng := (rng * 1664525 + 1013904223) & 4294967295;
      value := (value + drift + ((rng >> 16) % (2 * vol + 1)) - vol) & 4294967295;
    END LOOP;
    total := (total + value) & 4294967295;
    largest := greatest(largest, value);
    hits := hits + (value > 1000000)::integer;
  END LOOP;
  RETURN QUERY INSERT INTO results AS r VALUES(who, total, largest, hits, count)
    ON CONFLICT(id) DO UPDATE SET sum=excluded.sum, max=excluded.max,
      above=excluded.above, paths=excluded.paths
    RETURNING r.sum, r.max, r.above, r.paths;
END $$;
