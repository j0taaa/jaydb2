CREATE TABLE "accounts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "kind" TEXT NOT NULL,
  "currency" TEXT NOT NULL,
  "opening_balance_cents" INTEGER NOT NULL,
  "active" INTEGER NOT NULL CHECK ("active" IN (0, 1))
) STRICT;

CREATE TABLE "categories" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "monthly_budget_cents" INTEGER NOT NULL,
  "essential" INTEGER NOT NULL CHECK ("essential" IN (0, 1))
) STRICT;

CREATE TABLE "transactions" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "account_id" TEXT NOT NULL REFERENCES "accounts" ("id"),
  "category_id" TEXT NOT NULL REFERENCES "categories" ("id"),
  "description" TEXT NOT NULL,
  "amount_cents" INTEGER NOT NULL,
  "posted_on" TEXT NOT NULL
) STRICT;
