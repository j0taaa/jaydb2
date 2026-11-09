CREATE TABLE "accounts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "kind" TEXT NOT NULL,
  "currency" TEXT NOT NULL,
  "opening_balance_cents" BIGINT NOT NULL,
  "active" BOOLEAN NOT NULL
);

CREATE TABLE "categories" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "monthly_budget_cents" BIGINT NOT NULL,
  "essential" BOOLEAN NOT NULL
);

CREATE TABLE "transactions" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "account_id" TEXT NOT NULL REFERENCES "accounts" ("id"),
  "category_id" TEXT NOT NULL REFERENCES "categories" ("id"),
  "description" TEXT NOT NULL,
  "amount_cents" BIGINT NOT NULL,
  "posted_on" TEXT NOT NULL
);
