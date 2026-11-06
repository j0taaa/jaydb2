CREATE TABLE "customers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "email" TEXT NOT NULL,
  "country_code" TEXT NOT NULL
);

CREATE TABLE "categories" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "department" TEXT NOT NULL
);

CREATE TABLE "products" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "category_id" TEXT NOT NULL REFERENCES "categories" ("id"),
  "name" TEXT NOT NULL,
  "price_cents" BIGINT NOT NULL,
  "active" BOOLEAN NOT NULL
);

CREATE TABLE "warehouses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "city" TEXT NOT NULL,
  "active" BOOLEAN NOT NULL
);

CREATE TABLE "inventory" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "warehouse_id" TEXT NOT NULL REFERENCES "warehouses" ("id"),
  "quantity" BIGINT NOT NULL,
  "reorder_level" BIGINT NOT NULL
);

CREATE TABLE "orders" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "customer_id" TEXT NOT NULL REFERENCES "customers" ("id"),
  "status" TEXT NOT NULL,
  "ordered_at" TEXT NOT NULL,
  "total_cents" BIGINT NOT NULL
);

CREATE TABLE "order_items" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "order_id" TEXT NOT NULL REFERENCES "orders" ("id"),
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "quantity" BIGINT NOT NULL,
  "unit_price_cents" BIGINT NOT NULL
);

CREATE TABLE "payments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "order_id" TEXT NOT NULL REFERENCES "orders" ("id"),
  "method" TEXT NOT NULL,
  "amount_cents" BIGINT NOT NULL,
  "status" TEXT NOT NULL
);
