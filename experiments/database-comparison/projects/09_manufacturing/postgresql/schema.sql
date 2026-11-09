CREATE TABLE "plants" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "city" TEXT NOT NULL
);

CREATE TABLE "units_of_measure" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "code" TEXT NOT NULL,
  "description" TEXT NOT NULL
);

CREATE TABLE "suppliers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "lead_days" BIGINT NOT NULL
);

CREATE TABLE "customers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "credit_limit_cents" BIGINT NOT NULL
);

CREATE TABLE "employees" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "plant_id" TEXT NOT NULL REFERENCES "plants" ("id"),
  "full_name" TEXT NOT NULL,
  "role" TEXT NOT NULL
);

CREATE TABLE "work_centers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "plant_id" TEXT NOT NULL REFERENCES "plants" ("id"),
  "name" TEXT NOT NULL,
  "hourly_cost_cents" BIGINT NOT NULL
);

CREATE TABLE "materials" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "unit_id" TEXT NOT NULL REFERENCES "units_of_measure" ("id"),
  "sku" TEXT NOT NULL,
  "reorder_quantity" BIGINT NOT NULL
);

CREATE TABLE "supplier_materials" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "supplier_id" TEXT NOT NULL REFERENCES "suppliers" ("id"),
  "material_id" TEXT NOT NULL REFERENCES "materials" ("id"),
  "unit_cost_cents" BIGINT NOT NULL
);

CREATE TABLE "products" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "unit_id" TEXT NOT NULL REFERENCES "units_of_measure" ("id"),
  "sku" TEXT NOT NULL,
  "list_price_cents" BIGINT NOT NULL
);

CREATE TABLE "bills_of_material" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "revision" TEXT NOT NULL,
  "active" BOOLEAN NOT NULL
);

CREATE TABLE "bom_components" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "bill_id" TEXT NOT NULL REFERENCES "bills_of_material" ("id"),
  "material_id" TEXT NOT NULL REFERENCES "materials" ("id"),
  "quantity" BIGINT NOT NULL
);

CREATE TABLE "warehouses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "plant_id" TEXT NOT NULL REFERENCES "plants" ("id"),
  "name" TEXT NOT NULL
);

CREATE TABLE "stock_lots" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "warehouse_id" TEXT NOT NULL REFERENCES "warehouses" ("id"),
  "material_id" TEXT NOT NULL REFERENCES "materials" ("id"),
  "supplier_id" TEXT NOT NULL REFERENCES "suppliers" ("id"),
  "quantity" BIGINT NOT NULL
);

CREATE TABLE "machines" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "work_center_id" TEXT NOT NULL REFERENCES "work_centers" ("id"),
  "asset_tag" TEXT NOT NULL,
  "service_interval_hours" BIGINT NOT NULL
);

CREATE TABLE "work_orders" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "work_center_id" TEXT NOT NULL REFERENCES "work_centers" ("id"),
  "planned_quantity" BIGINT NOT NULL,
  "due_date" TEXT NOT NULL
);

CREATE TABLE "operations" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "work_order_id" TEXT NOT NULL REFERENCES "work_orders" ("id"),
  "machine_id" TEXT NOT NULL REFERENCES "machines" ("id"),
  "sequence" BIGINT NOT NULL,
  "planned_minutes" BIGINT NOT NULL
);

CREATE TABLE "production_runs" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "operation_id" TEXT NOT NULL REFERENCES "operations" ("id"),
  "employee_id" TEXT NOT NULL REFERENCES "employees" ("id"),
  "completed_quantity" BIGINT NOT NULL,
  "scrap_quantity" BIGINT NOT NULL
);

CREATE TABLE "quality_checks" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "production_run_id" TEXT NOT NULL REFERENCES "production_runs" ("id"),
  "inspector_id" TEXT NOT NULL REFERENCES "employees" ("id"),
  "result" TEXT NOT NULL,
  "defect_count" BIGINT NOT NULL
);

CREATE TABLE "purchase_orders" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "supplier_id" TEXT NOT NULL REFERENCES "suppliers" ("id"),
  "warehouse_id" TEXT NOT NULL REFERENCES "warehouses" ("id"),
  "ordered_date" TEXT NOT NULL,
  "total_cents" BIGINT NOT NULL
);

CREATE TABLE "purchase_order_lines" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "purchase_order_id" TEXT NOT NULL REFERENCES "purchase_orders" ("id"),
  "material_id" TEXT NOT NULL REFERENCES "materials" ("id"),
  "quantity" BIGINT NOT NULL,
  "unit_cost_cents" BIGINT NOT NULL
);

CREATE TABLE "sales_orders" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "customer_id" TEXT NOT NULL REFERENCES "customers" ("id"),
  "ordered_date" TEXT NOT NULL,
  "total_cents" BIGINT NOT NULL,
  "status" TEXT NOT NULL
);

CREATE TABLE "sales_order_lines" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "sales_order_id" TEXT NOT NULL REFERENCES "sales_orders" ("id"),
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "quantity" BIGINT NOT NULL,
  "unit_price_cents" BIGINT NOT NULL
);
