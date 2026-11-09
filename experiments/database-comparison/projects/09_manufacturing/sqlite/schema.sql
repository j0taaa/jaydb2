CREATE TABLE "plants" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "city" TEXT NOT NULL
) STRICT;

CREATE TABLE "units_of_measure" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "code" TEXT NOT NULL,
  "description" TEXT NOT NULL
) STRICT;

CREATE TABLE "suppliers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "lead_days" INTEGER NOT NULL
) STRICT;

CREATE TABLE "customers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "credit_limit_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "employees" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "plant_id" TEXT NOT NULL REFERENCES "plants" ("id"),
  "full_name" TEXT NOT NULL,
  "role" TEXT NOT NULL
) STRICT;

CREATE TABLE "work_centers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "plant_id" TEXT NOT NULL REFERENCES "plants" ("id"),
  "name" TEXT NOT NULL,
  "hourly_cost_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "materials" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "unit_id" TEXT NOT NULL REFERENCES "units_of_measure" ("id"),
  "sku" TEXT NOT NULL,
  "reorder_quantity" INTEGER NOT NULL
) STRICT;

CREATE TABLE "supplier_materials" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "supplier_id" TEXT NOT NULL REFERENCES "suppliers" ("id"),
  "material_id" TEXT NOT NULL REFERENCES "materials" ("id"),
  "unit_cost_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "products" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "unit_id" TEXT NOT NULL REFERENCES "units_of_measure" ("id"),
  "sku" TEXT NOT NULL,
  "list_price_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "bills_of_material" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "revision" TEXT NOT NULL,
  "active" INTEGER NOT NULL CHECK ("active" IN (0, 1))
) STRICT;

CREATE TABLE "bom_components" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "bill_id" TEXT NOT NULL REFERENCES "bills_of_material" ("id"),
  "material_id" TEXT NOT NULL REFERENCES "materials" ("id"),
  "quantity" INTEGER NOT NULL
) STRICT;

CREATE TABLE "warehouses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "plant_id" TEXT NOT NULL REFERENCES "plants" ("id"),
  "name" TEXT NOT NULL
) STRICT;

CREATE TABLE "stock_lots" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "warehouse_id" TEXT NOT NULL REFERENCES "warehouses" ("id"),
  "material_id" TEXT NOT NULL REFERENCES "materials" ("id"),
  "supplier_id" TEXT NOT NULL REFERENCES "suppliers" ("id"),
  "quantity" INTEGER NOT NULL
) STRICT;

CREATE TABLE "machines" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "work_center_id" TEXT NOT NULL REFERENCES "work_centers" ("id"),
  "asset_tag" TEXT NOT NULL,
  "service_interval_hours" INTEGER NOT NULL
) STRICT;

CREATE TABLE "work_orders" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "work_center_id" TEXT NOT NULL REFERENCES "work_centers" ("id"),
  "planned_quantity" INTEGER NOT NULL,
  "due_date" TEXT NOT NULL
) STRICT;

CREATE TABLE "operations" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "work_order_id" TEXT NOT NULL REFERENCES "work_orders" ("id"),
  "machine_id" TEXT NOT NULL REFERENCES "machines" ("id"),
  "sequence" INTEGER NOT NULL,
  "planned_minutes" INTEGER NOT NULL
) STRICT;

CREATE TABLE "production_runs" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "operation_id" TEXT NOT NULL REFERENCES "operations" ("id"),
  "employee_id" TEXT NOT NULL REFERENCES "employees" ("id"),
  "completed_quantity" INTEGER NOT NULL,
  "scrap_quantity" INTEGER NOT NULL
) STRICT;

CREATE TABLE "quality_checks" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "production_run_id" TEXT NOT NULL REFERENCES "production_runs" ("id"),
  "inspector_id" TEXT NOT NULL REFERENCES "employees" ("id"),
  "result" TEXT NOT NULL,
  "defect_count" INTEGER NOT NULL
) STRICT;

CREATE TABLE "purchase_orders" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "supplier_id" TEXT NOT NULL REFERENCES "suppliers" ("id"),
  "warehouse_id" TEXT NOT NULL REFERENCES "warehouses" ("id"),
  "ordered_date" TEXT NOT NULL,
  "total_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "purchase_order_lines" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "purchase_order_id" TEXT NOT NULL REFERENCES "purchase_orders" ("id"),
  "material_id" TEXT NOT NULL REFERENCES "materials" ("id"),
  "quantity" INTEGER NOT NULL,
  "unit_cost_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "sales_orders" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "customer_id" TEXT NOT NULL REFERENCES "customers" ("id"),
  "ordered_date" TEXT NOT NULL,
  "total_cents" INTEGER NOT NULL,
  "status" TEXT NOT NULL
) STRICT;

CREATE TABLE "sales_order_lines" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "sales_order_id" TEXT NOT NULL REFERENCES "sales_orders" ("id"),
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "quantity" INTEGER NOT NULL,
  "unit_price_cents" INTEGER NOT NULL
) STRICT;
