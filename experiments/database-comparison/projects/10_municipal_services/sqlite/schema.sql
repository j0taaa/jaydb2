CREATE TABLE "districts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "population" INTEGER NOT NULL
) STRICT;

CREATE TABLE "departments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "district_id" TEXT NOT NULL REFERENCES "districts" ("id"),
  "name" TEXT NOT NULL,
  "annual_budget_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "staff" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "department_id" TEXT NOT NULL REFERENCES "departments" ("id"),
  "full_name" TEXT NOT NULL,
  "role" TEXT NOT NULL
) STRICT;

CREATE TABLE "residents" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "district_id" TEXT NOT NULL REFERENCES "districts" ("id"),
  "full_name" TEXT NOT NULL,
  "birth_year" INTEGER NOT NULL
) STRICT;

CREATE TABLE "addresses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "district_id" TEXT NOT NULL REFERENCES "districts" ("id"),
  "street" TEXT NOT NULL,
  "number" INTEGER NOT NULL
) STRICT;

CREATE TABLE "properties" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "address_id" TEXT NOT NULL REFERENCES "addresses" ("id"),
  "owner_id" TEXT NOT NULL REFERENCES "residents" ("id"),
  "property_kind" TEXT NOT NULL,
  "assessed_value_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "service_categories" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "department_id" TEXT NOT NULL REFERENCES "departments" ("id"),
  "name" TEXT NOT NULL,
  "target_days" INTEGER NOT NULL
) STRICT;

CREATE TABLE "service_requests" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "resident_id" TEXT NOT NULL REFERENCES "residents" ("id"),
  "property_id" TEXT NOT NULL REFERENCES "properties" ("id"),
  "category_id" TEXT NOT NULL REFERENCES "service_categories" ("id"),
  "opened_date" TEXT NOT NULL,
  "status" TEXT NOT NULL
) STRICT;

CREATE TABLE "request_updates" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "request_id" TEXT NOT NULL REFERENCES "service_requests" ("id"),
  "staff_id" TEXT NOT NULL REFERENCES "staff" ("id"),
  "message" TEXT NOT NULL,
  "update_date" TEXT NOT NULL
) STRICT;

CREATE TABLE "permit_types" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "department_id" TEXT NOT NULL REFERENCES "departments" ("id"),
  "name" TEXT NOT NULL,
  "base_fee_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "permit_applications" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "property_id" TEXT NOT NULL REFERENCES "properties" ("id"),
  "resident_id" TEXT NOT NULL REFERENCES "residents" ("id"),
  "permit_type_id" TEXT NOT NULL REFERENCES "permit_types" ("id"),
  "submitted_date" TEXT NOT NULL
) STRICT;

CREATE TABLE "permits" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "application_id" TEXT NOT NULL REFERENCES "permit_applications" ("id"),
  "approved_by" TEXT NOT NULL REFERENCES "staff" ("id"),
  "issued_date" TEXT NOT NULL,
  "valid_days" INTEGER NOT NULL
) STRICT;

CREATE TABLE "inspection_types" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "department_id" TEXT NOT NULL REFERENCES "departments" ("id"),
  "name" TEXT NOT NULL,
  "checklist_items" INTEGER NOT NULL
) STRICT;

CREATE TABLE "inspections" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "property_id" TEXT NOT NULL REFERENCES "properties" ("id"),
  "inspection_type_id" TEXT NOT NULL REFERENCES "inspection_types" ("id"),
  "inspector_id" TEXT NOT NULL REFERENCES "staff" ("id"),
  "inspection_date" TEXT NOT NULL,
  "result" TEXT NOT NULL
) STRICT;

CREATE TABLE "violations" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "inspection_id" TEXT NOT NULL REFERENCES "inspections" ("id"),
  "code" TEXT NOT NULL,
  "fine_cents" INTEGER NOT NULL,
  "status" TEXT NOT NULL
) STRICT;

CREATE TABLE "vendors" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "registration" TEXT NOT NULL
) STRICT;

CREATE TABLE "contracts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "vendor_id" TEXT NOT NULL REFERENCES "vendors" ("id"),
  "department_id" TEXT NOT NULL REFERENCES "departments" ("id"),
  "description" TEXT NOT NULL,
  "ceiling_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "assets" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "department_id" TEXT NOT NULL REFERENCES "departments" ("id"),
  "address_id" TEXT NOT NULL REFERENCES "addresses" ("id"),
  "name" TEXT NOT NULL,
  "replacement_cost_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "work_orders" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "request_id" TEXT NOT NULL REFERENCES "service_requests" ("id"),
  "contract_id" TEXT NOT NULL REFERENCES "contracts" ("id"),
  "asset_id" TEXT NOT NULL REFERENCES "assets" ("id"),
  "scheduled_date" TEXT NOT NULL,
  "estimated_cost_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "work_order_assignments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "work_order_id" TEXT NOT NULL REFERENCES "work_orders" ("id"),
  "staff_id" TEXT NOT NULL REFERENCES "staff" ("id"),
  "planned_hours" INTEGER NOT NULL
) STRICT;

CREATE TABLE "material_catalog" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "unit" TEXT NOT NULL,
  "unit_cost_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "work_order_materials" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "work_order_id" TEXT NOT NULL REFERENCES "work_orders" ("id"),
  "material_id" TEXT NOT NULL REFERENCES "material_catalog" ("id"),
  "quantity" INTEGER NOT NULL
) STRICT;

CREATE TABLE "budget_accounts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "department_id" TEXT NOT NULL REFERENCES "departments" ("id"),
  "fiscal_year" INTEGER NOT NULL,
  "account_code" TEXT NOT NULL,
  "allocated_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "expenditures" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "budget_account_id" TEXT NOT NULL REFERENCES "budget_accounts" ("id"),
  "work_order_id" TEXT NOT NULL REFERENCES "work_orders" ("id"),
  "posted_date" TEXT NOT NULL,
  "amount_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "fee_invoices" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "resident_id" TEXT NOT NULL REFERENCES "residents" ("id"),
  "permit_id" TEXT NOT NULL REFERENCES "permits" ("id"),
  "issued_date" TEXT NOT NULL,
  "total_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "fee_payments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "fee_invoice_id" TEXT NOT NULL REFERENCES "fee_invoices" ("id"),
  "received_date" TEXT NOT NULL,
  "method" TEXT NOT NULL,
  "amount_cents" INTEGER NOT NULL
) STRICT;
