CREATE TABLE "properties" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "city" TEXT NOT NULL,
  "timezone" TEXT NOT NULL
) STRICT;

CREATE TABLE "room_types" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "property_id" TEXT NOT NULL REFERENCES "properties" ("id"),
  "name" TEXT NOT NULL,
  "base_nightly_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "rooms" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "room_type_id" TEXT NOT NULL REFERENCES "room_types" ("id"),
  "room_number" TEXT NOT NULL,
  "floor" INTEGER NOT NULL
) STRICT;

CREATE TABLE "guests" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "full_name" TEXT NOT NULL,
  "email" TEXT NOT NULL,
  "loyalty_tier" TEXT NOT NULL
) STRICT;

CREATE TABLE "departments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "property_id" TEXT NOT NULL REFERENCES "properties" ("id"),
  "name" TEXT NOT NULL,
  "monthly_budget_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "employees" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "department_id" TEXT NOT NULL REFERENCES "departments" ("id"),
  "full_name" TEXT NOT NULL,
  "hourly_rate_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "rate_plans" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "room_type_id" TEXT NOT NULL REFERENCES "room_types" ("id"),
  "name" TEXT NOT NULL,
  "nightly_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "reservations" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "guest_id" TEXT NOT NULL REFERENCES "guests" ("id"),
  "room_id" TEXT NOT NULL REFERENCES "rooms" ("id"),
  "check_in" TEXT NOT NULL,
  "nights" INTEGER NOT NULL
) STRICT;

CREATE TABLE "reservation_rates" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "reservation_id" TEXT NOT NULL REFERENCES "reservations" ("id"),
  "rate_plan_id" TEXT NOT NULL REFERENCES "rate_plans" ("id"),
  "nightly_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "payments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "reservation_id" TEXT NOT NULL REFERENCES "reservations" ("id"),
  "method" TEXT NOT NULL,
  "amount_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "amenities" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "property_id" TEXT NOT NULL REFERENCES "properties" ("id"),
  "name" TEXT NOT NULL,
  "unit_price_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "reservation_amenities" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "reservation_id" TEXT NOT NULL REFERENCES "reservations" ("id"),
  "amenity_id" TEXT NOT NULL REFERENCES "amenities" ("id"),
  "quantity" INTEGER NOT NULL
) STRICT;

CREATE TABLE "housekeeping_tasks" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "room_id" TEXT NOT NULL REFERENCES "rooms" ("id"),
  "employee_id" TEXT NOT NULL REFERENCES "employees" ("id"),
  "service_date" TEXT NOT NULL,
  "planned_minutes" INTEGER NOT NULL
) STRICT;

CREATE TABLE "maintenance_requests" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "room_id" TEXT NOT NULL REFERENCES "rooms" ("id"),
  "reported_by" TEXT NOT NULL REFERENCES "employees" ("id"),
  "description" TEXT NOT NULL,
  "estimated_cost_cents" INTEGER NOT NULL
) STRICT;

CREATE TABLE "reviews" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "reservation_id" TEXT NOT NULL REFERENCES "reservations" ("id"),
  "rating" INTEGER NOT NULL,
  "comment" TEXT NOT NULL
) STRICT;
