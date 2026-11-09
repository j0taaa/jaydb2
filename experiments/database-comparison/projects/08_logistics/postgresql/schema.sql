CREATE TABLE "customers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "billing_email" TEXT NOT NULL
);

CREATE TABLE "warehouses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "city" TEXT NOT NULL,
  "capacity_pallets" BIGINT NOT NULL
);

CREATE TABLE "carriers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "service_level" TEXT NOT NULL
);

CREATE TABLE "vehicle_types" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "max_payload_kg" BIGINT NOT NULL
);

CREATE TABLE "drivers" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "full_name" TEXT NOT NULL,
  "license_class" TEXT NOT NULL
);

CREATE TABLE "vehicles" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "carrier_id" TEXT NOT NULL REFERENCES "carriers" ("id"),
  "vehicle_type_id" TEXT NOT NULL REFERENCES "vehicle_types" ("id"),
  "registration" TEXT NOT NULL,
  "payload_kg" BIGINT NOT NULL
);

CREATE TABLE "addresses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "customer_id" TEXT NOT NULL REFERENCES "customers" ("id"),
  "label" TEXT NOT NULL,
  "postal_code" TEXT NOT NULL
);

CREATE TABLE "products" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "customer_id" TEXT NOT NULL REFERENCES "customers" ("id"),
  "sku" TEXT NOT NULL,
  "unit_weight_grams" BIGINT NOT NULL
);

CREATE TABLE "inventory" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "warehouse_id" TEXT NOT NULL REFERENCES "warehouses" ("id"),
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "quantity" BIGINT NOT NULL
);

CREATE TABLE "shipments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "customer_id" TEXT NOT NULL REFERENCES "customers" ("id"),
  "origin_warehouse_id" TEXT NOT NULL REFERENCES "warehouses" ("id"),
  "destination_address_id" TEXT NOT NULL REFERENCES "addresses" ("id"),
  "carrier_id" TEXT NOT NULL REFERENCES "carriers" ("id"),
  "service" TEXT NOT NULL
);

CREATE TABLE "shipment_items" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "shipment_id" TEXT NOT NULL REFERENCES "shipments" ("id"),
  "product_id" TEXT NOT NULL REFERENCES "products" ("id"),
  "quantity" BIGINT NOT NULL
);

CREATE TABLE "routes" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "carrier_id" TEXT NOT NULL REFERENCES "carriers" ("id"),
  "origin_warehouse_id" TEXT NOT NULL REFERENCES "warehouses" ("id"),
  "destination_warehouse_id" TEXT NOT NULL REFERENCES "warehouses" ("id"),
  "distance_km" BIGINT NOT NULL
);

CREATE TABLE "trips" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "route_id" TEXT NOT NULL REFERENCES "routes" ("id"),
  "vehicle_id" TEXT NOT NULL REFERENCES "vehicles" ("id"),
  "driver_id" TEXT NOT NULL REFERENCES "drivers" ("id"),
  "departure_date" TEXT NOT NULL
);

CREATE TABLE "shipment_legs" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "shipment_id" TEXT NOT NULL REFERENCES "shipments" ("id"),
  "trip_id" TEXT NOT NULL REFERENCES "trips" ("id"),
  "sequence" BIGINT NOT NULL
);

CREATE TABLE "tracking_events" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "shipment_id" TEXT NOT NULL REFERENCES "shipments" ("id"),
  "status" TEXT NOT NULL,
  "occurred_at" TEXT NOT NULL
);

CREATE TABLE "delivery_attempts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "shipment_id" TEXT NOT NULL REFERENCES "shipments" ("id"),
  "driver_id" TEXT NOT NULL REFERENCES "drivers" ("id"),
  "attempt_date" TEXT NOT NULL,
  "successful" BOOLEAN NOT NULL
);

CREATE TABLE "invoices" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "customer_id" TEXT NOT NULL REFERENCES "customers" ("id"),
  "issued_date" TEXT NOT NULL,
  "total_cents" BIGINT NOT NULL
);

CREATE TABLE "invoice_lines" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "invoice_id" TEXT NOT NULL REFERENCES "invoices" ("id"),
  "shipment_id" TEXT NOT NULL REFERENCES "shipments" ("id"),
  "charge_cents" BIGINT NOT NULL
);
