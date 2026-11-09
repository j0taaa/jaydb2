CREATE TABLE "specialties" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "department" TEXT NOT NULL
);

CREATE TABLE "clinicians" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "specialty_id" TEXT NOT NULL REFERENCES "specialties" ("id"),
  "license_code" TEXT NOT NULL
);

CREATE TABLE "patients" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "birth_date" TEXT NOT NULL,
  "email" TEXT NOT NULL
);

CREATE TABLE "rooms" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "location" TEXT NOT NULL,
  "active" BOOLEAN NOT NULL
);

CREATE TABLE "diagnoses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "code" TEXT NOT NULL,
  "description" TEXT NOT NULL
);

CREATE TABLE "appointments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "patient_id" TEXT NOT NULL REFERENCES "patients" ("id"),
  "clinician_id" TEXT NOT NULL REFERENCES "clinicians" ("id"),
  "room_id" TEXT NOT NULL REFERENCES "rooms" ("id"),
  "starts_at" TEXT NOT NULL,
  "status" TEXT NOT NULL
);

CREATE TABLE "encounters" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "appointment_id" TEXT NOT NULL REFERENCES "appointments" ("id"),
  "reason" TEXT NOT NULL,
  "closed_at" TEXT NOT NULL
);

CREATE TABLE "encounter_diagnoses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "encounter_id" TEXT NOT NULL REFERENCES "encounters" ("id"),
  "diagnosis_id" TEXT NOT NULL REFERENCES "diagnoses" ("id"),
  "primary" BOOLEAN NOT NULL
);

CREATE TABLE "prescriptions" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "encounter_id" TEXT NOT NULL REFERENCES "encounters" ("id"),
  "medication" TEXT NOT NULL,
  "instructions" TEXT NOT NULL,
  "duration_days" BIGINT NOT NULL
);

CREATE TABLE "invoices" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "encounter_id" TEXT NOT NULL REFERENCES "encounters" ("id"),
  "amount_cents" BIGINT NOT NULL,
  "status" TEXT NOT NULL,
  "due_date" TEXT NOT NULL
);
