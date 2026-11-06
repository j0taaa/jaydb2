CREATE TABLE "organizations" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "country_code" TEXT NOT NULL
) STRICT;

CREATE TABLE "learners" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "email" TEXT NOT NULL,
  "organization_id" TEXT NOT NULL REFERENCES "organizations" ("id")
) STRICT;

CREATE TABLE "instructors" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "organization_id" TEXT NOT NULL REFERENCES "organizations" ("id"),
  "expertise" TEXT NOT NULL
) STRICT;

CREATE TABLE "courses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "title" TEXT NOT NULL,
  "instructor_id" TEXT NOT NULL REFERENCES "instructors" ("id"),
  "fee_cents" INTEGER NOT NULL,
  "currency" TEXT NOT NULL
) STRICT;

CREATE TABLE "modules" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "course_id" TEXT NOT NULL REFERENCES "courses" ("id"),
  "title" TEXT NOT NULL,
  "position" INTEGER NOT NULL
) STRICT;

CREATE TABLE "lessons" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "module_id" TEXT NOT NULL REFERENCES "modules" ("id"),
  "title" TEXT NOT NULL,
  "duration_minutes" INTEGER NOT NULL
) STRICT;

CREATE TABLE "cohorts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "course_id" TEXT NOT NULL REFERENCES "courses" ("id"),
  "name" TEXT NOT NULL,
  "starts_on" TEXT NOT NULL,
  "capacity" INTEGER NOT NULL
) STRICT;

CREATE TABLE "enrollments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "learner_id" TEXT NOT NULL REFERENCES "learners" ("id"),
  "cohort_id" TEXT NOT NULL REFERENCES "cohorts" ("id"),
  "enrolled_on" TEXT NOT NULL,
  "status" TEXT NOT NULL
) STRICT;

CREATE TABLE "assignments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "lesson_id" TEXT NOT NULL REFERENCES "lessons" ("id"),
  "title" TEXT NOT NULL,
  "max_score" INTEGER NOT NULL,
  "due_on" TEXT NOT NULL
) STRICT;

CREATE TABLE "submissions" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "assignment_id" TEXT NOT NULL REFERENCES "assignments" ("id"),
  "enrollment_id" TEXT NOT NULL REFERENCES "enrollments" ("id"),
  "submitted_at" TEXT NOT NULL,
  "artifact_name" TEXT NOT NULL
) STRICT;

CREATE TABLE "grades" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "submission_id" TEXT NOT NULL REFERENCES "submissions" ("id"),
  "reviewer_id" TEXT NOT NULL REFERENCES "instructors" ("id"),
  "score" INTEGER NOT NULL,
  "feedback" TEXT NOT NULL
) STRICT;

CREATE TABLE "payments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "enrollment_id" TEXT NOT NULL REFERENCES "enrollments" ("id"),
  "amount_cents" INTEGER NOT NULL,
  "currency" TEXT NOT NULL,
  "status" TEXT NOT NULL
) STRICT;
