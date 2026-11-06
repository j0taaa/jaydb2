CREATE TABLE "organizations" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "country_code" TEXT NOT NULL
);

CREATE TABLE "learners" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "email" TEXT NOT NULL,
  "organization_id" TEXT NOT NULL REFERENCES "organizations" ("id")
);

CREATE TABLE "instructors" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "organization_id" TEXT NOT NULL REFERENCES "organizations" ("id"),
  "expertise" TEXT NOT NULL
);

CREATE TABLE "courses" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "title" TEXT NOT NULL,
  "instructor_id" TEXT NOT NULL REFERENCES "instructors" ("id"),
  "fee_cents" BIGINT NOT NULL,
  "currency" TEXT NOT NULL
);

CREATE TABLE "modules" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "course_id" TEXT NOT NULL REFERENCES "courses" ("id"),
  "title" TEXT NOT NULL,
  "position" BIGINT NOT NULL
);

CREATE TABLE "lessons" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "module_id" TEXT NOT NULL REFERENCES "modules" ("id"),
  "title" TEXT NOT NULL,
  "duration_minutes" BIGINT NOT NULL
);

CREATE TABLE "cohorts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "course_id" TEXT NOT NULL REFERENCES "courses" ("id"),
  "name" TEXT NOT NULL,
  "starts_on" TEXT NOT NULL,
  "capacity" BIGINT NOT NULL
);

CREATE TABLE "enrollments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "learner_id" TEXT NOT NULL REFERENCES "learners" ("id"),
  "cohort_id" TEXT NOT NULL REFERENCES "cohorts" ("id"),
  "enrolled_on" TEXT NOT NULL,
  "status" TEXT NOT NULL
);

CREATE TABLE "assignments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "lesson_id" TEXT NOT NULL REFERENCES "lessons" ("id"),
  "title" TEXT NOT NULL,
  "max_score" BIGINT NOT NULL,
  "due_on" TEXT NOT NULL
);

CREATE TABLE "submissions" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "assignment_id" TEXT NOT NULL REFERENCES "assignments" ("id"),
  "enrollment_id" TEXT NOT NULL REFERENCES "enrollments" ("id"),
  "submitted_at" TEXT NOT NULL,
  "artifact_name" TEXT NOT NULL
);

CREATE TABLE "grades" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "submission_id" TEXT NOT NULL REFERENCES "submissions" ("id"),
  "reviewer_id" TEXT NOT NULL REFERENCES "instructors" ("id"),
  "score" BIGINT NOT NULL,
  "feedback" TEXT NOT NULL
);

CREATE TABLE "payments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "enrollment_id" TEXT NOT NULL REFERENCES "enrollments" ("id"),
  "amount_cents" BIGINT NOT NULL,
  "currency" TEXT NOT NULL,
  "status" TEXT NOT NULL
);
