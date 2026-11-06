CREATE TABLE "tasks" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "title" TEXT NOT NULL,
  "priority" BIGINT NOT NULL,
  "completed" BOOLEAN NOT NULL,
  "due_on" TEXT NOT NULL,
  "estimated_minutes" BIGINT NOT NULL
);
