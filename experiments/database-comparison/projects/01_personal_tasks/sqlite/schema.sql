CREATE TABLE "tasks" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "title" TEXT NOT NULL,
  "priority" INTEGER NOT NULL,
  "completed" INTEGER NOT NULL CHECK ("completed" IN (0, 1)),
  "due_on" TEXT NOT NULL,
  "estimated_minutes" INTEGER NOT NULL
) STRICT;
