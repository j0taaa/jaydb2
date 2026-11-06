CREATE TABLE "authors" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "email" TEXT NOT NULL,
  "role" TEXT NOT NULL,
  "active" INTEGER NOT NULL CHECK ("active" IN (0, 1))
) STRICT;

CREATE TABLE "sections" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "slug" TEXT NOT NULL,
  "display_order" INTEGER NOT NULL
) STRICT;

CREATE TABLE "posts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "author_id" TEXT NOT NULL REFERENCES "authors" ("id"),
  "section_id" TEXT NOT NULL REFERENCES "sections" ("id"),
  "title" TEXT NOT NULL,
  "published_on" TEXT NOT NULL,
  "reading_minutes" INTEGER NOT NULL
) STRICT;

CREATE TABLE "comments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "post_id" TEXT NOT NULL REFERENCES "posts" ("id"),
  "display_name" TEXT NOT NULL,
  "body" TEXT NOT NULL,
  "approved" INTEGER NOT NULL CHECK ("approved" IN (0, 1)),
  "created_on" TEXT NOT NULL
) STRICT;

CREATE TABLE "revisions" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "post_id" TEXT NOT NULL REFERENCES "posts" ("id"),
  "editor_id" TEXT NOT NULL REFERENCES "authors" ("id"),
  "revision_number" INTEGER NOT NULL,
  "summary" TEXT NOT NULL,
  "revised_on" TEXT NOT NULL
) STRICT;
