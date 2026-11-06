CREATE TABLE "authors" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "email" TEXT NOT NULL,
  "role" TEXT NOT NULL,
  "active" BOOLEAN NOT NULL
);

CREATE TABLE "sections" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "name" TEXT NOT NULL,
  "slug" TEXT NOT NULL,
  "display_order" BIGINT NOT NULL
);

CREATE TABLE "posts" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "author_id" TEXT NOT NULL REFERENCES "authors" ("id"),
  "section_id" TEXT NOT NULL REFERENCES "sections" ("id"),
  "title" TEXT NOT NULL,
  "published_on" TEXT NOT NULL,
  "reading_minutes" BIGINT NOT NULL
);

CREATE TABLE "comments" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "post_id" TEXT NOT NULL REFERENCES "posts" ("id"),
  "display_name" TEXT NOT NULL,
  "body" TEXT NOT NULL,
  "approved" BOOLEAN NOT NULL,
  "created_on" TEXT NOT NULL
);

CREATE TABLE "revisions" (
  "id" TEXT NOT NULL PRIMARY KEY,
  "post_id" TEXT NOT NULL REFERENCES "posts" ("id"),
  "editor_id" TEXT NOT NULL REFERENCES "authors" ("id"),
  "revision_number" BIGINT NOT NULL,
  "summary" TEXT NOT NULL,
  "revised_on" TEXT NOT NULL
);
