#!/bin/sh
# Immutable launch fixture: report the effective runtime environment and argv.
printf '%s\n' "$BENDRTS"
printf '%s\n' "$@"
