---
title: Restore the Galerkin generator verification gate
state: ongoing
priority: high
labels: [tests, ci, galerkin]
claimed_by: codex/forseti_review_fixes
claimed_at: 2026-10-04T19:20:00Z
branch: fix/galerkin_generator_tests
---

# Restore the Galerkin generator verification gate

## Context

The generator now includes T3S and enstrophy bounds, but its tests still expect three members and the old Member constructor. CI stops before Lean verification.

## Outcome

The generator suite checks every current member, hostile bounds are still rejected, and the CI pre-build checks pass.

## Plan

Update explicit member expectations and construct hostile examples with dataclasses.replace. Run all generator tests and the Lean release build.

