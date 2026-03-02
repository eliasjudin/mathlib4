# AGENTS.md

## Cursor Cloud specific instructions

This is **mathlib4**, the community mathematical library for Lean 4. It is a single-package Lean library (not a web app or microservice), built with the **Lake** build system.

### Toolchain

- **elan** manages the Lean toolchain version (reads `lean-toolchain`).
- The update script installs elan and runs `lake exe cache get` to fetch pre-built `.olean` files.
- Without the cache, a full build takes many hours. Always run `lake exe cache get` after pulling.

### Key commands

| Task | Command |
|---|---|
| Download cached build artifacts | `lake exe cache get` |
| Build all of Mathlib | `lake build` |
| Build a specific module | `lake build Mathlib.Algebra.Group.Defs` |
| Run all tests | `lake test` |
| Build a single test file | `lake build MathlibTest.<name>` |
| Style lint (text-based) | `lake exe lint-style` |
| Check import files are up to date | `lake exe mk_all --check` |

### Caveats

- `lake test` runs **all** ~252 test files and can take a long time. To verify a specific area, build individual test files with `lake build MathlibTest.<name>`.
- `lake exe cache get` downloads from Azure blob storage. If it fails, retry or set `MATHLIB_CACHE_USE_CLOUDFLARE=1` to use the Cloudflare mirror.
- If builds behave unexpectedly after dependency changes, try `lake clean` or `rm -rf .lake` then re-run `lake exe cache get`.
- The `.pre-commit-config.yaml` only checks trailing whitespace and end-of-file fixers; these are lightweight.
- Lake executables like `lint-style`, `mk_all`, `cache`, and `autolabel` are built on first use and cached.
