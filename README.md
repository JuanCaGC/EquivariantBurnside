# EquivariantBurnside (working name)

A Julia package, to be used together with [OSCAR](https://www.oscar-system.org), for computing equivariant Burnside invariants of finite group actions.

Status: early development. Phase 0 is done: the working code of `legacy/` has been reorganized into a package under `src/`, with tests and scripts, without changing its mathematics or its numerical output.

## Install and run

From a local checkout, run `julia --project=.` and enter:

```julia
using Pkg
Pkg.instantiate()
using EquivariantBurnside, Oscar
bc(symmetric_group(4), 2)
# BC_2(G) = (Z/2)^3
```

The validated environment is Julia 1.12.4, OSCAR 1.8.2 and GAP 4.16.1. The declared compatibility is Julia 1.10 and later with OSCAR 1.8, but only 1.12.4 has been tested.

Run the tests with `Pkg.test()` in the Julia session. The original command line checks are reproduced by `julia --project=. scripts/validate.jl all`. Other entry points are `scripts/bcclass_tests.jl`, `scripts/ex75.jl`, `scripts/dcp_tests.jl`, `scripts/validate_tomlib.jl` and `scripts/gl_verify.jl`. The script `scripts/compare_with_legacy.jl` runs four of them and compares the normalized output with the stored outputs in `legacy/bc/`.

## What it computes today

- The groups B_n(H) for finite abelian H and the combinatorial Burnside groups BC_n(G) of Tschinkel, Yang and Zhang (arXiv:2112.12801), with explicit quotient maps.
- `bc` computes BC_n(G) by Theorem 5.2. `bc_direct` keeps the independent computation from the definition. `bc_structure_tom(n)` builds the structure for S_n from Table of Marks data. `certify_snf` returns exact Smith normal form certificates.
- The image in BC_n(G) of a class given as a sum of symbols, through `prepare!`, `symbol_image`, `class_coords`, `class_is_zero` and `class_order`.
- Arrangement and chain calculations under `EquivariantBurnside.DCP`.

## Scope

Inputs are finite groups given as OSCAR groups or raw GAP groups. Individual functions keep the input requirements of the frozen code, in particular symbol evaluation uses raw GAP groups.

Not implemented yet: the class of an action on a projective space or a toric variety, the Kresch-Tschinkel recursion (arXiv:2108.00518), and anything for general varieties. The function field part of a symbol is not recorded or computed.

## Legacy snapshot

`legacy/bc/` is a copy of the working code of the repository `combinatorial-burnside-groups` at the time of the reorganization. It is frozen and read-only, and it is the reference for the regression tests:

    cd legacy/bc
    julia --project=. validate.jl all          # 88 checks, about 26 seconds
    julia --project=. proj/bcclass_tests.jl    # 10 checks
    julia --project=. proj/dcp_tests.jl        # 69 PASS and 1 documented discrepancy

## License

MIT, see `LICENSE`.
