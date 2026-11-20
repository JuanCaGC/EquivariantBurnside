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
- `bc_structure(G)` computes subgroup and stabilizer data through OSCAR. `bc_structure_gap(G)` retains the GAP oracle. Both accept OSCAR permutation, polycyclic and matrix groups, plus raw GAP groups.
- `bc` computes BC_n(G) by Theorem 5.2. `bc_direct` keeps the independent computation from the definition. `bc_structure_tom(n)` builds the structure for S_n from Table of Marks data. `certify_snf` returns exact Smith normal form certificates.
- The image in BC_n(G) of a class given as a sum of symbols, through `prepare!`, `symbol_image`, `class_coords`, `class_is_zero` and `class_order`.
- A checked front end for the same computation: `BCSymbol(G, hgens, ygens, betas)` (the quotient convention `Y <= Z_G(H)/H` of the papers) or `BCSymbol_preimage` (the convention `H <= Y <= Z_G(H)`), `BCClass(G, n)` for integer combinations, `bc_image` for the image in BC_n(G), and `is_zero`, `order`, `+`, `-` on the result. Invalid input raises an `ArgumentError` with a message that names the problem.
- Certificates of non-vanishing: `certificate_nonzero` builds a plain text certificate, `verify` checks it with the standalone file `verifier/verify_nonzero.jl` (pure Julia, no packages), and `verify_with_group` rebuilds the group from the certificate and re-derives the block data through OSCAR. What is not certified: that the symbols map to the class vector, which is trusted engine code.
- `bc_image` evaluates a class in the group BC_n(G) defined by the relations (O), (C), (V) and (B) with its Theta_2 term. The block decomposition of Theorem 5.2 has no Theta_2 term, so each symbol is first replaced by the sum of its restrictions to the subgroups of H (`blowup_correction`, see the conventions page of the documentation). This was checked against the defining presentation on small groups and on the group of order 192 of EBGLA Example 7.5.
- Transport of symbols and classes along group isomorphisms (`bc_transport`), representatives of Out(G) (`bc_out_automorphisms`), and the comparison of two classes up to all automorphisms of the group (`bc_find_automorphism`, `bc_inequivalence_certificates`).
- Toric surfaces with a finite group acting by translations of the torus and automorphisms of the lattice, without reflections (`AffineTorusMap`, `ToricAction`, `equivariant_refinement`, `toric_class`). The class in BC_2(G) is computed from the boundary strata of a G-invariant smooth fan. Actions with reflections (fixed curves) and dimension three are not implemented.
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
