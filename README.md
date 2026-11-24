# EquivariantBurnside (working name)

A Julia package, to be used together with [OSCAR](https://www.oscar-system.org), for computing equivariant Burnside invariants of finite group actions.

Status: research code under active development, as part of a master's thesis. The working code of `legacy/` was reorganized into a package under `src/` without changing its mathematics or its numerical output, and the classes of linear actions on projective spaces are now computed by an implementation of the Kresch-Tschinkel recursion. The results have not been peer reviewed, and the checks described below are computational.

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
- Toric surfaces with a finite group acting by translations of the torus and automorphisms of the lattice (`AffineTorusMap`, `ToricAction`, `equivariant_refinement`, `toric_class`, `fixed_curves`, `special_points`). The class in BC_2(G) is computed from the strata of a standard form model: the boundary of a G-invariant smooth fan, the closures of the curves fixed by reflections, and the blowups of the special points. It agrees with the class printed by Kresch and Tschinkel for C_2 x S_3 acting on the del Pezzo surface of degree 6, and does not depend on the fan or on additional blowup centers. Dimension three is not implemented.
- Arrangement and chain calculations under `EquivariantBurnside.DCP`.

## Scope

Inputs are finite groups given as OSCAR groups or raw GAP groups. Individual functions keep the input requirements of the frozen code, in particular symbol evaluation uses raw GAP groups.

### Linear actions on projective spaces

- `linrep(G)` wraps a finite matrix group as a `LinearRepresentation`. `projective_class(rep)` and `projective_plus_class(rep)` compute the class of P(V) and of P(1 + V) with the action of G by the recursion of Kresch and Tschinkel (arXiv:2108.00518, Theorems 8.4 and 8.5), as an integer combination of indexed symbols (`IndexedClass`). The operations used by the recursion are exposed as `indexed_psi`, `indexed_tau`, `indexed_eta`, `indexed_omega`, `indexed_restrict`, `indexed_induce` and `indexed_product`. `projective_bc_class` and `projective_plus_bc_class` give the image in BC_n(G/C).
- Field datum. Each symbol carries a presentation of its function field as a product of projective spaces with the action of the group through lift matrices (`FieldFactor`). `field_fixed_signature` records which subgroups have a fixed point, and `compare_fields` returns `:equal`, `:different` or `:unknown` for two fields with the same group data. `:unknown` is a real outcome and not a failure.
- Dimension three. `plus_divisor_symbols(rep; omega = true)` and `omega_divisor_symbols(rep)` return the divisor symbols of P(1 + V), and `certify_incompressible_dim3` builds a certificate of incompressibility for a divisor symbol. `certified = false` means not decided, it is not a proof of compressibility. `epsilon_twist` and `compare_plus_divisors` compare the classes of the twists by a character.

How these were checked: against the tables and examples printed in the papers (the S4 class, the dimension two cases), against an independently written second implementation of the operations, by invariance under a change of basis and under twisting by a character, and by mutation testing of the source. Dimension four and above has no printed reference beyond the agreement of the two implementations.

### Not implemented

Classes of actions on general varieties, toric varieties in dimension three, the omega symbols of divisors above dimension three, and a decision procedure for incompressibility (only certificates).

## Legacy snapshot

`legacy/bc/` is a copy of the working code of the repository `combinatorial-burnside-groups` at the time of the reorganization. It is frozen and read-only, and it is the reference for the regression tests:

    cd legacy/bc
    julia --project=. validate.jl all          # 88 checks, about 26 seconds
    julia --project=. proj/bcclass_tests.jl    # 10 checks
    julia --project=. proj/dcp_tests.jl        # 69 PASS and 1 documented discrepancy

## License

MIT, see `LICENSE`.
