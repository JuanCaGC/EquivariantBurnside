# EquivariantBurnside

EquivariantBurnside computes combinatorial Burnside groups BC_n(G) with OSCAR and GAP. It also retains symbol evaluation, exact Smith certificates and the DCP arrangement routines.

## Local installation

Open Julia with `julia --project=.` from the checkout. Run `using Pkg` and then `Pkg.instantiate()` to install its dependencies.

```julia
using EquivariantBurnside, Oscar
bc(symmetric_group(4), 2)
# BC_2(G) = (Z/2)^3
```

## Scope

Phase 0 is a reorganization of existing code. What the package computes today:

- the groups ``BC_n(G)`` for any finite group given as an OSCAR group or a raw GAP group (`bc`, `bc_direct`),
- exact Smith normal form certificates (`certify_snf`),
- evaluation of integer combinations of symbols ``(H, Y, beta)`` in ``BC_n(G)`` with certificates of vanishing or non-vanishing (`class_is_zero`, `class_order`),
- the De Concini-Procesi arrangement data for linear actions, under `EquivariantBurnside.DCP`.

Not implemented yet: the class of an action on a projective space or a toric variety, the Kresch-Tschinkel recursion, and anything for general varieties. The function field part of a symbol is not recorded or computed.

The test suite records one documented basis discrepancy of the DCP data as a broken test instead of hiding it.
