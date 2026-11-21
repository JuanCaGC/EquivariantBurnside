# API reference

```@docs
EquivariantBurnside
```

## Groups BC_n(G)

```@docs
bc
bc_direct
bc_structure
bc_structure_gap
bc_structure_tom
AbGroup
ab
format_ab
certify_snf
```

## Symbols and classes

```@docs
BCSymbol
BCSymbol_preimage
BCClass
Base.push!(::BCClass, ::Integer, ::BCSymbol)
BCElement
BlockKey
bc_image
bc_blocks
```

## Transport and automorphisms

```@docs
bc_transport
bc_out_automorphisms
bc_find_automorphism
bc_inequivalence_certificates
```

## Toric surfaces

```@docs
AffineTorusMap
affine_group
ToricAction
toric_fan_P2
toric_fan_hexagon
equivariant_refinement
toric_class
FixedLayer
fixed_set
fixed_curves
special_points
```

## Incompressible symbols and the projective line

```@docs
ProjAction
pgl2_conjugate
pgl2_datum
projective_line_class
IncSymbol
IncClass
incompressible_class
inc_transport
inc_find_automorphism
```

## Indexed symbols, the first part of the recursion for linear actions

These are the building blocks of the recursion of Kresch and Tschinkel for the class of `P(V)` (arXiv:2108.00518, Section 8): indexed symbols and the operations `psi`, `tau`, `omega`, `eta`, induction, restriction and the product.

```@docs
indexed_character
IndexedSymbol
IndexedClass
indexed_psi
indexed_tau_matrix
indexed_tau
indexed_reindex
indexed_induce
indexed_eta
indexed_omega
indexed_restrict
indexed_product
```

## The recursion for projective linear actions

`projective_class` implements Proposition 8.3 and Theorem 8.4 of Kresch and Tschinkel (arXiv:2108.00518) for the class of `P(V)` with a finite group acting linearly, over the cyclotomic numbers. A representation is given as a GAP matrix group in the convention of `dcp.jl`, prepared by `linrep`. The classes are formal sums of indexed symbols, the relations of the Burnside group are applied only afterwards, through `bc_image`.

```@docs
LinearRepresentation
linrep
indexed_difference
chain_class
projective_class
indexed_negate_gamma
affine_class
projective_plus_class
projective_bc_class
projective_plus_bc_class
FieldFactor
projective_invariant
field_fingerprint
field_faithful
set_field_key_mode!
```

## Certificates

```@docs
NonzeroCertificate
certificate_nonzero
verify
verify_with_group
write_certificate
read_certificate
group_fingerprint
```

## Low level evaluation

```@docs
load_gap!
gapobj
npairs
prepare!
bcclass_init!
BlockMaps
block_maps
symbol_image
class_coords
class_is_zero
class_order
```

### Retained arrangement routines

These existing routines expose arrangement data. They do not compute classes of varieties.

```@docs
EquivariantBurnside.DCP.arrangement
EquivariantBurnside.DCP.chains
EquivariantBurnside.DCP.all_flags
EquivariantBurnside.DCP.entry_lookup
EquivariantBurnside.DCP.entry_action
```
