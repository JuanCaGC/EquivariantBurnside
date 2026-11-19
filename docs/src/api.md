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
```
