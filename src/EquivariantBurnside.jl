"""
EquivariantBurnside -- combinatorial Burnside groups BC_n(G) of Tschinkel-Yang-Zhang
(arXiv:2112.12801), computed with OSCAR/GAP.

Two independent implementations are provided:

  * `bc(G, n)`         Theorem 5.2:  BC_n(G) = (+)_{[H,Y]} B_n(H)/(C_(H,Y)).
                       Scales to S_7, S_8, ...
  * `bc_direct(G, n)`  Definition-level: generators (H,Y,beta) of SC_n(G) and
                       relations (C), (V), (B2) *including the Theta_2 term*,
                       with no use of Theorem 5.2.  Small groups only, it exists
                       to validate the first implementation (and the theorem).

Conventions (Lemma 5.1 of the paper).  For an abelian H with H^ = Hom(H,C^x)
written additively, a generator of B_n(H) is a multiset of n characters in H^
(zeros allowed = padding) that generate H^.  Relations:
  (B)  b_i != b_j, both nonzero:   beta = beta_1 + beta_2,
         beta_1 = (.., b_i-b_j, ..)   beta_2 = (.., b_j-b_i, ..)
  (B=) b_i == b_j != 0:            beta = beta with one copy of b_i replaced by 0
  (V)  b_i + b_j = 0, both nonzero (i != j as positions):   beta = 0
  (C)  beta = beta^g for g in N_G(H) n N_G(Y)   (acting through Aut(H))
Zero entries are never blown up: doing so with b_j = 0 only reproduces (V), and
with b_i = b_j = 0 would (wrongly) force beta = 2*beta.
"""
module EquivariantBurnside
using Oscar
using Printf
using SHA
export bc, bc_structure, bc_structure_gap, bc_structure_tom, bc_direct, AbGroup, ab, format_ab, load_gap!, gapobj, npairs, certify_snf
export prepare!, bcclass_init!, BlockMaps, block_maps, symbol_image, class_coords, class_is_zero, class_order
export BCSymbol, BCSymbol_preimage, BCClass, BCElement, BlockKey, bc_image, bc_blocks
export bc_transport, bc_out_automorphisms, bc_find_automorphism, bc_inequivalence_certificates
export NonzeroCertificate, certificate_nonzero, verify, verify_with_group, write_certificate, read_certificate, group_fingerprint
const GAPFILE = joinpath(@__DIR__, "..", "gap", "bc_structure.g")
const _gap_loaded = Ref(false)

"""
    load_gap!()

Load the GAP structure engine once.

Takes no arguments and returns `nothing`. Repeated calls reuse the loaded engine.
"""
function load_gap!()
    if !_gap_loaded[]
        GAP.evalstr("Read(\"$(GAPFILE)\");")
        _gap_loaded[] = true
    end
    return nothing
end

include("abgroups.jl")
include("cokernel.jl")
include("characters.jl")
include("bn.jl")
include("structure.jl")
include("direct.jl")
include("tom.jl")
include("evaluate.jl")
include("symbols.jl")
include("certificates_nz.jl")
include("transport.jl")
include("dcp.jl")
end
