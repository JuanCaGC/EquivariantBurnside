# ---------------------------------------------------------------------------
# Transport of symbols and classes along isomorphisms, and comparison up to Aut(G).
#
# Conventions (documented where chosen).
#  T1 An isomorphism phi: G1 -> G2 sends a symbol (H, Y, beta) of G1 to (phi(H), phi(Y), beta o phi^-1).
#     In the coordinates of `BCSymbol` this keeps every integer vector c of characters and replaces each
#     generator h_j of H and each generator of Y by its image, so that beta'(phi(h_j)) = beta(h_j).
#  T2 The induced map on BC_n is a group isomorphism BC_n(G1) -> BC_n(G2). It respects the relations
#     (O), (C), (V), (B) because phi respects centralizers, quotients and characters.
#  T3 An inner automorphism acts trivially on BC_n(G) (relation (C)). Hence to compare two classes up to
#     all automorphisms of G it is enough to run over representatives of Out(G) = Aut(G)/Inn(G).
#  T4 Two notions are kept apart. "Equal in BC_n(G) for a given identification" is `bc_image(a) == bc_image(b)`.
#     "Equal up to Aut(G)" is `bc_find_automorphism`. The first is what the papers call G-equivariantly
#     birational classes with the same G and the identity identification. The second is the relevant one
#     for conjugacy of subgroups of a Cremona group.
# ---------------------------------------------------------------------------

# Codomain and GAP mapping of an OSCAR group homomorphism or of a raw GAP mapping.
function _hom_data(phi)
    phi isa GAP.GapObj && return (GAP.Globals.Range(phi), phi)
    return (codomain(phi), GAP.GapObj(phi))
end

function _checked_map(phi, Ggap)
    G2, m = _hom_data(phi)
    src = GAP.Globals.Source(m)
    (_same_group(src, Ggap) || src == Ggap) ||
        throw(ArgumentError("the homomorphism is not defined on the group of the symbol or class"))
    GAP.Globals.IsBijective(m) || throw(ArgumentError("the homomorphism is not an isomorphism"))
    return G2, m
end

"""
    bc_transport(s::BCSymbol, phi) -> BCSymbol
    bc_transport(cls::BCClass, phi) -> BCClass

Transport a symbol or a class along an isomorphism of groups.

`phi` is an isomorphism from the group of `s` (or `cls`) onto another group `G2`, either an OSCAR group
homomorphism or a raw GAP mapping. The result lives in `G2`. Each generator of H and of Y is replaced by its
image under `phi` and the integer character vectors are kept, so the character of the new symbol on the
image of `h_j` equals the old character on `h_j`. The induced map `BC_n(G) -> BC_n(G2)` is a group
isomorphism, and an inner automorphism induces the identity. Throws `ArgumentError` when `phi` is not
defined on the group of the argument or is not bijective.

# Examples

```jldoctest
S3 = symmetric_group(3)
P = small_group(6, 1)
f = isomorphism(S3, P)
s = BCSymbol(S3, [cperm(S3, [1,2,3])], [cperm(S3, [1,2,3])], [[1],[1]])
t = bc_transport(s, f)
println(order(bc_image(s, 2)) == order(bc_image(t, 2)))

# output

true
```
"""
function bc_transport(s::BCSymbol, phi)
    G2, m = _checked_map(phi, s.Ggap)
    hg = Any[GAP.Globals.Image(m, h) for h in s.hg]
    yg = Any[GAP.Globals.Image(m, y) for y in s.yg]
    return _bcsymbol(G2, hg, yg, s.betas, false)
end

function bc_transport(cls::BCClass, phi)
    G2, _ = _checked_map(phi, cls.Ggap)
    out = BCClass(G2, cls.n)
    for (c, s) in cls.terms
        push!(out, c, bc_transport(s, phi))
    end
    return out
end

"""
    bc_out_automorphisms(G)

Representatives of Out(G) = Aut(G)/Inn(G).

Returns a vector of automorphisms of `G`, one for each coset of the inner automorphisms. They are OSCAR
group homomorphisms when `G` is an OSCAR group and GAP mappings when `G` is a raw GAP group. The identity
coset is represented by some inner automorphism, not necessarily the identity map. Since inner
automorphisms act trivially on `BC_n(G)`, comparing classes under these representatives covers all of
Aut(G). The cost grows with `|Out(G)|`, which can be large for elementary abelian groups.

# Examples

```jldoctest
println(length(bc_out_automorphisms(symmetric_group(4))))
println(length(bc_out_automorphisms(symmetric_group(6))))

# output

1
2
```
"""
function bc_out_automorphisms(G)
    Gg = gapobj(G)
    A = GAP.Globals.AutomorphismGroup(Gg)
    I = GAP.Globals.InnerAutomorphismsAutomorphismGroup(A)
    T = GAP.Globals.RightTransversal(A, I)
    maps = [T[i] for i in 1:length(T)]
    G isa GAP.GapObj && return maps
    return [Oscar.GAPGroupHomomorphism(G, G, m) for m in maps]
end

# class of `cls1` carried to the group of `cls2`, with a check that the groups then agree
function _carry(cls1::BCClass, cls2::BCClass, phi)
    c1 = phi === nothing ? cls1 : bc_transport(cls1, phi)
    _same_group(c1.Ggap, cls2.Ggap) ||
        throw(ArgumentError("the classes live in different groups, give an isomorphism `phi` from the group of the first class onto the group of the second"))
    c1.n == cls2.n || throw(ArgumentError("the classes have a different n"))
    return c1
end

"""
    bc_find_automorphism(cls1, cls2, phi = nothing)

Find an automorphism that makes two classes have the same image in BC_n(G).

`cls1` and `cls2` are classes of groups `G1` and `G2`. When they live in the same group, `phi` may be omitted.
Otherwise `phi` is an isomorphism `G1 -> G2`. Returns a representative `psi` of Out(G2), as in
`bc_out_automorphisms`, such that the image of `cls1` carried by `phi` and then by `psi` equals the image of
`cls2`, or `nothing` if there is none. A result of `nothing` means that BC_n(G2) distinguishes the two classes
for every identification of the groups. A non-`nothing` result means only that this invariant cannot tell
them apart under that identification, not that the actions are birational.

# Examples

```jldoctest
S3 = symmetric_group(3)
s = BCSymbol(S3, [cperm(S3, [1,2,3])], [cperm(S3, [1,2,3])], [[1],[1]])
a = BCClass(S3, 2); push!(a, s)
b = BCClass(S3, 2); push!(b, s)
println(bc_find_automorphism(a, b) !== nothing)

# output

true
```
"""
function bc_find_automorphism(cls1::BCClass, cls2::BCClass, phi = nothing)
    c1 = _carry(cls1, cls2, phi)
    x2 = bc_image(cls2)
    for psi in bc_out_automorphisms(c1.G)
        bc_image(bc_transport(c1, psi)) == x2 && return psi
    end
    return nothing
end

"""
    bc_inequivalence_certificates(cls1, cls2, phi = nothing) -> Vector{NonzeroCertificate}

Certify that two classes differ in BC_n(G) under every automorphism of G.

Same arguments as `bc_find_automorphism`. For each representative `psi` of Out(G2) it computes the image of
the difference between `cls1` carried by `phi` and `psi`, and `cls2`, and returns a non-vanishing certificate
for it. The result has one certificate per representative, in the order of `bc_out_automorphisms`. Throws
`ArgumentError` if some difference vanishes, which is the case where `bc_find_automorphism` would succeed.
All certificates are certificates in the group G2.

# Examples

```jldoctest
S3 = symmetric_group(3)
s = BCSymbol(S3, [cperm(S3, [1,2,3])], [cperm(S3, [1,2,3])], [[1],[1]])
a = BCClass(S3, 2); push!(a, s)
b = BCClass(S3, 2)
certs = bc_inequivalence_certificates(a, b)
println(length(certs), " ", all(verify, certs))

# output

1 true
```
"""
function bc_inequivalence_certificates(cls1::BCClass, cls2::BCClass, phi = nothing)
    c1 = _carry(cls1, cls2, phi)
    certs = NonzeroCertificate[]
    for psi in bc_out_automorphisms(c1.G)
        d = bc_image(bc_transport(c1, psi) - cls2)
        is_zero(d) && throw(ArgumentError("the difference of the classes vanishes after an automorphism of the group"))
        push!(certs, certificate_nonzero(d))
    end
    return certs
end
