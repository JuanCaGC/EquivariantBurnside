# ---------------------------------------------------------------------------
# Fixed loci of affine actions on the torus (first step towards actions with reflections).
#
# Coordinates. T = (C/Z)^2 through u -> exp(2 pi i u). An affine map (nu, t) acts as u -> nu u + t mod Z^2.
#  L1 The fixed set of g = (nu, t) is {u : (nu - 1) u = -t mod Z^2}. For nu = 1 it is empty (t != 0) or all of T.
#     For det(nu - 1) != 0 it is a finite set of |det(nu - 1)| rational points.
#     For a reflection (nu of finite order with eigenvalue 1) nu - 1 = w m^T has rank one, w primitive, and the fixed set
#     is empty unless det(w, t) is an integer, in which case it is the union of d = gcd(m) cosets
#     {u : m' . u = c mod 1} of the one dimensional subtorus ker(m'), m = d m'. These cosets are called layers.
#  L2 The intersection of two nonparallel layers is a finite set of rational points, |det| of them.
# ---------------------------------------------------------------------------

"""
    FixedLayer(m, c)

The curve `{u in (C/Z)^2 : m . u = c mod 1}` in the torus, a coset of a one dimensional subtorus.

`m` is a primitive integer vector of length two and `c` a rational number modulo one.
"""
struct FixedLayer
    m::Vector{Int}
    c::Rational{Int}
    function FixedLayer(m, c)
        gcd(m[1], m[2]) == 1 || throw(ArgumentError("m must be primitive"))
        # a layer and its opposite describe the same curve: normalize the sign of m
        if m[1] < 0 || (m[1] == 0 && m[2] < 0)
            return new(-collect(m), _mod1(-Rational{Int}(c)))
        end
        return new(collect(m), _mod1(Rational{Int}(c)))
    end
end
Base.:(==)(a::FixedLayer, b::FixedLayer) = a.m == b.m && a.c == b.c
Base.hash(a::FixedLayer, h::UInt) = hash((a.m, a.c), h)
Base.show(io::IO, l::FixedLayer) = print(io, "FixedLayer(", l.m, ", ", l.c, ")")

_adjugate2(B) = [B[2, 2] -B[1, 2]; -B[2, 1] B[1, 1]]

# the points u in (Q/Z)^2 with B u = rhs mod Z^2, for an integer matrix B with nonzero determinant
function _solve_mod1(B, rhs)
    D = _det2(B)
    D == 0 && error("singular matrix")
    adj = _adjugate2(B)
    out = Set{Vector{Rational{Int}}}()
    for z1 in 0:(abs(D) - 1), z2 in 0:(abs(D) - 1)
        u = (adj * (rhs .+ [z1, z2])) .// D
        push!(out, Rational{Int}[_mod1(x) for x in u])
    end
    return sort!(collect(out))
end

"""
    fixed_set(g::AffineTorusMap)

The fixed set of an affine map of the torus, as `(:all,)`, `(:points, points)` or `(:layers, layers)`.

For the identity map the answer is `(:all,)` and for a nontrivial translation `(:points, [])`. When
`det(nu - 1)` is not zero the fixed set is a finite set of rational points `u` with `exp(2 pi i u)` the points of the
torus. When `nu` is a reflection the fixed set is a union of layers (curves), possibly none.

# Examples

```jldoctest
swap = AffineTorusMap([0 1; 1 0], [0, 0])
kind, layers = fixed_set(swap)
println(kind, " ", layers)

# output

layers FixedLayer[FixedLayer([1, -1], 0//1)]
```
"""
function fixed_set(g::AffineTorusMap)
    B = g.nu - _id2()
    if all(==(0), B)
        all(==(0), g.t) && return (:all,)
        return (:points, Vector{Rational{Int}}[])
    end
    D = _det2(B)
    if D != 0
        return (:points, _solve_mod1(B, -g.t))
    end
    # rank one: B = w m^T with w primitive
    j = findfirst(k -> any(!=(0), B[:, k]), 1:2)
    col = B[:, j]
    gg = gcd(col[1], col[2])
    w = col .÷ gg
    i = findfirst(!=(0), w)
    m = [B[i, k] ÷ w[i] for k in 1:2]
    @assert B == w * m'
    # solvability: -t in R w mod Z^2
    dd = w[1] * g.t[2] - w[2] * g.t[1]
    isinteger(dd) || return (:layers, FixedLayer[])
    gw, u, v = gcdx(w[1], w[2])
    if gw < 0
        u, v = -u, -v
    end
    pp, qq = -v, u                          # w' = (pp, qq), det(w, w') = 1
    s = -(g.t[1] * qq - g.t[2] * pp)        # -t = s w mod Z^2
    s = _mod1(Rational{Int}(s))
    d = gcd(m[1], m[2])
    mp = m .÷ d
    layers = FixedLayer[FixedLayer(mp, (s + j2) // d) for j2 in 0:(d - 1)]
    return (:layers, layers)
end

# intersection points of two layers
function _layer_intersection(a::FixedLayer, b::FixedLayer)
    M = [a.m[1] a.m[2]; b.m[1] b.m[2]]
    _det2(M) == 0 && return Vector{Rational{Int}}[]
    return _solve_mod1(M, [a.c, b.c])
end

_apply(g::AffineTorusMap, u) = Rational{Int}[_mod1(x) for x in g.nu * u .+ g.t]
_fixes(g::AffineTorusMap, u) = all(isinteger, _apply(g, u) .- u)

"""
    fixed_curves(act::ToricAction) -> Vector{NamedTuple}

The curves of the torus with nontrivial generic stabilizer, one entry for each layer.

Each entry has the `layer` and the group `H` of the elements of `act.G` that fix the whole curve pointwise (the
generic stabilizer of the curve), as a vector of elements. Only elements whose linear part is a reflection give
curves. The entries are sorted and the layers are distinct.

# Examples

```jldoctest
swap = AffineTorusMap([0 1; 1 0], [0, 0])
act = ToricAction([swap], toric_fan_hexagon())
println(length(fixed_curves(act)))

# output

1
```
"""
function fixed_curves(act::ToricAction)
    layers = Dict{FixedLayer,Vector{Any}}()
    for (g, f) in act.images
        f.nu == _id2() && continue
        kind = fixed_set(f)
        kind[1] == :layers || continue
        for l in kind[2]
            get!(layers, l, Any[])
        end
    end
    out = NamedTuple[]
    for l in sort!(collect(keys(layers)); by = x -> (x.m, x.c))
        # a point of the layer: u = (c/m1, 0) if m1 != 0, else (0, c/m2)
        u0 = l.m[1] != 0 ? Rational{Int}[l.c // l.m[1], 0] : Rational{Int}[0, l.c // l.m[2]]
        v = [-l.m[2], l.m[1]]                   # direction of the layer
        # g fixes the layer pointwise iff nu v = v (so that nu u0 + t + lambda v does not depend on lambda) and g fixes u0
        H = [g for (g, f) in act.images if f.nu * v == v && _fixes(f, u0)]
        push!(out, (layer = l, H = H))
    end
    return out
end

"""
    special_points(act::ToricAction) -> Vector{NamedTuple}

Points of the torus where several strata of the fixed locus meet, with their stabilizers and orbits.

The candidates are the isolated fixed points of the elements of `act.G` and the intersection points of two fixed
layers. Each result has the point `u` (a vector of rationals modulo one, the point is `exp(2 pi i u)`), its
`stabilizer` (elements of `act.G`), the size of its orbit `orbit` under the group and a representative flag `rep` that
is true for one point of each orbit. The result is sorted. These are the points where an equivariant blowup is
needed to reach standard form: they have either a nonabelian stabilizer, or several fixed curves through them.

# Examples

```jldoctest
a = AffineTorusMap([0 -1; 1 -1], [0, 0])
act = ToricAction([a], toric_fan_hexagon())
println(length(special_points(act)))

# output

3
```
"""
function special_points(act::ToricAction)
    cands = Set{Vector{Rational{Int}}}()
    layers = Set{FixedLayer}()
    for (g, f) in act.images
        f.nu == _id2() && continue
        kind = fixed_set(f)
        if kind[1] == :points
            union!(cands, kind[2])
        elseif kind[1] == :layers
            union!(layers, kind[2])
        end
    end
    ls = sort!(collect(layers); by = x -> (x.m, x.c))
    for i in eachindex(ls), j in (i + 1):length(ls)
        union!(cands, _layer_intersection(ls[i], ls[j]))
    end
    pts = sort!(collect(cands))
    out = NamedTuple[]
    seen = Set{Vector{Rational{Int}}}()
    for u in pts
        stab = [g for (g, f) in act.images if _fixes(f, u)]
        length(stab) <= 1 && continue
        orbit = Set(_apply(f, u) for (g, f) in act.images)
        isrep = !(u in seen)
        union!(seen, orbit)
        push!(out, (u = u, stabilizer = stab, orbit = length(orbit), rep = isrep))
    end
    return out
end
