# The incompressible divisor symbols of the class of a toric surface (Phase 5.3 and 5.4).
#
# In dimension two the divisor symbols (H, Y acting on K, beta) of the class of a toric action have K = k(P^1), the field of
# a curve. By Proposition 3.6 of Kresch-Tschinkel (arXiv:2108.00518) such a symbol is compressible, that is, a
# term of the blowup relation (B2), exactly when Y is cyclic. The symbols with Y not cyclic generate a direct summand of
# Burn_2(G) with no relations except conjugation (C), so they can be compared as formal sums. The datum of K is the
# class function theta of `pgl2_datum`. Three kinds of curves occur: the boundary divisors, the closures of the curves
# fixed by reflections, and the exceptional curves of the blowups of special points.
#
# Conventions. A curve is a P^1 with coordinate z = x0 / x1 and the action is a left action through 2 by 2 matrices M_g,
# so that diag(a, 1) is z -> a z and [[0, a], [1, 0]] is z -> a / z.
#  I1 Boundary divisor D_rho, rho = (p, q). The coordinate is w = det(rho, u) = p u2 - q u1 and z = exp(2 pi i w). An
#     element g = (nu, t) with nu rho = rho sends w to s w + det(rho, t), s = det(nu) = +-1. So M_g = diag(e, 1) for
#     s = 1 and [[0, e], [1, 0]] for s = -1, with e = exp(2 pi i det(rho, t)).
#  I2 Closure of a fixed layer {m . u = c}. Let v = (-m2, m1) be its primitive direction, u0 a rational point of the layer and
#     lambda an integer covector with lambda . v = 1. The coordinate is s = lambda . (u - u0) and z = exp(2 pi i s).
#     An element g = (nu, t) preserving the layer has nu v = e v with e = +-1 and sends s to e s + s0,
#     s0 = lambda . (nu u0 + t - u0). So M_g = diag(exp(2 pi i s0), 1) for e = 1 and [[0, exp(2 pi i s0)], [1, 0]] for e = -1.
#  I3 Exceptional curve P(T_p) over a point p with stabilizer S_p: the matrix of g is the differential of g at p, in the
#     coordinates of the tangent plane used by `_blowup_symbols`, and H is the group of scalar elements.

# class function theta(M) in [0, 1/2], as a rational with the order of M in PGL_2 as denominator
function _theta_matrix(M)
    n = 1
    P = Matrix{ComplexF64}(M)
    I2c = Matrix{ComplexF64}([1 0; 0 1])
    while !_pm_equal(P, I2c)
        P = P * M
        n += 1
        n > 10_000 && error("the matrix has no finite order in PGL_2")
    end
    d = M[1, 1] * M[2, 2] - M[1, 2] * M[2, 1]
    c = ((M[1, 1] + M[2, 2])^2 / d - 2) / 2
    th = acos(clamp(real(c), -1.0, 1.0)) / (2pi)
    k = round(Int, th * n)
    abs(th * n - k) < 1e-6 || error("the ratio of eigenvalues is not a root of unity of order $n")
    return (k // n, n)
end

"""
    IncSymbol

An incompressible divisor symbol `(H, Y acting on P^1, beta)` of a group `G` with the datum of the action on the line.

Fields: `G`, `H` the elements of the cyclic group `H`, `Y` the elements of its preimage `Y~` in `G` (the stabilizer of
the curve), `beta` a `Dict` from the elements of `H` to the exponent `x` in `Q/Z` of the character value
`exp(2 pi i x)` and `theta` a `Dict` from the elements of `Y~` to the class function of `pgl2_datum` (it is constant on the
cosets of `H`). Symbols are created by `incompressible_class` and compared up to conjugation in `G` inside an `IncClass`.
"""
struct IncSymbol
    G::Any
    H::Vector{Any}
    Y::Vector{Any}
    beta::Dict{Any,Rational{Int}}
    theta::Dict{Any,Rational{Int}}
end

"""
    IncClass(G)

A formal sum of incompressible divisor symbols of `G` modulo conjugation, an element of the group `Burn^inc_2(G)` of
Kresch-Tschinkel (arXiv:2108.00518, Proposition 3.4), which is free on the symbols modulo (C).

`G` is a finite OSCAR group. Create with `IncClass(G)` and add with `push!(cls, sym)` or `push!(cls, coef, sym)`. Classes
support `+`, `-`, integer `*`, `==`, `iszero` and `length` (the number of distinct nonzero symbols). The coefficients are
integers and two symbols are identified when some element of `G` conjugates one to the other, `H`, `Y~`, `beta` and the datum
together. The normal form is the minimum over `G` of the conjugated data, so the cost of a symbol is `|G|` conjugations.

# Examples

```jldoctest
G = symmetric_group(3)
println(iszero(IncClass(G)))

# output

true
```
"""
mutable struct IncClass
    G::Any
    elems::Vector{Any}
    idx::Dict{Any,Int}
    terms::Dict{Any,Tuple{Int,IncSymbol}}
end

function IncClass(G)
    el = Any[g for g in G]
    return IncClass(G, el, Dict{Any,Int}(g => i for (i, g) in enumerate(el)), Dict{Any,Tuple{Int,IncSymbol}}())
end

# the conjugated data of a symbol as a comparable tuple
function _inc_key(cls::IncClass, s::IncSymbol, g)
    idx = cls.idx
    h = sort!(Int[idx[x^g] for x in s.H])
    y = sort!(Int[idx[x^g] for x in s.Y])
    b = sort!(Tuple{Int,Rational{Int}}[(idx[x^g], v) for (x, v) in s.beta])
    t = sort!(Tuple{Int,Rational{Int}}[(idx[x^g], v) for (x, v) in s.theta])
    return (h, y, b, t)
end

function _inc_canonical(cls::IncClass, s::IncSymbol)
    best = nothing
    for g in cls.elems
        k = _inc_key(cls, s, g)
        if best === nothing || k < best
            best = k
        end
    end
    return best
end

function Base.push!(cls::IncClass, coef::Integer, s::IncSymbol)
    s.G == cls.G || throw(ArgumentError("the symbol belongs to a different group"))
    k = _inc_canonical(cls, s)
    old = get(cls.terms, k, (0, s))
    c = old[1] + Int(coef)
    if c == 0
        delete!(cls.terms, k)
    else
        cls.terms[k] = (c, old[2])
    end
    return cls
end
Base.push!(cls::IncClass, s::IncSymbol) = push!(cls, 1, s)

Base.length(cls::IncClass) = length(cls.terms)
Base.iszero(cls::IncClass) = isempty(cls.terms)
Base.copy(cls::IncClass) = IncClass(cls.G, cls.elems, cls.idx, copy(cls.terms))
function Base.:+(a::IncClass, b::IncClass)
    a.G == b.G || throw(ArgumentError("the classes belong to different groups"))
    out = copy(a)
    for (_, (c, s)) in b.terms
        push!(out, c, s)
    end
    return out
end
function Base.:*(c::Integer, a::IncClass)
    out = IncClass(a.G, a.elems, a.idx, Dict{Any,Tuple{Int,IncSymbol}}())
    c == 0 && return out
    for (k, (x, s)) in a.terms
        out.terms[k] = (Int(c) * x, s)
    end
    return out
end
Base.:-(a::IncClass) = (-1) * a
Base.:-(a::IncClass, b::IncClass) = a + (-b)
function Base.:(==)(a::IncClass, b::IncClass)
    a.G == b.G || return false
    length(a.terms) == length(b.terms) || return false
    for (k, (c, _)) in a.terms
        haskey(b.terms, k) && b.terms[k][1] == c || return false
    end
    return true
end
Base.hash(a::IncClass, h::UInt) = hash(sort([(k, c) for (k, (c, _)) in a.terms]), h)

function Base.show(io::IO, cls::IncClass)
    print(io, "IncClass(", length(cls.terms), " symbols)")
    for (_, (c, s)) in sort(collect(cls.terms); by = first)
        print(io, "\n  ", c, " * (|H| = ", length(s.H), ", |Y~| = ", length(s.Y), ", |Y| = ", length(s.Y) ÷ length(s.H), ")")
    end
end

# the symbol of the curve with generic stabilizer H, stabilizer Y~ and matrices of the elements of Y~. Returns nothing
# when Y = Y~ / H is cyclic (a compressible divisor symbol)
function _curve_symbol(G, H, Yt, mats, beta)
    I2c = Matrix{ComplexF64}([1 0; 0 1])
    triv = Any[g for g in Yt if _pm_equal(mats[g], I2c)]
    Set(triv) == Set(H) || error("the elements acting trivially on the curve are not the generic stabilizer H")
    # the matrices must define a homomorphism to PGL_2 for the product of G or for the opposite product
    left_ok, right_ok = true, true
    for g in Yt, h in Yt
        gh = mats[g * h]
        left_ok &= _pm_equal(gh, mats[g] * mats[h])
        right_ok &= _pm_equal(gh, mats[h] * mats[g])
        (left_ok || right_ok) || error("the matrices of the action on the curve are not a homomorphism")
    end
    theta = Dict{Any,Rational{Int}}()
    ymax = 1
    for g in Yt
        th, n = _theta_matrix(mats[g])
        theta[g] = th
        ymax = max(ymax, n)
    end
    ysize = length(Yt) ÷ length(H)
    ymax == ysize && return nothing
    return IncSymbol(G, Any[h for h in H], Any[g for g in Yt], beta, theta)
end

# the character of the cyclic group H with generator h0 of order k and weight exponent c
function _cyclic_beta(H, h0, c)
    k = Int(order(h0))
    beta = Dict{Any,Rational{Int}}()
    for j in 0:(k - 1)
        beta[h0^j] = (j * c) // k - floor((j * c) // k)
    end
    Set(keys(beta)) == Set(H) || error("the generator does not generate H")
    return beta
end

"""
    incompressible_class(act::ToricAction; extra_points = []) -> IncClass

The incompressible part of the class of the action on the toric surface, in `Burn^inc_2(G)`.

The argument is a `ToricAction` as in `toric_class` and `extra_points` are extra rational points of the torus to blow up,
which must not change the result. Returns an `IncClass`: the formal sum, over the `G`-orbits of the curves of the standard form
model, of the symbols `(H, Y acting on P^1, beta)` with `Y` not cyclic, together with the class function `theta` of
the action of `Y` on the line, see `pgl2_datum`. The curves are the boundary divisors, the closures of the curves fixed
by reflections and the exceptional curves of the blowups of the special points, as in `toric_class`. Symbols with cyclic `Y` are
compressible (Proposition 3.6 of Kresch-Tschinkel) and are left out. The curves are all rational, the fields of
their functions are `k(P^1)`.

The matrix of each element of the stabilizer of a curve is computed internally, for the boundary and the fixed curves by the
formulas in the header of the source file, for the exceptional curves by the differential of the action. The code checks that
these matrices form a homomorphism and that the elements acting trivially are exactly `H`.

Validated against printed values (see `test/test_incompressible.jl`): the symbol `(C2, S3 acting on k(P^1), (1))` of Proposition 6.1
of Kresch-Tschinkel with coefficient 1 for the toric action and 2 for the linear action on `P(1 + V_chi)`, the symbols
`(C_n, D_m, eps)` and `(C_n, D_m, -eps)` of Corollary 7.7 and Lemma 7.8 of Tschinkel-Yang-Zhang, the two symbols
`(C6, D4, (1))` and `(C6, D4, (5))` of Example 7.9, and the absence of incompressible symbols in Example 7.5. Only fields `k(P^1)` and
dimension two are covered, and the result depends on `toric_class` for the choice of model.

# Examples

```jldoctest
refl = AffineTorusMap([1 0; 0 -1], [0, 0])
tr = AffineTorusMap([1 0; 0 1], [1//5, 0])
half = AffineTorusMap([1 0; 0 1], [0, 1//2])
act = ToricAction([refl, tr, half], [[1, 0], [0, 1], [-1, 0], [0, -1]])
cls = incompressible_class(act)
println(length(cls))

# output

2
```
"""
function incompressible_class(act::ToricAction; extra_points = Vector{Vector{Rational{Int}}}())
    G = act.G
    nus = _linear_parts(act)
    has_reflections = any(nu -> nu != _id2() && _det2(nu - _id2()) == 0, nus)
    rays = equivariant_refinement(act)
    cls = IncClass(G)
    elems = collect(keys(act.images))
    Aelems = [g for g in elems if act.images[g].nu == _id2()]
    # boundary divisors
    if length(Aelems) > 1
        for rho in _orbits_of_rays(rays, nus)
            p, q = rho
            Hr = Any[a for a in Aelems if isinteger(q * act.images[a].t[1] - p * act.images[a].t[2])]
            length(Hr) == 1 && continue
            a0 = Hr[argmax([Int(order(a)) for a in Hr])]
            k = Int(order(a0))
            k == length(Hr) || error("the pointwise stabilizer of a divisor is not cyclic")
            gg, u, v = gcdx(p, q)
            gg < 0 && ((u, v) = (-u, -v))
            pp, qq = -v, u
            t = act.images[a0].t
            c = (t[1] * qq - t[2] * pp) * k
            denominator(c) == 1 || error("weight is not an integer")
            Yt = Any[g for g in elems if Int.(act.images[g].nu * rho) == rho]
            mats = Dict{Any,Matrix{ComplexF64}}()
            for g in Yt
                f = act.images[g]
                e = _cisq(p * f.t[2] - q * f.t[1])
                mats[g] = _det2(f.nu) == 1 ? ComplexF64[e 0; 0 1] : ComplexF64[0 e; 1 0]
            end
            s = _curve_symbol(G, Hr, Yt, mats, _cyclic_beta(Hr, a0, Int(numerator(c))))
            s === nothing || push!(cls, s)
        end
    end
    if has_reflections
        fc = fixed_curves(act)
        seen = Set{FixedLayer}()
        for c in fc
            c.layer in seen && continue
            union!(seen, Set(_move_layer(c.layer, f) for (g, f) in act.images))
            length(c.H) == 2 || error("the generic stabilizer of a fixed curve has order $(length(c.H))")
            h = first(g for g in c.H if act.images[g].nu != _id2())
            m = c.layer.m
            v = [-m[2], m[1]]
            u0 = m[1] != 0 ? Rational{Int}[c.layer.c // m[1], 0] : Rational{Int}[0, c.layer.c // m[2]]
            gg, lu, lv = gcdx(v[1], v[2])
            gg < 0 && ((lu, lv) = (-lu, -lv))
            lam = [lu, lv]
            lam[1] * v[1] + lam[2] * v[2] == 1 || error("no covector of value one on the direction of the curve")
            Yt = Any[g for (g, f) in act.images if _move_layer(c.layer, f) == c.layer]
            mats = Dict{Any,Matrix{ComplexF64}}()
            for g in Yt
                f = act.images[g]
                nv = f.nu * v
                s0 = Rational{Int}(lam[1] * (f.nu * u0 .+ f.t .- u0)[1] + lam[2] * (f.nu * u0 .+ f.t .- u0)[2])
                e = _cisq(s0)
                mats[g] = nv == v ? ComplexF64[e 0; 0 1] : (nv == -v ? ComplexF64[0 e; 1 0] : error("the element does not preserve the direction of the curve"))
            end
            s = _curve_symbol(G, Any[x for x in c.H], Yt, mats, Dict{Any,Rational{Int}}(one(G) => 0 // 1, h => 1 // 2))
            s === nothing || push!(cls, s)
        end
        # exceptional curves of the blowups of the special points. The special points of the boundary are left out: the
        # tangent action there is diagonal, so S_p / Z is cyclic and the symbol is compressible
        for lp in _interior_points(act, extra_points)
            S = lp.stab
            Z = Any[g for g in S if _isscalar(lp.mats[g])]
            length(Z) > 1 || continue
            z = Z[argmax([Int(order(g)) for g in Z])]
            o = Int(order(z))
            o == length(Z) || error("the scalar subgroup is not cyclic")
            c = _expo(lp.mats[z][1, 1], o)
            s = _curve_symbol(G, Z, S, lp.mats, _cyclic_beta(Z, z, c))
            s === nothing || push!(cls, s)
        end
    end
    return cls
end

"""
    inc_transport(cls::IncClass, phi) -> IncClass

Transport a class along an isomorphism of groups.

`phi` is an isomorphism from the group of `cls` onto another group, an OSCAR group homomorphism or a raw GAP mapping. Each
element in `H`, in `Y~` and in the data `beta` and `theta` is replaced by its image, so the result lives in the target
group. Inner automorphisms act trivially, as in `bc_transport`. Throws `ArgumentError` when `phi` is not an
isomorphism defined on the group of the class.
"""
function inc_transport(cls::IncClass, phi)
    G2, m = _checked_map(phi, gapobj(cls.G))
    mp(x) = Oscar.group_element(G2, GAP.Globals.Image(m, GAP.GapObj(x)))
    out = IncClass(G2)
    for (_, (c, s)) in cls.terms
        s2 = IncSymbol(G2, Any[mp(x) for x in s.H], Any[mp(x) for x in s.Y],
                       Dict{Any,Rational{Int}}(mp(x) => v for (x, v) in s.beta),
                       Dict{Any,Rational{Int}}(mp(x) => v for (x, v) in s.theta))
        push!(out, c, s2)
    end
    return out
end

"""
    inc_find_automorphism(cls1, cls2, phi = nothing)

Find an automorphism that makes two incompressible classes equal.

`cls1` and `cls2` are `IncClass` values of groups `G1` and `G2`. When they live in the same group, `phi` may be omitted,
otherwise it is an isomorphism `G1 -> G2`. Returns a representative `psi` of Out(G2), as in `bc_out_automorphisms`, such that
the class of `cls1` carried by `phi` and then by `psi` equals `cls2`, or `nothing` if there is none. Since the
group `Burn^inc_2(G)` is free on the symbols, `nothing` is a proof that the actions have different classes in
`Burn_2(G)` for every identification of the groups.
"""
function inc_find_automorphism(cls1::IncClass, cls2::IncClass, phi = nothing)
    c1 = phi === nothing ? cls1 : inc_transport(cls1, phi)
    c1.G == cls2.G || throw(ArgumentError("the classes live in different groups, give an isomorphism `phi` from the group of the first class onto the group of the second"))
    for psi in bc_out_automorphisms(c1.G)
        inc_transport(c1, psi) == cls2 && return psi
    end
    return nothing
end
