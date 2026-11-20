# Finite group actions on the projective line, the field datum of dimension one.
#
# A faithful action of a finite group Y on P^1 is a faithful homomorphism psi: Y -> PGL_2(C). It is stored through
# lifts M_g in GL_2(C), well defined up to scalars. Conventions of this file:
#   * points of P^1 are lines [x0 : x1] in C^2 and the coordinate is z = x0 / x1, so that diag(a, 1) is
#     z -> a z and [[0, a], [1, 0]] is z -> a / z,
#   * the action is a left action: M_{g h} = M_g M_h for the `:left` convention, M_h M_g for `:right`,
#   * the weight of a point stabilizer at a fixed point p = [v] is the eigenvalue of the differential of g at p.
#     For M v = lambda v and the other eigenvalue mu the tangent space is Hom(L, V / L), so the weight is mu / lambda.

"""
    ProjAction(G, mats; gens = gens(G), convention = :left)

A faithful action of the finite group `G` on the projective line through matrices in `GL_2(C)` up to scalars.

`G` is a finite OSCAR group, `gens` a list of elements that generate `G` and `mats` the matrices of the images of
`gens`, as 2 by 2 complex matrices. The constructor extends the matrices to all of `G` by walking the Cayley graph and
checks that this is a well defined homomorphism to `PGL_2(C)`, and that it is faithful. The field `mats` holds one
matrix of determinant one for each element of `G`, determined up to sign. `convention` is `:left` if the
product `g * h` of `G` is the composition `g` after `h`, and `:right` if it is `h` after `g`.

Throws `ArgumentError` for a wrong number or size of matrices, a singular matrix, a map that is not a
homomorphism for the chosen convention, or an action that is not faithful.

# Examples

```jldoctest
G = symmetric_group(3)
r = [exp(2im * pi / 3) 0; 0 1]
s = [0 1; 1 0]
act = ProjAction(G, [r, s]; gens = [cperm(G, [1, 2, 3]), perm(G, [2, 1, 3])])
println(order(act.G))

# output

6
```
"""
struct ProjAction
    G::Any
    mats::Dict{Any,Matrix{ComplexF64}}
end

# normalization of a matrix up to scalar, as a rounded key
function _pm_key(M)
    for x in (M[1, 1], M[1, 2], M[2, 1], M[2, 2])
        if abs(x) > 1e-6
            N = M ./ x
            return Tuple(round(z; digits = 5) + 0.0im for z in (N[1, 1], N[1, 2], N[2, 1], N[2, 2]))
        end
    end
    error("the zero matrix")
end

_pm_equal(A, B) = _pm_key(A) == _pm_key(B)

function _unimodular(M)
    d = M[1, 1] * M[2, 2] - M[1, 2] * M[2, 1]
    abs(d) > 1e-9 || throw(ArgumentError("a matrix is singular"))
    return Matrix{ComplexF64}(M ./ sqrt(d))
end

function ProjAction(G, mats::AbstractVector; gens = Oscar.gens(G), convention::Symbol = :left)
    convention in (:left, :right) || throw(ArgumentError("convention must be :left or :right"))
    length(gens) == length(mats) || throw(ArgumentError("give one matrix for each of the $(length(gens)) generators"))
    for M in mats
        size(M) == (2, 2) || throw(ArgumentError("the matrices must be 2 by 2"))
    end
    ms = [_unimodular(ComplexF64.(M)) for M in mats]
    comp(A, B) = _unimodular(convention == :left ? A * B : B * A)
    one2 = Matrix{ComplexF64}([1 0; 0 1])
    images = Dict{Any,Matrix{ComplexF64}}(one(G) => one2)
    queue = Any[one(G)]
    while !isempty(queue)
        x = popfirst!(queue)
        for (s, m) in zip(gens, ms)
            y = x * s
            want = comp(images[x], m)
            if haskey(images, y)
                _pm_equal(images[y], want) || throw(ArgumentError(
                    "the matrices do not extend to a homomorphism for convention :$convention " *
                    "(try the other convention if G acts on the right)"))
            else
                images[y] = want
                push!(queue, y)
            end
        end
    end
    length(images) == Int(order(G)) || throw(ArgumentError("the given elements do not generate G"))
    length(Set(_pm_key(M) for M in values(images))) == length(images) ||
        throw(ArgumentError("the action is not faithful: two elements of G give the same transformation of the line"))
    return ProjAction(G, images)
end

"""
    pgl2_conjugate(act, P)

The action `act` conjugated by the matrix `P` of `GL_2(C)`: the element `g` acts through `P M_g P^-1`.

The arguments are a `ProjAction` and an invertible 2 by 2 matrix. Returns a `ProjAction` on the same group. The
datum of `pgl2_datum` does not change.
"""
function pgl2_conjugate(act::ProjAction, P)
    size(P) == (2, 2) || throw(ArgumentError("P must be 2 by 2"))
    abs(P[1, 1] * P[2, 2] - P[1, 2] * P[2, 1]) > 1e-9 || throw(ArgumentError("P is singular"))
    Pc = ComplexF64.(P)
    return ProjAction(act.G, Dict{Any,Matrix{ComplexF64}}(g => _unimodular(Pc * M * inv(Pc)) for (g, M) in act.mats))
end

"""
    pgl2_datum(act)

The complete invariant of a faithful action on the projective line up to conjugation in `PGL_2(C)`.

The argument is a `ProjAction`. Returns a `Dict` from the elements of the group to the rational number
`theta` in `[0, 1/2]` such that the ratio of the eigenvalues of the element is `exp(2 pi i theta)` up to inversion.
This is the class function `chi(g) = 1 + 2 cos(2 pi theta(g))`, the character of the three dimensional orthogonal
representation `Ad` composed with the action. Two faithful actions of the same group on `P^1` are conjugate in
`PGL_2(C)` exactly when their data are equal, because isomorphic orthogonal representations of a finite group are
conjugate by an orthogonal matrix, and `PGL_2(C) = SO_3(C)`.

Throws an error if some ratio of eigenvalues is not a root of unity of the order of the element, which cannot
happen for a `ProjAction` that passed its checks.

# Examples

```jldoctest
G = cyclic_group(PermGroup, 5)
M = [exp(2im * pi * 2 / 5) 0; 0 1]
act = ProjAction(G, [M])
d = pgl2_datum(act)
println(d[gen(G, 1)])

# output

2//5
```
"""
function pgl2_datum(act::ProjAction)
    out = Dict{Any,Rational{Int}}()
    for (g, M) in act.mats
        o = Int(order(g))
        tr = M[1, 1] + M[2, 2]
        d = M[1, 1] * M[2, 2] - M[1, 2] * M[2, 1]
        c = (tr^2 / d - 2) / 2          # cos(2 pi theta)
        abs(imag(c)) < 1e-6 || error("the trace invariant is not real")
        th = acos(clamp(real(c), -1.0, 1.0)) / (2pi)
        k = round(Int, th * o)
        abs(th * o - k) < 1e-6 || error("the ratio of eigenvalues of an element of order $o is not a root of unity of that order")
        out[g] = k // o
    end
    return out
end

# the point stabilizer data of the line [v]: the elements fixing it, and the weight of each
function _stabilizer(act::ProjAction, v)
    S = Any[]
    for (g, M) in act.mats
        w = _mmul(M, v)
        _sameline(w, v) && push!(S, g)
    end
    return S
end

# the weight of g at the fixed line [v]: mu / lambda = det / lambda^2
function _tangent_weight(M, v)
    w = _mmul(M, v)
    k = abs(v[1]) > abs(v[2]) ? 1 : 2
    lam = w[k] / v[k]
    return (M[1, 1] * M[2, 2] - M[1, 2] * M[2, 1]) / lam^2
end

"""
    projective_line_class(act)

The class of the action on the projective line in `BC_1(G)`.

The argument is a `ProjAction`. Returns a `BCClass` of dimension one. For every orbit of points of `P^1` with
nontrivial stabilizer `S` (a cyclic group) it holds the symbol `(S, trivial, beta)` where `beta` is the character by which `S`
acts on the tangent line of the point, written for the generator of `S` with the largest order that the
function picks. In dimension one the class has only point symbols and no blowup relation, so it is a formal sum
over the orbits modulo conjugation (Proposition 5.1 of Tschinkel-Yang-Zhang, arXiv:2302.02296). The point
`[x0 : x1]` is the line spanned by `(x0, x1)` and the weight of `g` at a fixed point with `M v = lambda v` is
`det(M) / lambda^2`.

# Examples

```jldoctest
G = cyclic_group(PermGroup, 5)
M = [exp(2im * pi / 5) 0; 0 1]
cls = projective_line_class(ProjAction(G, [M]))
println(length(cls.terms))

# output

2
```
"""
function projective_line_class(act::ProjAction)
    G = act.G
    cls = BCClass(G, 1)
    elems = collect(keys(act.mats))
    # orbits of the points with nontrivial stabilizer, lines compared with a tolerance
    reps = Vector{ComplexF64}[]
    for g in elems
        isone(g) && continue
        for v in _eigenlines(act.mats[g])
            any(w -> _sameline(v, w), reps) && continue
            push!(reps, v)
        end
    end
    used = falses(length(reps))
    for i in eachindex(reps)
        used[i] && continue
        v = reps[i]
        for g in elems
            w = _mmul(act.mats[g], v)
            for j in eachindex(reps)
                _sameline(w, reps[j]) && (used[j] = true)
            end
        end
        S = _stabilizer(act, v)
        length(S) > 1 || continue
        h = S[argmax([Int(order(x)) for x in S])]
        o = Int(order(h))
        o == length(S) || error("the stabilizer of a point of the line is not cyclic")
        c = _expo(_tangent_weight(act.mats[h], v), o)
        c == 0 && error("a point stabilizer with trivial weight")
        push!(cls, BCSymbol(G, Any[h], Any[], [[c]]))
    end
    return cls
end
