# The recursion of Kresch and Tschinkel for the class of P(V) (arXiv:2108.00518 Section 8), Phase 4.4.
#
# Conventions. A linear representation is a GAP matrix group G whose matrices M act on the coordinate columns of V^vee and on the
# points of V (rows) from the right, as in `dcp.jl`. The group is replaced by its image under `IsomorphismPermGroup`, a PermGroup
# of OSCAR, and all symbols are indexed symbols (`indexed.jl`) of that permutation group. The characters of a scalar subgroup are
# the eigenvalues of the matrices, as in `dcp.jl`.

const _GAPG = Oscar.GAP.Globals
const _rec_loaded = Ref(false)

function _rec_initialize!()
    _rec_loaded[] && return
    DCP.initialize!()
    Oscar.GAP.evalstr(raw"""
EB_CycExp := function(c, m)
  return Position(List([0..m-1], a->E(m)^a), c) - 1;
end;
EB_EigExps := function(M)
  local o, n, mult, j, k, s, ex, m;
  n := Length(M); o := Order(M); ex := [];
  for j in [0..o-1] do
    s := 0;
    for k in [0..o-1] do s := s + TraceMat(M^k) * E(o)^(-j*k); od;
    m := s / o;
    for k in [1..m] do Add(ex, j/o); od;
  od;
  return ex;
end;
EB_QuotMat := function(U, W, A)
  local B, v, r, s, T;
  B := ShallowCopy(U); r := Length(U);
  for v in W do
    if not DCP_Contains(B, [v]) then Add(B, v); fi;
  od;
  s := Length(B) - r;
  T := List(B, v -> SolutionMat(B, v*A));
  return ExtractSubMatrix(T, [r+1..r+s], [r+1..r+s]);
end;
""")
    _rec_loaded[] = true
end

"""
    LinearRepresentation

A finite group with a faithful linear representation `V^vee`, prepared for the recursion.

The field `P` is the permutation group (an OSCAR `PermGroup`) isomorphic to the matrix group, `mats` sends each element of `P` to its
matrix (a GAP object), `C` is the list of elements acting by scalars, and `arr` is the arrangement of `dcp.jl`. Build one with
`linrep(G)` where `G` is a GAP matrix group.
"""
struct LinearRepresentation
    G::Any
    arr::Any
    P::Any
    n::Int
    els::Vector{Any}
    mats::Dict{Any,Any}
    C::Vector{Any}
end

"""
    linrep(G)

Build the `LinearRepresentation` of a GAP matrix group `G` (a finite subgroup of `GL_n` over the cyclotomics, acting as in `dcp.jl`).
"""
function linrep(G)
    _rec_initialize!()
    arr = DCP.arrangement(G; projective = true)
    P = Oscar.PermGroup(arr.raw.P)
    els = Any[Oscar.group_element(P, x) for x in arr.raw.els]
    mats = Dict{Any,Any}(e => arr.raw.mats[i] for (i, e) in enumerate(els))
    id = _GAPG.IdentityMat(arr.dimension)
    C = Any[e for e in els if _GAPG.DCP_Scalar(id, mats[e]) != _GAPG.fail]
    return LinearRepresentation(G, arr, P, arr.dimension, els, mats, C)
end

"""
    projective_invariant(M)

The projective invariant of a GAP matrix `M` of finite order (Phase 4.6): the sorted list of the ratios of its eigenvalues, as
elements of `Q/Z` (a vector of `Rational{Int}` with values in `[0, 1)`).

The eigenvalue exponents are found from the traces of the powers of `M`. Multiplying `M` by a scalar does not change the result,
so it is an invariant of the image of `M` in `PGL`. It is the data stored in a `FieldFactor`.

# Examples

```jldoctest
M = Oscar.GAP.evalstr("[[1,0],[0,-1]]")
println(projective_invariant(M))

# output

Rational{Int64}[1//2, 1//2]
```
"""
function projective_invariant(M)
    _rec_initialize!()
    ex = Rational{Int}[Int(_GAPG.NumeratorRat(x)) // Int(_GAPG.DenominatorRat(x)) for x in _GAPG.EB_EigExps(M)]
    return sort!(Rational{Int}[_m1(a - b) for (i, a) in enumerate(ex) for (j, b) in enumerate(ex) if i != j])
end

# the eigenvalue of a scalar element as an element of Q/Z
function _scalar_char(rep::LinearRepresentation, g)
    m = Int(Oscar.order(g))
    c = _GAPG.DCP_Scalar(_GAPG.IdentityMat(rep.n), rep.mats[g])
    a = Int(_GAPG.EB_CycExp(c, m))
    return _m1(a // m)
end

# an element of P from a GAP matrix of G
_matrix_to_element(rep::LinearRepresentation, M) = Oscar.group_element(rep.P, _GAPG.Image(rep.arr.raw.iso, M))

"""
    generic_symbol_class(rep)

The class with the single generic term `(C in C, G/C acting on k(P(V)), (), epsilon)` of Proposition 8.3 for the representation `rep`.
"""
function _generic_class(rep::LinearRepresentation; fields::Bool = false)
    P = rep.P
    cls = IndexedClass(P, rep.n, [0])
    eps = Dict{Any,Rational{Int}}(g => _scalar_char(rep, g) for g in rep.C)
    F = Any[]
    if fields && rep.n >= 2
        F = Any[FieldFactor(rep.n, Dict{Any,Vector{Rational{Int}}}(g => projective_invariant(rep.mats[g]) for g in rep.els))]
    end
    push!(cls, IndexedSymbol(P, rep.C, rep.C, Any[g for g in Oscar.gens(P)], rep.n - 1, Dict{Any,Rational{Int}}[], Dict(0 => eps); field = F))
    return cls
end

"""
    indexed_difference(cls)

The transformation of Convention 8.1 on the characters `gamma_0, ..., gamma_t` of an indexed class with the index set `{0,...,t}`:
`gamma_0` is unchanged and `gamma_i` is replaced by `gamma_i - gamma_{i-1}`, the characters of the sequence `O(-1)`, `O(1) tensor O(-1)`, ...
Returns an `IndexedClass` with the same index set. The map on characters is invertible, so the symbols stay valid.
"""
function indexed_difference(cls::IndexedClass)
    cls.I == collect(0:(length(cls.I) - 1)) || throw(ArgumentError("the index set must be {0,...,t}"))
    out = IndexedClass(cls.G, cls.n, cls.I, cls.elems, cls.idx, Dict{Any,Tuple{Int,IndexedSymbol}}())
    for (_, (coef, s)) in cls.terms
        gm = Dict{Int,Dict{Any,Rational{Int}}}()
        for i in cls.I
            if i == 0
                gm[0] = s.gamma[0]
            else
                gm[i] = Dict{Any,Rational{Int}}(a => _m1(s.gamma[i][a] - s.gamma[i - 1][a]) for a in s.A)
            end
        end
        push!(out, coef, IndexedSymbol(s.G, s.H, s.A, s.Y, s.d, s.beta, gm, s.F, Val(:raw)))
    end
    return out
end

"""
    indexed_product(classes)

The product of several indexed classes with pairwise disjoint index sets in the direct product of their groups. Returns
`(cls, P, embs)` where `embs[i]` embeds the group of `classes[i]` in `P`.
"""
function indexed_product(classes::Vector{IndexedClass})
    isempty(classes) && throw(ArgumentError("no classes to multiply"))
    allI = vcat([c.I for c in classes]...)
    length(unique(allI)) == length(allI) || throw(ArgumentError("the index sets of the classes must be disjoint"))
    P = Oscar.direct_product([c.G for c in classes]...)
    embs = [Oscar.embedding(P, i) for i in eachindex(classes)]
    out = IndexedClass(P, sum(c.n for c in classes), sort!(allI))
    termlists = [collect(values(c.terms)) for c in classes]
    for combo in Iterators.product(termlists...)
        coef = prod(t[1] for t in combo)
        syms = [t[2] for t in combo]
        prodset(sets) = vec(Any[prod(embs[k](x) for (k, x) in enumerate(tup)) for tup in Iterators.product(sets...)])
        H = prodset([s.H for s in syms])
        A = prodset([s.A for s in syms])
        Y = prodset([s.Y for s in syms])
        function extend(k, c)
            D = Dict{Any,Rational{Int}}()
            for tup in Iterators.product((s.A for s in syms)...)
                D[prod(embs[j](x) for (j, x) in enumerate(tup))] = c[tup[k]]
            end
            return D
        end
        beta = Dict{Any,Rational{Int}}[]
        gm = Dict{Int,Dict{Any,Rational{Int}}}()
        for (k, s) in enumerate(syms)
            for c in s.beta
                push!(beta, extend(k, c))
            end
            for (i, c) in s.gamma
                gm[i] = extend(k, c)
            end
        end
        F = Any[]
        for (k, s) in enumerate(syms), x in s.F
            D = Dict{Any,Vector{Rational{Int}}}()
            for tup in Iterators.product((s2.Y for s2 in syms)...)
                D[prod(embs[j](y) for (j, y) in enumerate(tup))] = x.inv[tup[k]]
            end
            push!(F, FieldFactor(x.dim, D))
        end
        push!(out, coef, IndexedSymbol(P, H, A, Y, sum(s.d for s in syms), beta, gm, F, Val(:raw)))
    end
    return out, P, embs
end

# matrix of the action of the group element with matrix M on the piece (W modulo U)
_piece_matrix(U, W, M) = _GAPG.EB_QuotMat(U, W, M)

"""
    chain_class(rep, cd)

The class `[P(V_1) x P(V_2/V_1) x ... x P(V/V_t) with N](O(-1))` of equation (8.5) of KT-repr for the chain `cd` of `rep`
(an element of `DCP.chains(rep.arr)`), which equals `[D_Lambda with N](O(-1))` by Lemma 8.2.

Returns `(cls, NO, embN)` with `cls` an `IndexedClass` of the group `NO`, the subgroup `N = N_G(Lambda)` of `rep.P`, with the index
set `{0,...,t}`, and `embN` the embedding of `NO` in `rep.P`. The graded piece `V_{i+1}/V_i` carries the image of `N` in its general
linear group, the class of its projective space is computed by `projective_class` recursively, the classes are multiplied,
restricted to the image of `N` in the product (an injective map) and the characters are transformed by Convention 8.1.
"""
function chain_class(rep::LinearRepresentation, cd; fields::Bool = false)
    P = rep.P
    t = length(cd.indices)
    iso = rep.arr.raw.iso
    Nperm = _GAPG.Image(iso, cd.normalizer)
    Nel = Any[Oscar.group_element(P, x) for x in _GAPG.AsSSortedList(Nperm)]
    Ngens = Any[Oscar.group_element(P, x) for x in _GAPG.GeneratorsOfGroup(Nperm)]
    isempty(Ngens) && (Ngens = Any[one(P)])
    NO, embN = Oscar.sub(P, elem_type(P)[g for g in Ngens])
    spaces = vcat(cd.subspaces, [_GAPG.IdentityMat(rep.n)])
    classes = IndexedClass[]
    subreps = LinearRepresentation[]
    phis = Vector{Dict{Any,Any}}()
    for i in 0:t
        U = i == 0 ? Oscar.GAP.GapObj([]) : spaces[i]
        W = spaces[i + 1]
        Qs(g) = _piece_matrix(U, W, rep.mats[g])
        d = Int(_GAPG.Length(W)) - Int(_GAPG.Length(U))
        gens_ = [Qs(g) for g in Ngens]
        Gi = _GAPG.Group(Oscar.GAP.GapObj(gens_))
        ri = linrep(Gi)
        cls_i = projective_class(ri; fields = fields)
        push!(classes, indexed_reindex(cls_i, [i]))
        push!(subreps, ri)
        push!(phis, Dict{Any,Any}(g => _matrix_to_element(ri, Qs(g)) for g in Nel))
    end
    prodcls, Pi, embs = indexed_product(classes)
    psi(g) = prod(embs[i + 1](phis[i + 1][g]) for i in 0:t)
    Limg = Dict{Any,Any}(psi(g) => g for g in Nel)
    length(Limg) == length(Nel) || error("the map from N to the product of the images is not injective")
    resL, L, embL = indexed_restrict(prodcls, Any[psi(g) for g in Ngens])
    nodict = Dict{Any,Any}(g => Oscar.preimage(embN, g) for g in Nel)
    f(l) = nodict[Limg[embL(l)]]
    out = IndexedClass(NO, rep.n, collect(0:t))
    mv(c) = Dict{Any,Rational{Int}}(f(a) => v for (a, v) in c)
    for (_, (coef, s)) in resL.terms
        push!(out, coef, IndexedSymbol(NO, Any[f(x) for x in s.H], Any[f(x) for x in s.A], Any[f(x) for x in s.Y], s.d,
            Dict{Any,Rational{Int}}[mv(c) for c in s.beta], Dict(i => mv(c) for (i, c) in s.gamma), _move_field(s.F, f), Val(:raw)))
    end
    return indexed_difference(out), NO, embN
end

# data to enumerate the flags and to move a flag to the representative of its G-orbit chosen by `DCP.chains`
function _flag_data(rep::LinearRepresentation, chs)
    flags = DCP.all_flags(rep.arr)
    lookup = DCP.entry_lookup(rep.arr)
    gP = Any[g for g in Oscar.gens(rep.P)]
    perms = [DCP.entry_action(rep.arr, lookup, rep.mats[g]) for g in gP]
    rep_of = Dict{Vector{Int},Tuple{Int,Any}}()
    for (k, cd) in enumerate(chs)
        f0 = Vector{Int}(cd.indices)
        rep_of[f0] = (k, one(rep.P))
        queue = [f0]
        while !isempty(queue)
            q = popfirst!(queue)
            hq = rep_of[q][2]
            for (gi, g) in enumerate(gP)
                z = Int[perms[gi][x] for x in q]
                if !haskey(rep_of, z)
                    rep_of[z] = (k, hq * g)
                    push!(queue, z)
                end
            end
        end
    end
    return flags, lookup, rep_of
end

"""
    projective_class(rep)

The class `[P(V) with G](O_{P(V)}(-1))` in `Burn_{n,{0}}(G)` of Proposition 8.3 and Theorem 8.4 of KT-repr, an `IndexedClass` of
`rep.P` with the index set `{0}`.

It is the generic term plus the sum over the chains `Lambda` modulo `G` (from `DCP.chains`) of `ind psi_{{0..t},{0}}` of the class
`[D_Lambda^o with N]^naive`. The latter is `chain_class` minus, over the `N`-orbits of flags `Lambda'` strictly containing `Lambda`,
the induction from `N_G(Lambda')` to `N` of `psi_{I,J} tau_{I,J}` of the already computed class of `Lambda'`, where `J` is `0`
together with the positions of the members of `Lambda` in `Lambda'`. Chains are processed from the longest to the shortest, a
flag `Lambda' = Lambda'_0 h` of the representative `Lambda'_0` uses the class of `Lambda'_0` transported by `x -> x^h`.
Relations are not applied, the result is a formal sum.
"""
function projective_class(rep::LinearRepresentation; fields::Bool = false)
    cls = _generic_class(rep; fields = fields)
    chs = DCP.chains(rep.arr)
    isempty(chs) && return cls
    flags, lookup, rep_of = _flag_data(rep, chs)
    P = rep.P
    naive = Dict{Int,Tuple{IndexedClass,Any,Any}}()
    for k in sortperm([length(cd.indices) for cd in chs]; rev = true)
        cd = chs[k]
        f = Vector{Int}(cd.indices)
        t = length(f)
        c, NO, embN = chain_class(rep, cd; fields = fields)
        Ngens = Any[embN(g) for g in Oscar.gens(NO)]
        nperms = [DCP.entry_action(rep.arr, lookup, rep.mats[g]) for g in Ngens]
        longer = [fl for fl in flags if length(fl) > t && all(x in fl for x in f)]
        seen = Set{Vector{Int}}()
        for fl in longer
            fl in seen && continue
            queue = [fl]
            push!(seen, fl)
            while !isempty(queue)
                q = popfirst!(queue)
                for pm in nperms
                    z = Int[pm[x] for x in q]
                    if !(z in seen)
                        push!(seen, z)
                        push!(queue, z)
                    end
                end
            end
            k2, h = rep_of[fl]
            c2, NO2, embN2 = naive[k2]
            J = vcat([0], [findfirst(==(x), fl) for x in f])
            c3 = indexed_reindex(indexed_psi(indexed_tau(c2, J), J), collect(0:t))
            contribution = indexed_induce(c3, NO, x -> Oscar.preimage(embN, embN2(x)^h))
            c = c + (-1) * contribution
        end
        naive[k] = (c, NO, embN)
    end
    for k in eachindex(chs)
        c, NO, embN = naive[k]
        cls = cls + indexed_induce(indexed_psi(c, [0]), P, embN)
    end
    return cls
end

"""
    indexed_negate_gamma(cls)

The class obtained by replacing every character of `gamma` by its negative. For the class of `P(V)` this passes from the line
bundle `O(-1)` to `O(1)` (the characters of the dual line bundle), as used in Theorem 8.5 of KT-repr.
"""
function indexed_negate_gamma(cls::IndexedClass)
    out = IndexedClass(cls.G, cls.n, cls.I, cls.elems, cls.idx, Dict{Any,Tuple{Int,IndexedSymbol}}())
    for (_, (coef, s)) in cls.terms
        gm = Dict{Int,Dict{Any,Rational{Int}}}(i => Dict{Any,Rational{Int}}(a => _m1(-v) for (a, v) in c) for (i, c) in s.gamma)
        push!(out, coef, IndexedSymbol(s.G, s.H, s.A, s.Y, s.d, s.beta, gm, s.F, Val(:raw)))
    end
    return out
end

"""
    affine_class(rep)

The class `[V with G]^naive` of Theorem 8.5 of KT-repr, `omega_{0} + psi_{0}` applied to `[P(V) with G](O(-1))`, an `IndexedClass`
of dimension `n` with the empty index set. Relations are not applied.
"""
function affine_class(rep::LinearRepresentation)
    c = projective_class(rep)
    return indexed_omega(c, Int[]) + indexed_psi(c, Int[])
end

"""
    projective_plus_class(rep)

The class `[P(1 + V) with G]` of Theorem 8.5 of KT-repr, `omega_{0}[P(V)](O(-1)) + psi_{0}[P(V)](O(-1)) + psi_{0}[P(V)](O(1))`, an
`IndexedClass` of dimension `n` with the empty index set. The group acts faithfully on `P(1 + V)` when it acts faithfully on `V`.
"""
function projective_plus_class(rep::LinearRepresentation)
    c = projective_class(rep)
    return indexed_omega(c, Int[]) + indexed_psi(c, Int[]) + indexed_psi(indexed_negate_gamma(c), Int[])
end

"""
    projective_bc_class(rep)

The image in `BC_{n-1}(G/C)` of `[P(V) with G/C]`, which is `eta_{0}` of `projective_class(rep)` (Theorem 8.5), as `(cls, Q, proj)`:
a `BCClass` of the quotient group `Q = G/C` (the group itself when the scalar subgroup `C` is trivial) and the quotient map.
"""
function projective_bc_class(rep::LinearRepresentation)
    out, Q, proj, _ = indexed_eta(projective_class(rep), rep.C)
    return out, Q, proj
end

"""
    projective_plus_bc_class(rep)

The image in `BC_n(G)` of `[P(1 + V) with G]` as a `BCClass` of `rep.P`, from `projective_plus_class`.
"""
function projective_plus_bc_class(rep::LinearRepresentation)
    out, _, _, _ = indexed_eta(projective_plus_class(rep), Any[])
    return out
end


"""
    field_fingerprint(cls)

The fingerprint of an indexed class that carries the field datum (build it with `projective_class(rep; fields = true)`).

Returns a sorted vector of pairs `key => coefficient`, where `key` is the tuple `(h, a, y, d, I, betas, gammas, factors)` with the
orders `|H|`, `|A|`, `|Y~|`, the transcendence degree `d`, the index set, the sorted orders of the characters of `beta`, the orders of
the characters of `gamma` (as pairs `(index, order)`), and the sorted list of triples `(dim W_j, |image of Y~ in PGL(W_j)|, |kernel|)`
over the factors `k(P(W_j))` of the field. Coefficients of equal keys are added and zero totals are dropped. This is a coarse
invariant (orders only), meant for comparisons and counting, not a decision of equality of symbols.
"""
function field_fingerprint(cls::IndexedClass)
    ordchar(ch) = foldl(lcm, (denominator(v) for v in values(ch)); init = 1)
    out = Dict{Any,Int}()
    for (_, (c, s)) in cls.terms
        facs = sort!([(x.dim, length(s.Y) ÷ length(_factor_kernel(x)), length(_factor_kernel(x))) for x in s.F])
        key = (length(s.H), length(s.A), length(s.Y), s.d, Tuple(cls.I), Tuple(sort([ordchar(b) for b in s.beta])),
               Tuple(sort([(j, ordchar(g)) for (j, g) in s.gamma])), Tuple(facs))
        out[key] = get(out, key, 0) + c
    end
    return sort!(collect(filter(kv -> kv[2] != 0, out)); by = string)
end

"""
    field_faithful(cls)

Whether, for every symbol of `cls`, the intersection of the kernels of the actions on the factors of its field datum is exactly `A`
(so that `Y~/A` acts faithfully on the field) and `A` lies in every kernel. Returns `(ok, terms_without_factor, max_factors)`.
"""
function field_faithful(cls::IndexedClass)
    ok = true
    nofac = 0
    maxf = 0
    for (_, (_, s)) in cls.terms
        if isempty(s.F)
            nofac += 1
            ok &= length(s.A) == length(s.Y)
        else
            K = reduce(intersect, (_factor_kernel(x) for x in s.F))
            ok &= K == Set(s.Y[findall(in(Set(s.A)), s.Y)]) && Set(s.A) <= K
        end
        maxf = max(maxf, length(s.F))
    end
    return ok, nofac, maxf
end
