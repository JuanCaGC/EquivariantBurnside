
# ---------------------------------------------------------------------------
# Theorem 5.2 implementation
# ---------------------------------------------------------------------------

struct Summand
    Hdesc::String
    d::Vector{Int}
    Hgens::Vector{String}
    Ydesc::String
    Ysize::Int
    orbitsize::Int
    stabsize::Int
    autsize::Int                 # size of the image of N_G(H) n N_G(Y) in Aut(H)
    value::AbGroup               # B_n([H,Y])
end

struct HClass
    Hdesc::String
    d::Vector{Int}
    Hgens::Vector{String}
    classsize::Int
    Csize::Int
    Nsize::Int
    pairs::Vector{Dict{Symbol,Any}}
end

struct BCStruct
    name::String
    order::Int
    hclasses::Vector{HClass}
    gap_seconds::Float64
end

"""
    npairs(st)

Count the subgroup pair blocks in a structure.

The argument `st` is returned by `bc_structure`. Returns an integer counting its pairs.
"""
npairs(st::BCStruct) = sum(length(h.pairs) for h in st.hclasses)

"""
    gapobj(G)

Return the GAP object underlying a group.

The argument `G` is an OSCAR group or a raw GAP group. Raw GAP objects are returned unchanged.

The underlying GAP group of an OSCAR group (or a raw GAP group, passed through).
"""
gapobj(G::GAP.GapObj) = G
gapobj(G) = GAP.GapObj(G)

"""
    bc_structure_gap(G; name="G")

Compute the block structure through GAP.

The argument `G` is a finite OSCAR or GAP group and `name` labels the result. Returns a `BCStruct` for use with `bc`.

Compute classes [H,Y] using the retained GAP implementation. Accept OSCAR
permutation, polycyclic and matrix groups, or a raw GAP group.
The matrix rows satisfy h_j^g = prod_i h_i^M[j][i], with x^g = inv(g)*x*g.
Descriptions use GAP StructureDescription, or "order N" for Y of order > 2000.
"""
function bc_structure_gap(G; name::AbstractString="G")
    load_gap!()
    t = @elapsed raw = GAP.gap_to_julia(GAP.Globals.BCStructure(gapobj(G)); recursive=true)
    hcl = HClass[]
    for h in raw
        push!(hcl, HClass(h[:Hdesc], Int.(h[:d]), String.(h[:Hgens]), Int(h[:classsize]),
                          Int(h[:Csize]), Int(h[:Nsize]), h[:pairs]))
    end
    return BCStruct(String(name), Int(GAP.Globals.Size(gapobj(G))), hcl, t)
end

# GAP supplies coordinates in its independent cyclic factors. Wrapping the
# generators keeps conjugation and reconstruction in the OSCAR element API.
_independent_gens(H) = [Oscar.group_element(H, x) for x in GAP.Globals.IndependentGeneratorsOfAbelianGroup(gapobj(H))]

function _intermediate_groups(C, H)
    order(C) == order(H) && return [H]
    inter = GAP.Globals.IntermediateSubgroups(gapobj(C), gapobj(H))
    return vcat([H], [first(Oscar._as_subgroup(C, x)) for x in inter.subgroups], [C])
end

function _action_matrix(H, hs, g)
    # Row j stores h_j^g = prod_i h_i^M[j][i], where x^g = inv(g)*x*g.
    # Conjugation is performed on OSCAR elements, coordinates are supplied by GAP.
    return [Int.(GAP.gap_to_julia(GAP.Globals.IndependentGeneratorExponents(
                gapobj(H), GAP.GapObj(h^g)))) for h in hs]
end

function _record_structure_time!(timings, key, started)
    timings === nothing || (timings[key] = get(timings, key, 0.0) + (time_ns() - started) / 1.0e9)
    return nothing
end

function _structure_classes(G; timings=nothing)
    hcl = HClass[]
    started = time_ns()
    classes = subgroup_classes(G)
    _record_structure_time!(timings, :classes, started)
    for cl in classes
        H = representative(cl)
        order(H) > 1 && is_abelian(H) || continue
        started = time_ns()
        hs = _independent_gens(H)
        d = [order(Int, h) for h in hs]
        _record_structure_time!(timings, :generators, started)
        started = time_ns()
        C = first(centralizer(G, H))
        _record_structure_time!(timings, :centralizer, started)
        started = time_ns()
        N = first(normalizer(G, H))
        _record_structure_time!(timings, :normalizer, started)
        started = time_ns()
        Ys = _intermediate_groups(C, H)
        _record_structure_time!(timings, :intermediate, started)
        # GAP's subgroup orbit algorithm avoids repeatedly constructing subgroup
        # embeddings. Every orbit representative is wrapped back into OSCAR.
        started = time_ns()
        orbs = GAP.Globals.Orbits(gapobj(N), GAP.GapObj(gapobj.(Ys)), GAP.Globals.OnPoints)
        _record_structure_time!(timings, :orbits, started)
        pairs = Dict{Symbol,Any}[]
        for orb in orbs
            Y = first(Oscar._as_subgroup(C, orb[1]))
            started = time_ns()
            S = first(normalizer(N, Y))
            _record_structure_time!(timings, :stabilizer, started)
            started = time_ns()
            mats = Vector{Vector{Int}}[]
            for g in small_generating_set(S)
                M = _action_matrix(H, hs, g)
                any(M[j][i] != Int(i == j) for j in eachindex(d) for i in eachindex(d)) && push!(mats, M)
            end
            _record_structure_time!(timings, :matrices, started)
            started = time_ns()
            ysize = order(Int, Y)
            desc = ysize <= 2000 ? String(GAP.Globals.StructureDescription(gapobj(Y))) : "order $ysize"
            _record_structure_time!(timings, :descriptions, started)
            push!(pairs, Dict(:Ysize => ysize, :Ydesc => desc,
                              :orbitsize => length(orb), :stabsize => order(Int, S), :mats => mats))
        end
        started = time_ns()
        push!(hcl, HClass(String(GAP.Globals.StructureDescription(gapobj(H))), d,
                          [String(GAP.Globals.String(GAP.GapObj(h))) for h in hs],
                          div(order(Int, G), order(Int, N)), order(Int, C), order(Int, N), pairs))
        _record_structure_time!(timings, :descriptions, started)
    end
    return hcl
end

"""
    bc_structure(G; name="G")

Compute the group data needed for the block decomposition.

The argument `G` is a finite OSCAR or GAP group and `name` labels the result. Returns a `BCStruct`, reusable for different dimensions.

Compute the group theoretic data for Theorem 5.2 using OSCAR groups and elements.
Accept permutation, polycyclic and matrix groups. Raw GAP groups use the retained
`bc_structure_gap` route. GAP provides subgroup intervals, subgroup orbits,
independent cyclic coordinates and StructureDescription strings.

For each nontrivial abelian subgroup class H, enumerate the N_G(H)-orbits of
H <= Y <= C_G(H). For stabilizer generators g, matrix row j is defined by
h_j^g = prod_i h_i^M[j][i], with x^g = inv(g)*x*g. Identity matrices are omitted.
Y descriptions are "order N" when |Y| > 2000. The legacy `gap_seconds` field
records elapsed structure computation time, including the OSCAR operations.

# Examples

```jldoctest
st = bc_structure(symmetric_group(4))
println(bc(st, 2).total)

# output

(Z/2)^3
```
"""
function bc_structure(G; name::AbstractString="G")
    G isa GAP.GapObj && return bc_structure_gap(G; name)
    t = @elapsed hcl = _structure_classes(G)
    return BCStruct(String(name), order(Int, G), hcl, t)
end

_intmat(x) = Matrix{Int}(reduce(hcat, [Int.(r) for r in x])')

struct BCResult
    name::String
    n::Int
    total::AbGroup
    summands::Vector{Summand}
    seconds::Float64
    npairs::Int
end

function Base.show(io::IO, r::BCResult)
    print(io, "BC_$(r.n)($(r.name)) = ", r.total)
end

"""
    bc(G, n; name="G", kwargs...)
    bc(st, n; extra_vanishing=false, cache=Dict{Any,AbGroup}())

Compute the combinatorial Burnside group BC_n(G).

Pass a finite group `G` or a structure `st` and a positive integer dimension `n`. Returns a `BCResult` with the abelian group in `total`, the block contributions in `summands`, elapsed `seconds` and `npairs`. The optional `cache` stores block groups. The default `extra_vanishing=false` uses the defining relations. Setting it to true adds the zero-sum vanishing relations implemented by the engine.

BC_n(G) via Theorem 5.2 from a precomputed `bc_structure`.

# Examples

```jldoctest
println(bc(symmetric_group(4), 2).total)
println(bc(dihedral_group(PermGroup, 14), 3).total)

# output

(Z/2)^3
Z/2
```
"""
function bc(st::BCStruct, n::Int; extra_vanishing::Bool=false, cache=Dict{Any,AbGroup}())
    t0 = time()
    total = AbGroup()
    summands = Summand[]
    for h in st.hclasses
        ctx = CharCtx(h.d)
        # B_n(H) = 0 when n < (minimal number of generators of H^): nothing to enumerate
        for p in h.pairs
            perms = [char_perm(ctx, _intmat(M)) for M in p[:mats]]
            cl = perm_closure(perms)
            key = (h.d, n, cl === nothing ? sort(perms) : cl, extra_vanishing)
            val = get!(cache, key) do
                min_generators(h.d) > n ? AbGroup() : first(bn_quotient(h.d, n, cl === nothing ? perms : cl; extra_vanishing))
            end
            total += val
            push!(summands, Summand(h.Hdesc, h.d, h.Hgens, String(p[:Ydesc]), Int(p[:Ysize]),
                                    Int(p[:orbitsize]), Int(p[:stabsize]),
                                    cl === nothing ? -1 : length(cl) + (isempty(cl) ? 1 : 0), val))
        end
    end
    return BCResult(st.name, n, total, summands, time() - t0, npairs(st))
end

bc(G, n::Int; name::AbstractString="G", kwargs...) = bc(bc_structure(G; name), n; kwargs...)
