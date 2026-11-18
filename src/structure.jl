
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

npairs(st::BCStruct) = sum(length(h.pairs) for h in st.hclasses)

"""The underlying GAP group of an OSCAR group (or a raw GAP group, passed through)."""
gapobj(G::GAP.GapObj) = G
gapobj(G) = G.X

"""Group-theoretic part (GAP): classes [H,Y] and the Aut(H)-action of their stabilisers."""
function bc_structure(G; name::AbstractString="G")
    load_gap!()
    t = @elapsed raw = GAP.gap_to_julia(GAP.Globals.BCStructure(gapobj(G)); recursive=true)
    hcl = HClass[]
    for h in raw
        push!(hcl, HClass(h[:Hdesc], Int.(h[:d]), String.(h[:Hgens]), Int(h[:classsize]),
                          Int(h[:Csize]), Int(h[:Nsize]), h[:pairs]))
    end
    return BCStruct(String(name), Int(GAP.Globals.Size(gapobj(G))), hcl, t)
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

"""BC_n(G) via Theorem 5.2 from a precomputed `bc_structure`."""
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
