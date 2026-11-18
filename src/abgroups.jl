# ---------------------------------------------------------------------------
# Finitely generated abelian groups, in the paper's (primary) notation
# ---------------------------------------------------------------------------

"""Z^free x prod (Z/q)^mult   with q running over prime powers."""
struct AbGroup
    free::Int
    pp::Dict{Int,Int}          # prime power q => multiplicity
end

AbGroup() = AbGroup(0, Dict{Int,Int}())

function prime_power_factors(n::Integer)
    out = Int[]
    m = Int(n)
    p = 2
    while p * p <= m
        if m % p == 0
            q = 1
            while m % p == 0
                m ÷= p; q *= p
            end
            push!(out, q)
        end
        p += 1
    end
    m > 1 && push!(out, m)
    return out
end

"""Build from a free rank and a list of invariant factors (each >1)."""
function AbGroup(free::Int, invariants::AbstractVector{<:Integer})
    pp = Dict{Int,Int}()
    for t in invariants, q in prime_power_factors(t)
        pp[q] = get(pp, q, 0) + 1
    end
    return AbGroup(free, pp)
end

function Base.:+(a::AbGroup, b::AbGroup)
    pp = copy(a.pp)
    for (q, m) in b.pp
        pp[q] = get(pp, q, 0) + m
    end
    return AbGroup(a.free + b.free, pp)
end

Base.:(==)(a::AbGroup, b::AbGroup) = a.free == b.free && a.pp == b.pp
Base.hash(a::AbGroup, h::UInt) = hash((a.free, a.pp), h)
Base.iszero(a::AbGroup) = a.free == 0 && isempty(a.pp)

function prime_of(q::Int)
    p = 2
    while q % p != 0
        p += 1
    end
    return p
end

"""Invariant-factor form  d_1 | d_2 | ... | d_k  (torsion part only)."""
function invariant_factors(a::AbGroup)
    byprime = Dict{Int,Vector{Int}}()
    for (q, m) in a.pp
        append!(get!(byprime, prime_of(q), Int[]), fill(q, m))
    end
    for v in values(byprime)
        sort!(v; rev=true)
    end
    k = isempty(byprime) ? 0 : maximum(length, values(byprime))
    inv = [prod((length(v) >= i ? v[i] : 1) for v in values(byprime); init=1) for i in 1:k]
    return sort(inv)
end

function format_ab(a::AbGroup; sep=" × ")
    iszero(a) && return "0"
    parts = String[]
    for q in sort(collect(keys(a.pp)); by=q -> (prime_of(q), q))
        m = a.pp[q]
        s = m == 1 ? "Z/$q" : "(Z/$q)^$m"
        push!(parts, s)
    end
    if a.free == 1
        push!(parts, "Z")
    elseif a.free > 1
        push!(parts, "Z^$(a.free)")
    end
    return join(parts, sep)
end

Base.show(io::IO, a::AbGroup) = print(io, format_ab(a))

"""Parse the paper's notation, e.g. ab("(Z/2)^6 x Z/4"), ab("Z^13 x (Z/2)^7"), ab("0")."""
function ab(s::AbstractString)
    s = strip(s)
    (s == "0" || s == "") && return AbGroup()
    free = 0
    pp = Dict{Int,Int}()
    for tok in split(s, r"\s*[x×]\s*")
        tok = strip(tok)
        if (m = match(r"^Z(?:\^(\d+))?$", tok)) !== nothing
            free += m.captures[1] === nothing ? 1 : parse(Int, m.captures[1])
        elseif (m = match(r"^\(?Z/(\d+)\)?(?:\^(\d+))?$", tok)) !== nothing
            n = parse(Int, m.captures[1])
            mult = m.captures[2] === nothing ? 1 : parse(Int, m.captures[2])
            for q in prime_power_factors(n)
                pp[q] = get(pp, q, 0) + mult
            end
        else
            error("cannot parse abelian-group token '$tok'")
        end
    end
    return AbGroup(free, pp)
end
