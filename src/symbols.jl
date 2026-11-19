# ---------------------------------------------------------------------------
# Symbols, classes and their images in BC_n(G)  (work package 1.2)
#
# Conventions, see handoff/SPEC_FASE1_2_1_3.md section 1.
#  C1 A character beta of H = <h_1> x ... x <h_k> is given by integers c with
#     beta(h_j) = exp(2 pi i c_j / ord(h_j)).
#  C2 Y is a subgroup of Z_G(H)/H in the papers of Kresch-Tschinkel and EBGLA, the engine uses the
#     preimage Y~ with H <= Y~ <= Z_G(H).  `BCSymbol` takes lifts of generators of Y, so Y~ = <H, ygens>.
#     `BCSymbol_preimage` takes generators of Y~ itself and checks that they contain H.
#  C3 A block [H,Y] is named by a `BlockKey`, never by an index of the GAP enumeration.
#  C4 Raw coordinates of a `BCElement` live in the Smith basis chosen by the engine.  Compare elements
#     with `==`, `is_zero`, `order`, or exchange them through certificates.
# ---------------------------------------------------------------------------

_gap_el(x) = x isa GAP.GapObj ? x : GAP.GapObj(x)

function _ensure_prepared!(Gg)
    bcclass_init!()
    p = _prepared[]
    (p !== nothing && GAP.Globals.IsIdenticalObj(p, Gg)) || prepare!(Gg)
    return nothing
end

_same_group(a, b) = GAP.Globals.IsIdenticalObj(a, b)

"""
    BlockKey

Name of a block `[H,Y]` of Theorem 5.2: the GAP structure descriptions of the representative H and of
the preimage Y~, the orders `d` of the independent generators of H, `ysize = |Y~|`, the size of the
`N_G(H)` orbit of Y~, and `rank`, the 1-based rank among blocks with identical other entries in the
enumeration order of the engine (it is 1 unless two blocks share every other invariant).
"""
struct BlockKey
    hdesc::String
    d::Vector{Int}
    ydesc::String
    ysize::Int
    orbitsize::Int
    rank::Int
end
Base.:(==)(a::BlockKey, b::BlockKey) = a.hdesc == b.hdesc && a.d == b.d && a.ydesc == b.ydesc &&
    a.ysize == b.ysize && a.orbitsize == b.orbitsize && a.rank == b.rank
Base.hash(a::BlockKey, h::UInt) = hash((a.hdesc, a.d, a.ydesc, a.ysize, a.orbitsize, a.rank), h)
Base.show(io::IO, k::BlockKey) = print(io, "[H=", k.hdesc, ", d=", k.d, ", Y=", k.ydesc, ", |Y|=", k.ysize,
                                       ", orbit=", k.orbitsize, k.rank == 1 ? "" : ", rank=$(k.rank)", "]")

struct BlockInfo
    key::BlockKey
    hgens::Vector{String}      # independent generators of the representative H, GAP strings
    ygens::Vector{String}      # generators of the representative Y~, GAP strings
end

# Table of block names of the currently prepared group, built once per `prepare!`.
function _blocktable()
    _block_table[] === nothing || return _block_table[]
    counts = GAP.gap_to_julia(GAP.Globals.BCNumBlocks(); recursive=true)
    seen = Dict{Tuple,Int}()
    tab = Vector{Vector{BlockInfo}}()
    for (b, np) in enumerate(counts)
        row = BlockInfo[]
        for p in 1:np
            r = GAP.gap_to_julia(GAP.Globals.BCBlockInfo(b, p); recursive=true)
            sig = (String(r[:Hdesc]), Int.(r[:d]), String(r[:Ydesc]), Int(r[:Ysize]), Int(r[:orbitsize]))
            rank = seen[sig] = get(seen, sig, 0) + 1
            push!(row, BlockInfo(BlockKey(sig..., rank), String.(r[:Hgens]), String.(r[:Ygens])))
        end
        push!(tab, row)
    end
    _block_table[] = tab
    return tab
end

# ----------------------------------------------------------------------------- symbols

"""
    BCSymbol(G, hgens, ygens, betas)

The symbol `(H, Y, beta)` of the combinatorial Burnside group BC_n(G), in the quotient convention of
the papers (Y is a subgroup of Z_G(H)/H).

- `G` is an OSCAR group (permutation, polycyclic or matrix group) or a raw GAP group.
- `hgens` are independent generators h_1..h_k of the abelian subgroup H, elements of G
  (OSCAR elements, or GAP elements when G is a raw GAP group).
- `ygens` are elements of Z_G(H) whose images in Z_G(H)/H generate Y. Internally Y~ = <H, ygens>.
  An empty list means Y trivial.
- `betas` are the characters of H as integer vectors c with `beta(h_j) = exp(2 pi i c_j / ord(h_j))`.
  They must be nonzero and, together, generate the dual of H. The count bound `length <= n` is checked
  when the symbol is added to a `BCClass(G, n)`.

Throws `ArgumentError` for a trivial or non abelian H, dependent generators, a `ygens` element that does
not centralize H, and wrongly sized or zero characters.
"""
struct BCSymbol
    G::Any
    Ggap::Any
    hg::Vector{Any}
    yg::Vector{Any}
    ords::Vector{Int}
    betas::Vector{Vector{Int}}
end

function _bcsymbol(G, hgens, ygens, betas, preimage::Bool)
    Gg = gapobj(G)
    hg = Any[_gap_el(x) for x in hgens]
    yg = Any[_gap_el(x) for x in ygens]
    for x in vcat(hg, yg)
        GAP.Globals.IN(x, Gg) || throw(ArgumentError("generator $(GAP.Globals.String(x)) is not an element of G"))
    end
    isempty(hg) && throw(ArgumentError("H is trivial: give at least one nontrivial generator"))
    Hs = GAP.Globals.Subgroup(Gg, GAP.GapObj(hg))
    Int(GAP.Globals.Size(Hs)) == 1 && throw(ArgumentError("H is trivial: all generators are the identity"))
    GAP.Globals.IsAbelian(Hs) || throw(ArgumentError("H is not abelian"))
    ords = [Int(GAP.Globals.Order(h)) for h in hg]
    prod(ords) == Int(GAP.Globals.Size(Hs)) ||
        throw(ArgumentError("the generators of H are not independent: |H| = $(Int(GAP.Globals.Size(Hs))) but the product of their orders is $(prod(ords))"))
    for y in yg, h in hg
        GAP.Globals.IsOne(GAP.Globals.Comm(y, h)) ||
            throw(ArgumentError("generator $(GAP.Globals.String(y)) of Y does not centralize H"))
    end
    if preimage
        Ys = GAP.Globals.Subgroup(Gg, GAP.GapObj(yg))
        GAP.Globals.IsSubgroup(Ys, Hs) || throw(ArgumentError("the subgroup generated by ygens does not contain H"))
    end
    bs = Vector{Int}[]
    for c in betas
        length(c) == length(hg) || throw(ArgumentError("a character has the wrong number of coordinates: expected $(length(hg)), got $(length(c))"))
        r = [mod(Int(c[j]), ords[j]) for j in eachindex(ords)]
        all(==(0), r) && throw(ArgumentError("a character is the zero character: symbols carry nonzero characters"))
        push!(bs, r)
    end
    return BCSymbol(G, Gg, hg, yg, ords, bs)
end

BCSymbol(G, hgens, ygens, betas) = _bcsymbol(G, hgens, ygens, betas, false)

"""
    BCSymbol_preimage(G, hgens, ygens, betas)

Like `BCSymbol`, but `ygens` generate the preimage Y~ of Y in Z_G(H) (the convention of
Tschinkel-Yang-Zhang), so they must contain H. The result is the same object as the quotient form
`BCSymbol(G, hgens, ygens, betas)` since Y~ = <H, ygens> in both.
"""
BCSymbol_preimage(G, hgens, ygens, betas) = _bcsymbol(G, hgens, ygens, betas, true)

function Base.show(io::IO, s::BCSymbol)
    gs(v) = join((String(GAP.Globals.String(x)) for x in v), ", ")
    print(io, "BCSymbol(H=<", gs(s.hg), ">, Y=<H, ", gs(s.yg), ">, betas=", s.betas, ")")
end

# ----------------------------------------------------------------------------- classes

"""
    BCClass(G, n)

A formal integer combination of symbols of `G`, to be mapped into BC_n(G) by `bc_image`.
Use `push!(cls, sym)`, `push!(cls, coef, sym)`, `cls + sym`, `cls - sym`, `cls + cls2`, `c * cls`, `-cls`.
Adding a symbol checks that it belongs to the same group, that it carries at most `n` characters and that
they generate the dual of H.
"""
mutable struct BCClass
    G::Any
    Ggap::Any
    n::Int
    terms::Vector{Tuple{Int,BCSymbol}}
end

function BCClass(G, n::Integer)
    n >= 1 || throw(ArgumentError("n must be positive"))
    return BCClass(G, gapobj(G), Int(n), Tuple{Int,BCSymbol}[])
end

function Base.push!(cls::BCClass, coef::Integer, s::BCSymbol)
    _same_group(cls.Ggap, s.Ggap) || throw(ArgumentError("the symbol belongs to a different group than the class"))
    length(s.betas) <= cls.n || throw(ArgumentError("more characters than n: $(length(s.betas)) characters for n = $(cls.n)"))
    ctx = CharCtx(s.ords)
    generates_all(ctx, [encode(ctx, c) for c in s.betas]) ||
        throw(ArgumentError("the characters do not generate the dual of H"))
    push!(cls.terms, (Int(coef), s))
    return cls
end
Base.push!(cls::BCClass, s::BCSymbol) = push!(cls, 1, s)

Base.copy(cls::BCClass) = BCClass(cls.G, cls.Ggap, cls.n, copy(cls.terms))
Base.:+(cls::BCClass, s::BCSymbol) = push!(copy(cls), 1, s)
Base.:-(cls::BCClass, s::BCSymbol) = push!(copy(cls), -1, s)
function Base.:+(a::BCClass, b::BCClass)
    _same_group(a.Ggap, b.Ggap) || throw(ArgumentError("the classes belong to a different group"))
    a.n == b.n || throw(ArgumentError("the classes have a different n"))
    return BCClass(a.G, a.Ggap, a.n, vcat(a.terms, b.terms))
end
Base.:*(c::Integer, cls::BCClass) = BCClass(cls.G, cls.Ggap, cls.n, [(Int(c) * t[1], t[2]) for t in cls.terms])
Base.:-(cls::BCClass) = (-1) * cls
Base.:-(a::BCClass, b::BCClass) = a + (-b)

function Base.show(io::IO, cls::BCClass)
    print(io, "BCClass(n=$(cls.n), $(length(cls.terms)) terms)")
end

# ----------------------------------------------------------------------------- elements

struct BlockData
    coords::Vector{Int}                        # reduced Smith coordinates
    moduli::Vector{Int}                        # 0 means a free coordinate
    classvec::Dict{Vector{Int},Int}            # generator key (sorted character indices) => coefficient
    bm::BlockMaps
    d::Vector{Int}
    perms::Vector{Vector{Int}}                 # generators of the action of N_G(H) n N_G(Y) on character indices
    info::BlockInfo
end

"""
    BCElement

An element of BC_n(G), stored block by block (only blocks with a nonzero component). Raw coordinates are
in the Smith basis chosen by the engine and are comparable only between elements produced by the same
version of the package. Use `==`, `is_zero`, `order`, `+`, `-`, `c * x`, or certificates.
"""
struct BCElement
    G::Any
    Ggap::Any
    n::Int
    blocks::Dict{BlockKey,BlockData}
    terms::Vector{String}                      # audit trail only
end

_reduce(c, m) = [m[j] == 0 ? c[j] : mod(c[j], m[j]) for j in eachindex(c)]

"""Block keys with a nonzero component, sorted for reproducibility."""
bc_blocks(x::BCElement) = sort!(collect(keys(x.blocks)); by = string)

function _term_string(coef, s::BCSymbol)
    gs(v) = join((String(GAP.Globals.String(h)) for h in v), " ")
    return "$(coef) H<$(gs(s.hg))> Y<$(gs(s.yg))> betas=$(s.betas)"
end

"""
    bc_image(cls) -> BCElement

The image in BC_n(G) of a class given as an integer combination of symbols, block by block.
"""
function bc_image(cls::BCClass)
    Gg = cls.Ggap
    _ensure_prepared!(Gg)
    n = cls.n
    acc = Dict{Tuple{Int,Int},Vector{Int}}()
    bms = Dict{Tuple{Int,Int},BlockMaps}()
    cvec = Dict{Tuple{Int,Int},Dict{Vector{Int},Int}}()
    for (coef, s) in cls.terms
        coef == 0 && continue
        b, p, v, bm, key = symbol_image(Gg, n, s.hg, s.yg, s.betas)
        w = get!(acc, (b, p), zeros(Int, length(v)))
        w .+= coef .* v
        bms[(b, p)] = bm
        cv = get!(cvec, (b, p), Dict{Vector{Int},Int}())
        cv[key] = get(cv, key, 0) + coef
    end
    tab = _blocktable()
    blks = Dict{BlockKey,BlockData}()
    for ((b, p), w) in acc
        bm = bms[(b, p)]
        coords = _reduce(w, bm.moduli)
        all(==(0), coords) && continue
        info = tab[b][p]
        ctx = CharCtx(bm.d)
        mats = GAP.gap_to_julia(GAP.Globals.BCInfo(b); recursive=true)[:mats][p]
        perms = [char_perm(ctx, _intmat(M)) for M in mats]
        blks[info.key] = BlockData(coords, bm.moduli, filter!(kv -> kv[2] != 0, cvec[(b, p)]), bm, bm.d, perms, info)
    end
    return BCElement(cls.G, Gg, n, blks, [_term_string(c, s) for (c, s) in cls.terms if c != 0])
end

function bc_image(s::BCSymbol, n::Integer)
    cls = BCClass(s.G, n)
    push!(cls, s)
    return bc_image(cls)
end

Base.iszero(x::BCElement) = isempty(x.blocks)

function _combine(x::BCElement, y::BCElement, sy::Int)
    _same_group(x.Ggap, y.Ggap) || throw(ArgumentError("the elements belong to a different group"))
    x.n == y.n || throw(ArgumentError("the elements have a different n"))
    out = Dict{BlockKey,BlockData}()
    for k in union(keys(x.blocks), keys(y.blocks))
        a = get(x.blocks, k, nothing); b = get(y.blocks, k, nothing)
        base = a === nothing ? b : a
        m = base.moduli
        ca = a === nothing ? zeros(Int, length(m)) : a.coords
        cb = b === nothing ? zeros(Int, length(m)) : b.coords
        coords = _reduce(ca .+ sy .* cb, m)
        all(==(0), coords) && continue
        cv = Dict{Vector{Int},Int}()
        a === nothing || for (kk, c) in a.classvec; cv[kk] = get(cv, kk, 0) + c; end
        b === nothing || for (kk, c) in b.classvec; cv[kk] = get(cv, kk, 0) + sy * c; end
        out[k] = BlockData(coords, m, filter!(kv -> kv[2] != 0, cv), base.bm, base.d, base.perms, base.info)
    end
    terms = sy == 1 ? vcat(x.terms, y.terms) : vcat(x.terms, ["-1 * [" * join(y.terms, " + ") * "]"])
    return BCElement(x.G, x.Ggap, x.n, out, terms)
end
Base.:+(x::BCElement, y::BCElement) = _combine(x, y, 1)
Base.:-(x::BCElement, y::BCElement) = _combine(x, y, -1)
function Base.:*(c::Integer, x::BCElement)
    out = Dict{BlockKey,BlockData}()
    for (k, a) in x.blocks
        coords = _reduce(Int(c) .* a.coords, a.moduli)
        all(==(0), coords) && continue
        out[k] = BlockData(coords, a.moduli, filter!(kv -> kv[2] != 0, Dict(kk => Int(c) * v for (kk, v) in a.classvec)),
                           a.bm, a.d, a.perms, a.info)
    end
    return BCElement(x.G, x.Ggap, x.n, out, ["$(c) * [" * join(x.terms, " + ") * "]"])
end
Base.:-(x::BCElement) = (-1) * x

function Base.:(==)(x::BCElement, y::BCElement)
    _same_group(x.Ggap, y.Ggap) && x.n == y.n || return false
    keys(x.blocks) == keys(y.blocks) || return false
    return all(x.blocks[k].coords == y.blocks[k].coords for k in keys(x.blocks))
end
Base.hash(x::BCElement, h::UInt) = hash((x.n, sort([(string(k), v.coords) for (k, v) in x.blocks]; by = first)), h)

"""Order of the element, `nothing` if it has infinite order."""
function Oscar.order(x::BCElement)
    ord = 1
    for a in values(x.blocks), j in eachindex(a.coords)
        if a.moduli[j] == 0
            a.coords[j] != 0 && return nothing
        elseif a.coords[j] != 0
            ord = lcm(ord, a.moduli[j] ÷ gcd(a.coords[j], a.moduli[j]))
        end
    end
    return ord
end

function Base.show(io::IO, x::BCElement)
    if is_zero(x)
        print(io, "0 in BC_$(x.n)(G)")
    else
        print(io, "element of BC_$(x.n)(G) with $(length(x.blocks)) nonzero block(s), order ",
              something(order(x), "infinite"))
    end
end
