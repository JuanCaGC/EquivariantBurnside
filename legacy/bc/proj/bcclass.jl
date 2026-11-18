# bcclass.jl -- evaluate elements of BC_n(G) given as sums of symbols (H, Y, beta).
#
# The group BC_n(G) is computed block by block (Theorem 5.2) by ../BurnsideC.jl.  Here we also keep the
# quotient map  Z^{generators of B_n(H)} -> B_n(H)/(C_(H,Y))  (tracked unit-pivot elimination plus Smith
# transform, the same ingredients as ../gl_verify.jl), so that an arbitrary integer combination of symbols
# can be mapped to explicit coordinates and tested for being zero.
#
# Conventions.
#   * A symbol is (hgens, ygens, betas): hgens are INDEPENDENT generators h_1..h_k of the abelian group H
#     (GAP elements of G, of orders d_1..d_k), ygens generate Y with H <= Y <= C_G(H), and betas is a list
#     of characters of H, each a vector c with  beta(h_j) = exp(2 pi i c_j / d_j).
#   * The symbol is moved by an element conj of G to the class representative of [H,Y] used by
#     ../bc_structure.g, and the characters are transported by beta'(x^conj) = beta(x).
#   * A symbol with length(betas) < n stands for beta padded with zeros up to length n (the point of
#     view of Lemma 5.1, a symbol of dimension d = n - length(betas)).
module BCClass

using Oscar
include(joinpath(@__DIR__, "..", "BurnsideC.jl"))
using .BurnsideC
const B = BurnsideC
include(joinpath(@__DIR__, "..", "gl_tracked_elimination.jl"))

export prepare!, bcclass_init!, BlockMaps, symbol_image, class_coords, class_is_zero, class_order, block_maps

const _loaded = Ref(false)
function bcclass_init!()
    _loaded[] && return
    B.load_gap!()
    GAP.evalstr(read(joinpath(@__DIR__, "bcclass.g"), String))
    _loaded[] = true
end

"""Build the block data (GAP side) for G.  Must be called before `symbol_image` for a new group."""
function prepare!(G)
    bcclass_init!()
    GAP.Globals.BCBuild(G)
end

struct BlockMaps
    d::Vector{Int}
    n::Int
    gens::Vector{Vector{Int}}
    col::Dict{Vector{Int},Int}
    Qm::Matrix{Int}            # N x k: image of the i-th generator is Qm[i, :]
    moduli::Vector{Int}        # 0 = free coordinate
end

reduce_coords(bm::BlockMaps, v) = [bm.moduli[j] == 0 ? v[j] : mod(v[j], bm.moduli[j]) for j in eachindex(v)]

function block_maps(d::Vector{Int}, perms::Vector{Vector{Int}}, n::Int)
    ctx = B.CharCtx(d)
    gens = [ms for ms in B.multisets(ctx.m, n) if B.generates_all(ctx, ms)]
    col = Dict{Vector{Int},Int}(g => i for (i, g) in enumerate(gens))
    rows, N = B.bn_quotient(d, n, perms; return_presentation=true)
    @assert N == length(gens)
    if N == 0
        return BlockMaps(d, n, gens, col, zeros(Int, N, 0), Int[])
    end
    E, J, M, survivors, trace = tracked_elimination(deepcopy(rows), N)
    q = length(survivors)
    D, U, V = nrows(M) == 0 ? (M, identity_matrix(ZZ, 0), identity_matrix(ZZ, q)) : snf_with_transform(M)
    diagonal = [j <= nrows(D) ? Int(D[j, j]) : 0 for j in 1:q]
    keep = findall(dd -> abs(dd) != 1, diagonal)
    moduli = abs.(diagonal[keep])
    Qz = (E * V)[:, keep]
    k = length(keep)
    Qm = [Int(Qz[i, a]) for i in 1:N, a in 1:k]
    bm = BlockMaps(d, n, gens, col, Qm, moduli)
    # every presentation relation must map to zero
    for r in rows
        v = zeros(Int, k)
        for (c, coef) in r
            v .+= coef .* Qm[c, :]
        end
        @assert all(x -> x == 0, reduce_coords(bm, v)) "relation not killed: the quotient map is wrong"
    end
    return bm
end

const _bm_cache = Dict{Any,BlockMaps}()

_intmat(x) = Matrix{Int}(reduce(hcat, [Int.(r) for r in x])')

"""Image of the symbol in its block: returns (block index b, pair index p, coordinates vector)."""
function symbol_image(G, n::Int, hgens, ygens, betas::Vector{Vector{Int}}; cache=_bm_cache)
    bcclass_init!()
    hg = GAP.GapObj(collect(hgens))
    yg = GAP.GapObj(collect(ygens))
    ords = [Int(GAP.Globals.Order(h)) for h in hgens]
    loc = GAP.Globals.BCLocate(G, hg, yg)
    GAP.Globals.IsRecord(loc) || error("symbol (H,Y) not found: is H abelian and nontrivial, and H <= Y <= C_G(H)?")
    b = Int(loc.b); p = Int(loc.p)
    F = GAP.gap_to_julia(GAP.Globals.BCExpsMat(b, loc.conj, hg, GAP.GapObj(ords)); recursive=true)
    info = GAP.gap_to_julia(GAP.Globals.BCInfo(b); recursive=true)
    d0 = Int.(info[:d])
    ctx = B.CharCtx(d0)
    k0 = length(d0)
    Dl = lcm(vcat(d0, ords)...)
    key = Int[]
    for c in betas
        length(c) == length(ords) || error("character has the wrong number of coordinates")
        c0 = zeros(Int, k0)
        for i in 1:k0
            s = mod(sum(F[i][j] * c[j] * (Dl ÷ ords[j]) for j in eachindex(ords)), Dl)
            q = Dl ÷ d0[i]
            s % q == 0 || error("transported character is not integral: wrong exponent matrix")
            c0[i] = s ÷ q
        end
        all(x -> x == 0, c0) && error("symbols carry nonzero characters")
        push!(key, B.encode(ctx, c0))
    end
    length(key) <= n || error("more characters than n")
    key = sort!(vcat(key, ones(Int, n - length(key))))
    B.generates_all(ctx, key) || error("the characters do not generate the dual of H")
    mats = [_intmat(M) for M in info[:mats][p]]
    perms = [B.char_perm(ctx, M) for M in mats]
    ckey = (d0, n, sort(perms))
    bm = get!(cache, ckey) do
        block_maps(d0, perms, n)
    end
    return b, p, reduce_coords(bm, bm.Qm[bm.col[key], :]), bm, key
end

"""Sum of `terms` = [(coef, hgens, ygens, betas), ...] in BC_n(G): Dict (b,p) => coordinates."""
function class_coords(G, n::Int, terms)
    acc = Dict{Tuple{Int,Int},Vector{Int}}()
    mods = Dict{Tuple{Int,Int},Vector{Int}}()
    for (coef, hg, yg, betas) in terms
        b, p, v, bm, _ = symbol_image(G, n, hg, yg, betas)
        w = get!(acc, (b, p), zeros(Int, length(v)))
        w .+= coef .* v
        mods[(b, p)] = bm.moduli
    end
    out = Dict{Tuple{Int,Int},Vector{Int}}()
    for (key, w) in acc
        m = mods[key]
        out[key] = [m[j] == 0 ? w[j] : mod(w[j], m[j]) for j in eachindex(w)]
    end
    return out, mods
end

class_is_zero(G, n, terms) = all(all(x -> x == 0, v) for v in values(first(class_coords(G, n, terms))))

"""Order of the element (nothing if infinite order)."""
function class_order(G, n, terms)
    out, mods = class_coords(G, n, terms)
    ord = 1
    for (key, v) in out
        for j in eachindex(v)
            if mods[key][j] == 0
                v[j] != 0 && return nothing
            elseif v[j] != 0
                ord = lcm(ord, mods[key][j] ÷ gcd(v[j], mods[key][j]))
            end
        end
    end
    return ord
end

end # module
