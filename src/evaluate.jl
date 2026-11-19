# Additive instrumented copy of BurnsideC.cokernel_group unit-pivot loop.
# Pivot selection and row updates are unchanged. Only trace recording is added.
# Final residual matrix retains zero columns to keep free-generator coordinates.
function tracked_elimination(rows::Vector{Row}, ncols::Int)
    colrows = Dict{Int,Set{Int}}()
    for (r, row) in enumerate(rows), c in keys(row)
        push!(get!(colrows, c, Set{Int}()), r)
    end
    alive = trues(length(rows))
    trace = Tuple{Int,Int,Row}[]
    neliminated = 0
    changed = true
    while changed
        changed = false
        for r in sortperm(length.(rows))
            alive[r] || continue
            row = rows[r]
            if isempty(row)
                alive[r] = false
                continue
            end
            best = 0; bestcnt = typemax(Int)
            for (c, v) in row
                if abs(v) == 1
                    cnt = length(colrows[c])
                    if cnt < bestcnt
                        best = c; bestcnt = cnt
                    end
                end
            end
            best == 0 && continue
            c = best; ε = row[c]
            push!(trace, (c, ε, copy(row)))
            for r2 in collect(colrows[c])
                r2 == r && continue
                row2 = rows[r2]
                f = row2[c] * ε
                for (k, v) in row
                    nv = get(row2, k, 0) - f * v
                    if nv == 0
                        delete!(row2, k)
                        delete!(colrows[k], r2)
                    else
                        if !haskey(row2, k)
                            push!(colrows[k], r2)
                        end
                        row2[k] = nv
                    end
                end
            end
            for k in keys(row)
                delete!(colrows[k], r)
            end
            alive[r] = false
            neliminated += 1
            changed = true
        end
    end
    liverows = [rows[r] for r in eachindex(rows) if alive[r] && !isempty(rows[r])]
    eliminated = Set(c for (c, _, _) in trace)
    survivors = [c for c in 1:ncols if !(c in eliminated)]
    q = length(survivors)
    E = zero_matrix(ZZ, ncols, q)
    J = zero_matrix(ZZ, q, ncols)
    for (j,c) in enumerate(survivors)
        E[c,j] = 1; J[j,c] = 1
    end
    for (c, epsilon, row) in reverse(trace), j in 1:q
        E[c,j] = -epsilon * sum((ZZ(v)*E[k,j] for (k,v) in row if k != c); init=ZZ(0))
    end
    M = zero_matrix(ZZ,length(liverows),q)
    for (i,row) in enumerate(liverows), (j,c) in enumerate(survivors)
        M[i,j] = get(row,c,0)
    end
    return E,J,M,survivors,trace
end

const _loaded = Ref(false)
# The group whose block data is currently stored in the GAP global BCB, and the lazily built table of block names.
const _prepared = Ref{Any}(nothing)
const _block_table = Ref{Any}(nothing)
"""
    bcclass_init!()

Initialize the GAP symbol evaluation routines.

Takes no arguments. Returns `true` after the first initialization and `nothing` on subsequent calls. Call it for its initialization side effect. Repeated calls reuse the initialized routines.
"""
function bcclass_init!()
    _loaded[] && return
    load_gap!()
    GAP.evalstr(read(joinpath(@__DIR__, "..", "gap", "bcclass.g"), String))
    _loaded[] = true
end

"""
    prepare!(G)

Prepare the GAP block data for symbol evaluation.

The argument `G` is a raw GAP group. Returns the result of `BCBuild`, the number of abelian subgroup blocks. Replaces the current prepared group and invalidates its block-name table. Call before low level evaluation for a new group. High level `bc_image` prepares automatically.

Build the block data (GAP side) for G.  Must be called before `symbol_image` for a new group.

# Examples

```jldoctest
G = gapobj(symmetric_group(3))
h = Oscar.GAP.Globals.GeneratorsOfGroup(Oscar.GAP.Globals.DerivedSubgroup(G))[1]
prepare!(G)
terms = [(1, [h], [h], [[1],[1]])]
println(class_order(G, 2, terms))

# output

2
```
"""
function prepare!(G)
    bcclass_init!()
    nb = GAP.Globals.BCBuild(G)
    _prepared[] = G
    _block_table[] = nothing
    return nb
end

"""
    BlockMaps(d, n, gens, col, Qm, moduli)

Store a block presentation and its quotient map.

The arguments are cyclic orders `d`, dimension `n`, character multisets `gens`, their index dictionary `col`, the integer quotient matrix `Qm`, and Smith `moduli`. Returns a `BlockMaps`. Prefer `block_maps` to compute consistent fields. A zero modulus denotes a free coordinate and row i of `Qm` is the image of generator i.
"""
struct BlockMaps
    d::Vector{Int}
    n::Int
    gens::Vector{Vector{Int}}
    col::Dict{Vector{Int},Int}
    Qm::Matrix{Int}            # N x k: image of the i-th generator is Qm[i, :]
    moduli::Vector{Int}        # 0 = free coordinate
end

reduce_coords(bm::BlockMaps, v) = [bm.moduli[j] == 0 ? v[j] : mod(v[j], bm.moduli[j]) for j in eachindex(v)]

"""
    block_maps(d, perms, n)

Compute a block quotient map in Smith coordinates.

The argument `d::Vector{Int}` contains cyclic orders. The vector `perms::Vector{Vector{Int}}` contains permutations of character indices and `n::Int` is the dimension. Returns a `BlockMaps` and checks that every relation maps to zero. Character indices use the internal `CharCtx` encoding with index one for zero.
"""
function block_maps(d::Vector{Int}, perms::Vector{Vector{Int}}, n::Int)
    ctx = CharCtx(d)
    gens = [ms for ms in multisets(ctx.m, n) if generates_all(ctx, ms)]
    col = Dict{Vector{Int},Int}(g => i for (i, g) in enumerate(gens))
    rows, N = bn_quotient(d, n, perms; return_presentation=true)
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


"""
    symbol_image(G, n, hgens, ygens, betas; cache)

Evaluate one symbol using the prepared GAP data.

The arguments are a prepared raw GAP group `G`, dimension `n::Int`, GAP element lists `hgens` and `ygens`, and `betas::Vector{Vector{Int}}`. The optional cache stores block maps. Returns `(b, p, coords, maps, key)` with subgroup and pair indices, reduced Smith coordinates, a `BlockMaps` and the padded sorted character-index multiset. Use `prepare!` first. The subgroup located from `ygens` includes H.

# Examples

```jldoctest
G = gapobj(symmetric_group(3))
h = Oscar.GAP.Globals.GeneratorsOfGroup(Oscar.GAP.Globals.DerivedSubgroup(G))[1]
prepare!(G)
terms = [(1, [h], [h], [[1],[1]])]
b, p, coords, maps, key = symbol_image(G, 2, [h], [h], [[1],[1]])
println(length((b, p, coords, maps, key)))
println(any(!iszero, coords))

# output

5
true
```
"""
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
    ctx = CharCtx(d0)
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
        push!(key, encode(ctx, c0))
    end
    length(key) <= n || error("more characters than n")
    key = sort!(vcat(key, ones(Int, n - length(key))))
    generates_all(ctx, key) || error("the characters do not generate the dual of H")
    mats = [_intmat(M) for M in info[:mats][p]]
    perms = [char_perm(ctx, M) for M in mats]
    ckey = (d0, n, sort(perms))
    bm = get!(cache, ckey) do
        block_maps(d0, perms, n)
    end
    return b, p, reduce_coords(bm, bm.Qm[bm.col[key], :]), bm, key
end

"""
    class_coords(G, n, terms)

Evaluate an integer combination in the prepared group.

Pass a prepared raw GAP group `G`, dimension `n::Int`, and `terms` containing `(coef, hgens, ygens, betas)` tuples with GAP elements. Returns `(coordinates, moduli)`, two dictionaries indexed by `(b,p)`. Zero components are retained. A zero modulus denotes a free coordinate. Use `prepare!` before evaluating a new group.

# Examples

```jldoctest
G = gapobj(symmetric_group(3))
h = Oscar.GAP.Globals.GeneratorsOfGroup(Oscar.GAP.Globals.DerivedSubgroup(G))[1]
prepare!(G)
terms = [(1, [h], [h], [[1],[1]])]
coords, moduli = class_coords(G, 2, terms)
println(length(coords))
println(all(k -> length(coords[k]) == length(moduli[k]), keys(coords)))

# output

1
true
```
"""
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

"""
    class_is_zero(G, n, terms)

Test whether a low level formal class vanishes.

The arguments have the same meaning as in `class_coords`. Returns a boolean after reducing every component. Use a raw GAP group and call `prepare!` first.

# Examples

```jldoctest
G = gapobj(symmetric_group(3))
h = Oscar.GAP.Globals.GeneratorsOfGroup(Oscar.GAP.Globals.DerivedSubgroup(G))[1]
prepare!(G)
terms = [(1, [h], [h], [[1],[1]])]
println(class_is_zero(G, 2, terms))
println(class_is_zero(G, 2, vcat(terms, terms)))

# output

false
true
```
"""
class_is_zero(G, n, terms) = all(all(x -> x == 0, v) for v in values(first(class_coords(G, n, terms))))

"""
    class_order(G, n, terms)

Compute the order of a low level formal class.

The arguments have the same meaning as in `class_coords`. Returns a positive integer, one for zero, or `nothing` for infinite order. Use a raw GAP group and call `prepare!` first.

Order of the element (nothing if infinite order).

# Examples

```jldoctest
G = gapobj(symmetric_group(3))
h = Oscar.GAP.Globals.GeneratorsOfGroup(Oscar.GAP.Globals.DerivedSubgroup(G))[1]
prepare!(G)
terms = [(1, [h], [h], [[1],[1]])]
println(class_order(G, 2, terms))

# output

2
```
"""
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

