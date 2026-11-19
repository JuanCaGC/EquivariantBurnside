
# ---------------------------------------------------------------------------
# Definition-level implementation: relations (C), (V), (B2) on SC_n(G)
# ---------------------------------------------------------------------------

struct DSub
    elts::Vector{Int}
    gens::Vector{Int}
    d::Vector{Int}
    exps::Vector{Vector{Int}}
    cent::BitSet
    eltset::BitSet
end

"""
    bc_direct(G, n)

Compute BC_n(G) from the defining presentation.

The arguments are a finite OSCAR or GAP group `G` and a positive integer `n`. Returns `(group, statistics)` with an `AbGroup` and counts `ngens`, `nrels`, and residual matrix size `dense`. This small-group validation route includes the Theta_2 term and does not use Theorem 5.2.

BC_n(G) straight from the definition (generators (H,Y,beta), relations (O),(C),(V),(B2)
with the Theta_2 term).  Intended for |G| up to a few hundred.

# Examples

```jldoctest
println(first(bc_direct(symmetric_group(3), 2)))

# output

Z/2
```
"""
function bc_direct(G, n::Int)
    load_gap!()
    raw = GAP.gap_to_julia(GAP.Globals.BCDirectData(gapobj(G)); recursive=true)
    subs = [DSub(Int.(s[:elts]), Int.(s[:gens]), Int.(s[:d]),
                 [Int.(e) for e in s[:exps]], BitSet(Int.(s[:cent])), BitSet(Int.(s[:elts])))
            for s in raw[:subs]]
    allsubs = [Int.(s) for s in raw[:allsubs]]
    conj = [Int.(c) for c in raw[:conj]]
    cinv = [invperm(c) for c in conj]
    subidx = Dict(s.elts => i for (i, s) in enumerate(subs))
    allidx = Dict(s => i for (i, s) in enumerate(allsubs))
    allbits = [BitSet(s) for s in allsubs]

    # generators: (i, yidx, sorted tuple of nonzero char indices in H_i^)
    col = Dict{Tuple{Int,Int,Vector{Int}},Int}()
    ys_of = Vector{Vector{Int}}(undef, length(subs))
    for (i, s) in enumerate(subs)
        ctx = CharCtx(s.d)
        ys = [y for y in eachindex(allsubs) if s.eltset ⊆ allbits[y] && allbits[y] ⊆ s.cent]
        ys_of[i] = ys
        for r in 1:n, β in multisets(ctx.m - 1, r)
            β = β .+ 1                                   # nonzero characters only
            generates_all(ctx, β) || continue
            for y in ys
                col[(i, y, β)] = length(col) + 1
            end
        end
    end

    eltpos(s::DSub, p) = searchsortedfirst(s.elts, p)
    # value of character c (of s) on group element at position p of s, as numerator mod D
    function charval(s::DSub, ctx::CharCtx, c::Vector{Int}, p::Int)
        e = s.exps[eltpos(s, p)]
        return mod(sum(c[i] * e[i] * (ctx.D ÷ s.d[i]) for i in eachindex(e)), ctx.D)
    end
    # transport character c of H_i along a position map f (g'_j -> f(g'_j) in H_i) to target H_k
    function transport(i, k, c, f::Vector{Int})
        s, t = subs[i], subs[k]
        cs, ct = CharCtx(s.d), CharCtx(t.d)
        cnew = Int[]
        for gj in t.gens
            v = charval(s, cs, c, f[gj])
            q = cs.D ÷ (order_of_gen(t, gj))
            v % q == 0 || error("transport: value not in expected subgroup")
            push!(cnew, v ÷ q)
        end
        return cnew
    end
    order_of_gen(t::DSub, gj) = t.d[findfirst(==(gj), t.gens)]

    rows = Row[]
    function addrow!(terms...)
        row = Row()
        for (key, coef) in terms
            c = col[key]
            v = get(row, c, 0) + coef
            v == 0 ? delete!(row, c) : (row[c] = v)
        end
        isempty(row) || push!(rows, row)
    end
    skey(i, y, β) = (i, y, sort(β))

    for ((i, y, β), _) in col
        s = subs[i]; ctx = CharCtx(s.d)
        r = length(β)
        # (V)
        vanishes = any(ctx.add[β[a], β[b]] == 1 for a in 1:r-1 for b in a+1:r)
        vanishes && addrow!(((i, y, β), 1))
        # (B2)
        for a in 1:r-1, b in a+1:r
            ba, bb = β[a], β[b]
            if ba == bb
                β0 = β[[t for t in 1:r if t != b]]
                addrow!(((i, y, β), 1), (skey(i, y, β0), -1))
            else
                β1 = copy(β); β1[a] = ctx.add[ba, ctx.neg[bb]]
                β2 = copy(β); β2[b] = ctx.add[bb, ctx.neg[ba]]
                terms = Any[((i, y, β), 1), (skey(i, y, β1), -1), (skey(i, y, β2), -1)]
                δ = ctx.add[ba, ctx.neg[bb]]             # b1 - b2 ; generates <b1-b2>
                sub = Set{Int}([1]); x = 1
                while true
                    x = Int(ctx.add[x, δ]); x == 1 && break; push!(sub, x)
                end
                if !any(β[t] in sub for t in 1:r)        # Theta_2 present
                    dc = ctx.chars[δ]
                    Hbar = [p for p in s.elts if charval(s, ctx, dc, p) == 0]
                    k = subidx[Hbar]
                    t = subs[k]; ct = CharCtx(t.d)
                    id = collect(1:maximum(s.elts))      # restriction: positions map to themselves
                    βbar = [encode(ct, transport(i, k, ctx.chars[bx], id)) for bx in β]
                    push!(terms, (skey(k, y, βbar), -1))
                end
                addrow!(terms...)
            end
        end
        # (C): generate by the generators of G
        for (ai, cv) in enumerate(conj)
            Hp = sort([cv[p] for p in s.elts]); k = subidx[Hp]
            Yp = allidx[sort([cv[p] for p in allsubs[y]])]
            # beta^a on H' = aHa^-1:  (beta^a)(x) = beta(a^-1 x a) -> position map cinv[a]
            βa = [encode(CharCtx(subs[k].d), transport(i, k, ctx.chars[bx], cinv[ai])) for bx in β]
            addrow!(((i, y, β), 1), (skey(k, Yp, βa), -1))
        end
    end
    G0, sz = cokernel_group(rows, length(col))
    return G0, (ngens=length(col), nrels=length(rows), dense=sz)
end

