"""
B_n(H)/(C): H = prod Z/d_i, `perms` = permutations of H^ induced by the group
of N_G(H) n N_G(Y).  Returns (AbGroup, info).  If `extra_vanishing`, also impose
the (redundant, by [KT, Prop 4.7]) vanishing for every sub-multiset summing to 0.
With `return_presentation=true`, instead return `(rows, ncols)` before any
elimination, for use with `certify_snf`, the default computation is unchanged.
"""
function bn_quotient(d::Vector{Int}, n::Int, perms::Vector{Vector{Int}};
                     extra_vanishing::Bool=false, return_presentation::Bool=false)
    ctx = CharCtx(d)
    m = ctx.m
    gens = [ms for ms in multisets(m, n) if generates_all(ctx, ms)]
    col = Dict{Vector{Int},Int}(g => i for (i, g) in enumerate(gens))
    rows = Row[]
    function addrow!(terms::Pair{Vector{Int},Int}...)
        row = Row()
        for (key, coef) in terms
            c = col[sort(key)]
            v = get(row, c, 0) + coef
            v == 0 ? delete!(row, c) : (row[c] = v)
        end
        isempty(row) || push!(rows, row)
    end
    for β in gens
        for i in 1:n-1, j in i+1:n
            a, b = β[i], β[j]
            (a == 1 && b == 1) && continue
            if a == b                                   # duplicate nonzero: (b,b,..) = (0,b,..)
                β0 = copy(β); β0[j] = 1
                addrow!(β => 1, β0 => -1)
                if ctx.neg[a] == a                       # 2b = 0: (V) applies to (b,b,..)
                    addrow!(β => 1)
                end
            elseif a != 1 && b != 1
                # (V) and (B) are independent relations, both hold when b_i + b_j = 0
                ctx.add[a, b] == 1 && addrow!(β => 1)    # (V): b_i + b_j = 0
                β1 = copy(β); β1[i] = ctx.add[a, ctx.neg[b]]      # (B)
                β2 = copy(β); β2[j] = ctx.add[b, ctx.neg[a]]
                addrow!(β => 1, β1 => -1, β2 => -1)
            end
        end
        if extra_vanishing
            nz = [x for x in β if x != 1]
            for mask in 1:(1<<length(nz))-1
                s = 1
                for t in eachindex(nz)
                    (mask >> (t - 1)) & 1 == 1 && (s = Int(ctx.add[s, nz[t]]))
                end
                s == 1 && addrow!(β => 1)
            end
        end
        for p in perms                                   # (C_(H,Y))
            βg = [p[x] for x in β]
            sort(βg) != β && addrow!(β => 1, βg => -1)
        end
    end
    return_presentation && return (rows, length(gens))
    G, sz = cokernel_group(rows, length(gens))
    return G, (ngens=length(gens), nrels=length(rows), dense=sz)
end
