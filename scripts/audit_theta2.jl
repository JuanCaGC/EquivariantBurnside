# Audit of the class level evaluation `bc_image` against the defining presentation of BC_n(G).
#
# Usage: julia --project=. scripts/audit_theta2.jl
#
# For small groups G and dimensions n it builds the presentation of BC_n(G) from the definition (generators
# (H, Y~, beta), relations (O), (C), (V), (B) with the Theta_2 term, `EquivariantBurnside._direct_presentation`),
# evaluates every generator with the engine (`bc_image` of the corresponding symbol) and reports:
#   A. how many rows of the true relation module the engine sends to a nonzero element, by kind of relation,
#   B. how many rows of the engine relation module (the same rows with the Theta_2 term removed) are nonzero
#      in the true quotient, that is, not in the row space of the true relation module.
# A relation row that the engine does not kill shows that the engine evaluation is not a homomorphism from the
# group defined by the paper.

using Oscar, EquivariantBurnside, Random
const EB = EquivariantBurnside

function engine_elements(G, n, P)
    Gg = gapobj(G)
    els = GAP.Globals.AsSSortedList(Gg)
    cache = Dict{Any,Any}()
    function elem(key)
        get!(cache, key) do
            i, y, β = key
            s = P.subs[i]
            ctx = EB.CharCtx(s.d)
            hg = [els[p] for p in s.gens]
            yg = [els[p] for p in P.allsubs[y]]
            betas = [Int.(ctx.chars[b]) for b in β]
            bc_image(BCSymbol(Gg, hg, yg, betas), n)
        end
    end
    return elem
end

function row_value(row, keys, elem)
    acc = nothing
    for (c, coef) in row
        x = coef * elem(keys[c])
        acc = acc === nothing ? x : acc + x
    end
    return acc
end

function in_rowspace(rows, extra, ncols)
    # is `extra` (a sparse row) in the Z-row span of `rows` ?  Decided with Smith/Hermite style solving over Z.
    R = zero_matrix(ZZ, length(rows), ncols)
    for (i, r) in enumerate(rows), (c, v) in r
        R[i, c] = v
    end
    b = zero_matrix(ZZ, 1, ncols)
    for (c, v) in extra
        b[1, c] = v
    end
    return can_solve(R, b; side = :left)
end

function audit(label, G, n; part_b = true)
    t0 = time()
    P = EB._direct_presentation(G, n)
    keys = Vector{Any}(undef, length(P.col))
    for (k, c) in P.col
        keys[c] = k
    end
    elem = engine_elements(G, n, P)
    kinds = unique(P.kinds)
    nonzero = Dict(k => 0 for k in kinds)
    total = Dict(k => 0 for k in kinds)
    for (r, k) in zip(P.rows, P.kinds)
        total[k] += 1
        v = row_value(r, keys, elem)
        (v === nothing || is_zero(v)) || (nonzero[k] += 1)
    end
    println(label, " n=", n, ": ", length(keys), " generators, ", length(P.rows), " relations")
    for k in kinds
        println("   A  ", rpad(string(k), 20), " engine nonzero on ", nonzero[k], " of ", total[k])
    end
    if part_b
        # exact structure of the true group: Smith form of the true relation matrix with the column transform
        m = length(keys)
        R = zero_matrix(ZZ, length(P.rows), m)
        for (i, r) in enumerate(P.rows), (c, v) in r
            R[i, c] = v
        end
        S, _, U = snf_with_transform(R)
        d = [i <= min(size(S)...) ? S[i, i] : ZZ(0) for i in 1:m]
        function true_order(x)            # x is a row vector of length m, returns 0 for infinite order
            y = x * U
            o = ZZ(1)
            for i in 1:m
                yi = y[1, i]
                yi == 0 && continue
                d[i] == 0 && return 0
                o = lcm(o, div(d[i], gcd(d[i], yi)))
            end
            return Int(o)
        end
        eng_order(x) = x === nothing || is_zero(x) ? 1 : (o = order(x); o === nothing ? 0 : Int(o))
        agree = 0; zero_mismatch = 0; order_mismatch = 0
        examples = []
        for (key, c) in P.col
            x = zero_matrix(ZZ, 1, m); x[1, c] = 1
            to = true_order(x); eo = eng_order(elem(key))
            if to == eo
                agree += 1
            else
                (to == 1) != (eo == 1) ? (zero_mismatch += 1) : (order_mismatch += 1)
                length(examples) < 3 && push!(examples, (key, to, eo))
            end
        end
        # engine relation rows (Theta_2 term dropped) in the true quotient
        # random classes: compare the order in the engine and in the true group
        rng = Random.MersenneTwister(1)
        nrand = 3000; rmis = 0; rzero = 0; rex = []
        for _ in 1:nrand
            supp = rand(rng, 1:min(4, m))
            x = zero_matrix(ZZ, 1, m)
            for c in rand(rng, 1:m, supp)
                x[1, c] += rand(rng, -2:2)
            end
            e = nothing
            for c in 1:m
                x[1, c] == 0 && continue
                term = Int(x[1, c]) * elem(keys[c])
                e = e === nothing ? term : e + term
            end
            to = true_order(x); eo = eng_order(e)
            if to != eo
                rmis += 1
                (to == 1) != (eo == 1) && (rzero += 1)
                length(rex) < 2 && push!(rex, (to, eo))
            end
        end
        println("   B  random classes: order differs on ", rmis, " of ", nrand, " (zero verdict differs on ", rzero, ")",
                isempty(rex) ? "" : "   e.g. (true, engine) = " * string(rex))
        nbad = 0; ncnt = 0
        for (r, k) in zip(P.rows, P.kinds)
            k == :B_distinct_theta2 || continue
            ncnt += 1
            x = zero_matrix(ZZ, 1, m)
            for (c, v) in r
                x[1, c] = v
            end
            # drop the Theta_2 term: the symbol being blown up is the only term with coefficient +1, its subgroup index is
            # shared by the two Theta_1 terms, and the Theta_2 term is the term of coefficient -1 with another subgroup
            plus = [c for (c, v) in r if v == 1]
            length(plus) == 1 || error("unexpected shape of a blowup row")
            i0 = keys[plus[1]][1]
            for (c, v) in r
                (v == -1 && keys[c][1] != i0) && (x[1, c] += 1)
            end
            true_order(x) == 1 || (nbad += 1)
        end
        println("   B  generators with the same order in the engine and in the true group: ", agree, " of ", length(keys),
                "   (zero verdict differs on ", zero_mismatch, ", order differs on ", order_mismatch, ")")
        for e in examples
            println("        e.g. key ", e[1], " true order ", e[2], " engine order ", e[3])
        end
        println("   B  engine relations of Theta_2 rows that are nonzero in the true group: ", nbad, " of ", ncnt)
    end
    println("   time ", round(time() - t0; digits = 1), " s")
    return (nonzero = nonzero, total = total)
end

if abspath(PROGRAM_FILE) == @__FILE__
    audit("C3 x C3", abelian_group(PermGroup, [3, 3]), 2; part_b = true)
    audit("S3", symmetric_group(3), 2; part_b = true)
    audit("S3", symmetric_group(3), 3; part_b = true)
    audit("C6", cyclic_group(PermGroup, 6), 2; part_b = true)
    audit("D4", dihedral_group(PermGroup, 8), 2; part_b = true)
    audit("C4 x C2", abelian_group(PermGroup, [4, 2]), 2; part_b = true)
    audit("C9", cyclic_group(PermGroup, 9), 2; part_b = true)
end
