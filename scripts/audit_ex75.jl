# Decide the non-vanishing of the difference of the classes of EBGLA Example 7.5 in the group BC_2(G)
# defined by the paper (with the Theta_2 term), instead of in the block decomposition used by `bc_image`.
#
# Usage: julia --project=. scripts/audit_ex75.jl
#
# The defining presentation of `EquivariantBurnside._direct_presentation` has about 5500 generators and 11000
# relations for this group of order 192. A class vector v is nonzero in BC_2(G) tensored with F_p, hence nonzero in
# BC_2(G), when v is not in the row space of the relation matrix over F_p.

using Oscar, EquivariantBurnside
const EB = EquivariantBurnside

GAP.evalstr("""
pt75 := function(i,j) return 8*(i mod 8)+(j mod 8)+1; end;;
Ta75 := PermList(List([0..63], k -> pt75(QuoInt(k,8)+1, k mod 8)));;
Tb75 := PermList(List([0..63], k -> pt75(QuoInt(k,8), (k mod 8)+1)));;
M175 := PermList(List([0..63], k -> pt75(k mod 8, -QuoInt(k,8)-(k mod 8))));;
M275 := M175^-1;;
G75b := fail;;
if M175*Ta75*M175^-1 = Tb75^-1 and M175*Tb75*M175^-1 = Ta75*Tb75^-1 then G75b := Group(Ta75,Tb75,M175);
elif M275*Ta75*M275^-1 = Tb75^-1 and M275*Tb75*M275^-1 = Ta75*Tb75^-1 then G75b := Group(Ta75,Tb75,M275); fi;;
""")

# The class of the action of type (7.1) with (s, t), as derived for this project (symbols of the six ray model).
function class75(G, s, t)
    alpha = GAP.Globals.Ta75; A = [alpha, GAP.Globals.Tb75]
    neg(x) = mod(-x, 8)
    cls = BCClass(G, 2)
    push!(cls, BCSymbol(G, [alpha], A, [[mod(s, 8)]]))
    push!(cls, BCSymbol(G, [alpha], A, [[neg(s)]]))
    push!(cls, BCSymbol(G, A, A, [[mod(s, 8), neg(t)], [0, mod(t, 8)]]))
    push!(cls, BCSymbol(G, A, A, [[mod(s, 8), 0], [neg(s), mod(t, 8)]]))
    return cls
end

# Column of the defining presentation that corresponds to a symbol of `BCSymbol`.
function key_of(sym, P, els, Gg, subidx, allidx)
    pos(x) = Int(GAP.Globals.Position(els, x))
    plist(gens) = sort([pos(x) for x in GAP.Globals.AsSSortedList(GAP.Globals.Subgroup(Gg, GAP.GapObj(gens)))])
    Hpos = plist(sym.hg)
    Ypos = plist(vcat(sym.hg, sym.yg))
    i = subidx[Hpos]; y = allidx[Ypos]
    s = P.subs[i]
    # exponent vector of every element of H in the generators of the symbol
    exps = Dict{Int,Vector{Int}}()
    for e in Iterators.product((0:(o - 1) for o in sym.ords)...)
        g = GAP.Globals.One(Gg)
        for (h, k) in zip(sym.hg, e)
            g = GAP.Globals.PROD(g, GAP.Globals.POW(h, k))
        end
        exps[pos(g)] = collect(e)
    end
    ctx = EB.CharCtx(s.d)
    idx = Int[]
    for c in sym.betas
        cp = Int[]
        for (k, gp) in enumerate(s.gens)
            e = exps[gp]
            frac = sum(c[j] * e[j] // sym.ords[j] for j in eachindex(e))
            v = frac * s.d[k]
            denominator(v) == 1 || error("character does not restrict to an integer exponent")
            push!(cp, mod(Int(numerator(v)), s.d[k]))
        end
        all(==(0), cp) && continue
        push!(idx, EB.encode(ctx, cp))
    end
    return (i, y, sort(idx))
end

function class_vector(cls, P, els, Gg, subidx, allidx)
    v = Dict{Int,Int}()
    for (coef, sym) in cls.terms
        k = key_of(sym, P, els, Gg, subidx, allidx)
        c = P.col[k]
        v[c] = get(v, c, 0) + coef
    end
    return filter(kv -> kv[2] != 0, v)
end

function rank_test(P, v, p)
    m = length(P.col); nr = length(P.rows)
    F = GF(p)
    R = zero_matrix(F, nr + 1, m)
    for (i, r) in enumerate(P.rows), (c, a) in r
        R[i, c] = F(a)
    end
    r0 = rank(view(R, 1:nr, 1:m))
    for (c, a) in v
        R[nr + 1, c] = F(a)
    end
    return (r0, rank(R))
end

if abspath(PROGRAM_FILE) == @__FILE__
    Gg = GAP.Globals.G75b
    G = Gg
    P = EB._direct_presentation(G, 2)
    els = GAP.Globals.AsSSortedList(Gg)
    subidx = Dict(s.elts => i for (i, s) in enumerate(P.subs))
    allidx = Dict(s => i for (i, s) in enumerate(P.allsubs))
    println("generators ", length(P.col), " relations ", length(P.rows))
    diff = class75(G, 1, 7) - class75(G, 3, 5)
    v = class_vector(diff, P, els, Gg, subidx, allidx)
    println("class vector with ", length(v), " nonzero entries")
    # the engine verdict, for comparison
    x = bc_image(diff)
    println("engine: zero = ", is_zero(x), ", order = ", is_zero(x) ? 1 : order(x))
    for p in (2, 3, 5, 32003)
        r0, r1 = rank_test(P, v, p)
        println("p = ", p, ": rank of relations ", r0, ", with the class ", r1, " => ", r1 > r0 ? "NONZERO in BC_2(G) (true group)" : "in the row space over F_p (inconclusive for this p)")
    end
end
