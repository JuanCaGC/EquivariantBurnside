# Example 7.5 of Tschinkel-Yang-Zhang (arXiv:2302.02296): the two actions of G = C8^2 : C3 on P^2
#   (x:y:z) -> (zeta^s x:y:z), (x:zeta^t y:z), (z:x:y)    for (s,t) = (1,7) and (3,5).
# The class of P^2 in Burn_2(G) is derived here from the toric geometry of the hexagon surface dP6
# (see the comments), and its image in BC_2(G) is computed with proj/bcclass.jl.
include("bcclass.jl")
using .BCClass, Oscar
const B = BCClass.B

# Abstract group G = A : <c>, A = <alpha,beta> = C8^2 acting by translations on (Z/8)^2,
# c acting linearly by M with  c alpha c^-1 = beta^-1,  c beta c^-1 = alpha beta^-1  (both actions satisfy this,
# because s/t = -1 and -t/s = 1 mod 8 for (1,7) and (3,5)).
GAP.evalstr("""
pt := function(i,j) return 8*(i mod 8)+(j mod 8)+1; end;;
Ta := PermList(List([0..63], k -> pt(QuoInt(k,8)+1, k mod 8)));;
Tb := PermList(List([0..63], k -> pt(QuoInt(k,8), (k mod 8)+1)));;
M1 := PermList(List([0..63], k -> pt(k mod 8, -QuoInt(k,8)-(k mod 8))));;   # (i,j) -> (j,-i-j)
M2 := M1^-1;;
G75 := fail;;
if M1*Ta*M1^-1 = Tb^-1 and M1*Tb*M1^-1 = Ta*Tb^-1 then G75 := Group(Ta,Tb,M1); gam75 := M1;
elif M2*Ta*M2^-1 = Tb^-1 and M2*Tb*M2^-1 = Ta*Tb^-1 then G75 := Group(Ta,Tb,M2); gam75 := M2; fi;;
""")
G = GAP.Globals.G75
GAP.Globals.IsGroup(G) || error("could not realize the relations")
println("|G| = ", GAP.Globals.Size(G))
alpha = GAP.Globals.Ta; beta = GAP.Globals.Tb
@assert Int(GAP.Globals.Order(GAP.Globals.gam75)) == 3
prepare!(G)

neg(x) = mod(-x, 8)
# class symbols, derived from the hexagon surface (see the derivation in the report):
#  divisors D_{e1} and D_{-e1} (one C3-orbit each) have stabilizer H = <alpha>, Y = A, normal weights s and -s
#  vertices of the two C3-orbits have stabilizer A with weights ((s,-t),(0,t)) and ((s,0),(-s,t)).
function class75(s, t)
    A = [alpha, beta]
    return [
        (1, [alpha], A, [[mod(s, 8)]]),
        (1, [alpha], A, [[neg(s)]]),
        (1, A, A, [[mod(s, 8), neg(t)], [0, mod(t, 8)]]),
        (1, A, A, [[mod(s, 8), 0], [neg(s), mod(t, 8)]]),
    ]
end
for n in (2,)
    println("BC_$n(G) = ", B.bc(G, n))
end
c1 = class75(1, 7); c2 = class75(3, 5)
diff = vcat(c1, [(-c, h, y, b) for (c, h, y, b) in c2])
println("class (s,t)=(1,7) is zero in BC_2(G)?  ", class_is_zero(G, 2, c1), "  order ", class_order(G, 2, c1))
println("class (s,t)=(3,5) is zero in BC_2(G)?  ", class_is_zero(G, 2, c2), "  order ", class_order(G, 2, c2))
println("difference zero in BC_2(G)?           ", class_is_zero(G, 2, diff), "  order ", class_order(G, 2, diff))
# control: an action compared with itself
println("control (1,7) - (1,7) zero?           ", class_is_zero(G, 2, vcat(c1, [(-c, h, y, b) for (c, h, y, b) in c1])))
# per-block coordinates of the difference
out, mods = class_coords(G, 2, diff)
for (key, v) in sort(collect(out); by=first)
    println("  block ", key, " moduli ", mods[key], " coordinates ", v)
end

# ---- independent consistency checks of the derivation ----
# Only the actions with s/t = -1 mod 8 are actions of the SAME abstract group G (for other (s,t) the relation
# c a c^-1 = b^(s/t) changes), that is (s,t) = (s,-s) with s = 1,3,5,7.
# The Cremona involution (x:y:z) -> (1/x:1/y:1/z) commutes with the coordinate permutations and conjugates the
# action (s,-s) into (-s,s), so those two classes must be equal. For s' not equal to +-s the paper's conclusion
# (Example 7.5) is that the actions are not birational, so the classes must differ.
println("equality matrix of the classes of the actions (s,-s), s = 1,3,5,7 in BC_2(G) (true = equal):")
ss = (1, 3, 5, 7)
for s1 in ss
    row = []
    for s2 in ss
        d = vcat(class75(s1, neg(s1)), [(-c, h, y, b) for (c, h, y, b) in class75(s2, neg(s2))])
        push!(row, class_is_zero(G, 2, d))
    end
    println("  s=$s1: ", row)
end

# ---- a certificate of non-vanishing that does not use the Smith normal form ----
# A functional f: Z^{gens of B_2(A)} -> Z/m that kills EVERY relation of the block [A,A] and does not kill the
# difference proves that the difference is nonzero in BC_2(G).  We extract f from the quotient map, then check
# the two properties directly on the relation matrix (plain integer arithmetic).
let
    bkey, pidx = (15, 1)
    # collect the difference restricted to this block as a vector over generator keys
    acc = Dict{Vector{Int},Int}()
    bmref = nothing
    for (coef, hg, yg, betas) in diff
        b, p, v, bm, key = symbol_image(G, 2, hg, yg, betas)
        if (b, p) == (bkey, pidx)
            acc[key] = get(acc, key, 0) + coef
            bmref = bm
        end
    end
    bm = bmref
    out, mods = class_coords(G, 2, diff)
    v = out[(bkey, pidx)]
    j = findfirst(x -> x != 0, v)
    m = bm.moduli[j]
    f = [mod(bm.Qm[i, j], m) for i in 1:size(bm.Qm, 1)]
    ctx = B.CharCtx(bm.d)
    perms = [B.char_perm(ctx, Matrix{Int}(reduce(hcat, [Int.(r) for r in M])')) for M in
             GAP.gap_to_julia(GAP.Globals.BCInfo(bkey); recursive=true)[:mats][pidx]]
    rows, N = B.bn_quotient(bm.d, 2, perms; return_presentation=true)
    kills = all(mod(sum(coef * f[c] for (c, coef) in r), m) == 0 for r in rows)
    val = mod(sum(c * f[bm.col[key]] for (key, c) in acc), m)
    println("certificate: block [A,A] of BC_2(G): $N generators, $(length(rows)) relations, functional mod $m")
    println("  f kills all relations: ", kills, "     f(difference) = ", val, " (nonzero means the difference is nonzero)")
end
