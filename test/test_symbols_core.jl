module TestSymbolsCore
using Test, Oscar, EquivariantBurnside
const EB = EquivariantBurnside

img(G, n, terms...) = (cls = BCClass(G, n); foreach(t -> push!(cls, t[1], t[2]), terms); bc_image(cls))
nonzero_blocks(old) = sort([v for v in values(old) if any(!=(0), v)])
mycoords(x) = sort([a.coords for a in values(x.blocks)])

@testset "T1 the ten checks of test_bcclass through the new API" begin
    S3 = symmetric_group(3); c3 = cperm(S3, [1, 2, 3])
    sym(betas) = BCSymbol(S3, [c3], [c3], betas)
    x = img(S3, 2, (1, sym([[1], [1]])))
    @test !is_zero(x) && order(x) == 2
    @test is_zero(img(S3, 2, (2, sym([[1], [1]]))))
    @test is_zero(img(S3, 2, (1, sym([[1], [1]])), (-1, sym([[2], [2]]))))      # conjugate weights give the same class
    @test is_zero(img(S3, 2, (1, sym([[1], [2]]))))                              # (V)
    @test is_zero(img(S3, 2, (1, sym([[1]])), (-1, sym([[1], [1]]))))            # blowup relation
    D7 = dihedral_group(PermGroup, 14)
    r7 = first(filter(g -> order(g) == 7, collect(D7)))
    @test string(EB.bc(D7, 3).total) == "Z/2"
    s7(w) = BCSymbol(D7, [r7], [r7], [[c] for c in w])
    ws = ([1, 1, 2], [2, 4, 6], [2, 3, 6])
    xs = [img(D7, 3, (1, s7(w))) for w in ws]
    @test all(!is_zero, xs)
    @test xs[1] == xs[2] == xs[3]
    @test !is_zero(img(D7, 3, [(1, s7(w)) for w in ws]...))
end

@testset "T8 coordinates agree with the older API" begin
    S3 = GAP.Globals.SymmetricGroup(3)
    prepare!(S3)
    c3 = GAP.evalstr("(1,2,3)")
    old = [(1, [c3], [c3], [[1], [1]])]
    x = img(S3, 2, (1, BCSymbol(S3, [c3], [c3], [[1], [1]])))
    @test mycoords(x) == nonzero_blocks(first(class_coords(S3, 2, old)))
    @test order(x) == class_order(S3, 2, old)
    @test is_zero(x - x) && is_zero(2 * x) && !is_zero(3 * x) && order(3 * x) == 2
    @test x + x == 2 * x && -x == x            # order 2
    @test 4 * x == 0 * x
end

# ---- Example 7.5 of EBGLA, certificate that the two actions give different classes
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

@testset "T3 Example 7.5 certificate" begin
    G = GAP.Globals.G75b
    alpha = GAP.Globals.Ta75; beta = GAP.Globals.Tb75
    A = [alpha, beta]
    neg(x) = mod(-x, 8)
    function class75(s, t)
        cls = BCClass(G, 2)
        push!(cls, BCSymbol(G, [alpha], A, [[mod(s, 8)]]))
        push!(cls, BCSymbol(G, [alpha], A, [[neg(s)]]))
        push!(cls, BCSymbol(G, A, A, [[mod(s, 8), neg(t)], [0, mod(t, 8)]]))
        push!(cls, BCSymbol(G, A, A, [[mod(s, 8), 0], [neg(s), mod(t, 8)]]))
        return cls
    end
    diff = class75(1, 7) - class75(3, 5)
    x = bc_image(diff)
    @test !is_zero(x)
    @test order(x) == 3
    @test length(bc_blocks(x)) == 1
    @test is_zero(bc_image(class75(1, 7) - class75(1, 7)))
    cert = certificate_nonzero(x)
    @test cert.modulus == 3 && cert.n == 2 && sort(cert.d) == [8, 8] && length(cert.gens) == 768
    @test length(cert.ggens) == 3
    @test verify(cert)
    @test verify_with_group(cert)
    path = tempname()
    write_certificate(path, cert)
    @test read_certificate(path) == cert
    @test verify(path)
    # the same certificate checked by the standalone file in a separate process
    verifier = joinpath(@__DIR__, "..", "verifier", "verify_nonzero.jl")
    out = IOBuffer()
    proc = run(pipeline(ignorestatus(`$(Base.julia_cmd()) --startup-file=no $verifier $path`); stdout = out, stderr = devnull))
    @test proc.exitcode == 0 && strip(String(take!(out))) == "VALID"
    @test_throws ArgumentError certificate_nonzero(x - x)
end

@testset "T5 the standalone verifier is standalone and short" begin
    lines = readlines(joinpath(@__DIR__, "..", "verifier", "verify_nonzero.jl"))
    @test length(lines) <= 150
    code = [first(split(l, '#')) for l in lines]
    @test !any(l -> occursin(r"\b(using|import|include)\b", l), code)
end

@testset "T6 relation rows of the verifier equal those of bn_quotient" begin
    V = EB.NZVerifier
    canon(row) = sort(collect(row))
    function compare(d, n, mats)
        ctx = EB.CharCtx(d)
        perms = [EB.char_perm(ctx, M) for M in mats]
        gens_e = [ms for ms in EB.multisets(ctx.m, n) if EB.generates_all(ctx, ms)]
        gens_v, rels = V.relations(n, d, perms)
        rows_e, N = EB.bn_quotient(d, n, perms; return_presentation = true)
        col = Dict(g => i for (i, g) in enumerate(gens_v))
        rows_v = Set{Vector{Pair{Int,Int}}}()
        for r in rels
            acc = Dict{Int,Int}()
            for (t, c) in r
                acc[col[sort(t)]] = get(acc, col[sort(t)], 0) + c
            end
            filter!(kv -> kv[2] != 0, acc)
            isempty(acc) || push!(rows_v, canon(acc))
        end
        return gens_v == gens_e && N == length(gens_e) && rows_v == Set(canon(r) for r in rows_e)
    end
    @test compare([3], 2, Matrix{Int}[])
    @test compare([3], 2, [reshape([-1], 1, 1)])
    @test compare([3], 3, [reshape([-1], 1, 1)])
    @test compare([5], 3, [reshape([2], 1, 1)])
    @test compare([4], 2, [reshape([-1], 1, 1)])
    @test compare([2, 2], 2, [[0 1; 1 0], [1 1; 0 1]])
    @test compare([2, 2], 3, [[0 1; 1 0], [1 1; 0 1]])
    @test compare([2, 4], 2, Matrix{Int}[])
    @test compare([3, 3], 2, [[0 -1; 1 -1]])
    @test compare([3, 3], 3, [[0 1; 1 0]])
    @test compare([8, 8], 2, [[0 -1; 1 -1]])
    @test compare([6], 2, [reshape([-1], 1, 1)])
end

end
