module TestSymbolsErrors
using Test, Oscar, EquivariantBurnside
const EB = EquivariantBurnside

# True when f() throws an ArgumentError whose message contains the phrase.
function throws(phrase, f)
    try
        f()
    catch e
        return e isa ArgumentError && occursin(phrase, e.msg)
    end
    return false
end

@testset "T2 errors of the symbol constructors (one per row of the table)" begin
    # the same checks on a permutation group and on a raw GAP group
    for (label, G, el) in [("OSCAR perm group", symmetric_group(4), (p...) -> cperm(symmetric_group(4), collect(p))),
                           ("raw GAP group", GAP.Globals.SymmetricGroup(4), (p...) -> GAP.evalstr("(" * join(p, ",") * ")"))]
        if label == "OSCAR perm group"
            S4 = G
            el = (p...) -> cperm(S4, collect(p))
            one_el = one(S4)
        else
            one_el = GAP.evalstr("()")
        end
        c3 = el(1, 2, 3); t12 = el(1, 2); t23 = el(2, 3)
        v1 = el(1, 2) * el(3, 4); v2 = el(1, 3) * el(2, 4)
        @testset "$label" begin
            @test throws("H is trivial", () -> BCSymbol(G, [], [], [[1]]))
            @test throws("H is trivial", () -> BCSymbol(G, [one_el], [], [[1]]))
            @test throws("H is not abelian", () -> BCSymbol(G, [t12, t23], [], [[1, 0]]))
            @test throws("not independent", () -> BCSymbol(G, [el(1, 2, 3, 4), el(1, 2, 3, 4)^2], [], [[1, 0]]))
            @test throws("does not centralize H", () -> BCSymbol(G, [c3], [t12], [[1]]))
            @test throws("does not contain H", () -> BCSymbol_preimage(G, [v1], [v2], [[1]]))
            @test throws("does not contain H", () -> BCSymbol_preimage(G, [c3], [], [[1]]))
            @test throws("wrong number of coordinates", () -> BCSymbol(G, [c3], [], [[1, 2]]))
            @test throws("zero character", () -> BCSymbol(G, [c3], [], [[0]]))
            @test throws("zero character", () -> BCSymbol(G, [c3], [], [[3]]))
            sym_v = BCSymbol(G, [v1, v2], [], [[1, 0], [1, 0]])
            @test throws("do not generate", () -> push!(BCClass(G, 2), sym_v))
            sym3 = BCSymbol(G, [c3], [], [[1], [1], [1]])
            @test throws("more characters than n", () -> push!(BCClass(G, 2), sym3))
            @test throws("n must be positive", () -> BCClass(G, 0))
            @test throws("n must be positive", () -> BCClass(G, -3))
            other = symmetric_group(3)
            sym_other = BCSymbol(other, [cperm(other, [1, 2, 3])], [], [[1]])
            @test throws("different group", () -> push!(BCClass(G, 2), sym_other))
            # a generator that is not an element of G
            @test throws("not an element of G", () -> BCSymbol(G, [GAP.evalstr("(1,5)") |> x -> (G isa GAP.GapObj ? x : cperm(symmetric_group(5), [1, 5]))], [], [[1]]))
        end
    end
    # matrix and polycyclic groups: the same rows that apply
    GL = general_linear_group(2, 3)
    a, b = gens(GL)[1], gens(GL)[2]
    @test a * b != b * a
    @test throws("H is not abelian", () -> BCSymbol(GL, [a, b], [], [[1, 0]]))
    @test throws("H is trivial", () -> BCSymbol(GL, [one(GL)], [], [[1]]))
    P = small_group(27, 3)
    pa, pb = gens(P)[1], gens(P)[2]
    comm_trivial = pa * pb == pb * pa
    @test comm_trivial || throws("H is not abelian", () -> BCSymbol(P, [pa, pb], [], [[1, 0]]))
    @test throws("zero character", () -> BCSymbol(P, [pa], [], [[0]]))
    @test throws("H is trivial", () -> BCSymbol(P, [one(P)], [], [[1]]))
end

@testset "T2b things the spec implies" begin
    S4 = symmetric_group(4)
    c3 = cperm(S4, [1, 2, 3]); c4 = cperm(S4, [1, 2, 3, 4])
    s = BCSymbol(S4, [c3], [], [[1], [1]])
    # coefficient zero is accepted and has no effect
    cls = BCClass(S4, 2); push!(cls, 0, s)
    @test is_zero(bc_image(cls))
    # empty ygens means Y trivial, ygens inside H change nothing
    s2 = BCSymbol(S4, [c3], [c3], [[1], [1]])
    s3 = BCSymbol(S4, [c3], [c3^2], [[1], [1]])
    x = bc_image(s, 2)
    @test x == bc_image(s2, 2) == bc_image(s3, 2)
    # preimage constructor equals the quotient constructor with the same data
    V = [cperm(S4, [1, 2]) * cperm(S4, [3, 4]), cperm(S4, [1, 3]) * cperm(S4, [2, 4])]
    q = BCSymbol(S4, [V[1]], [V[2]], [[1]])
    p = BCSymbol_preimage(S4, [V[1]], V, [[1]])
    @test bc_image(q, 2) == bc_image(p, 2)
    @test BCSymbol(S4, [V[1]], V, [[1]]).yg == BCSymbol(S4, [V[1]], V, [[1]]).yg
end

@testset "T7 alternating between two groups" begin
    S3 = symmetric_group(3); D7 = dihedral_group(PermGroup, 14)
    c3 = cperm(S3, [1, 2, 3]); r7 = first(filter(g -> order(g) == 7, collect(D7)))
    sa = BCSymbol(S3, [c3], [c3], [[1], [1]])
    sb = BCSymbol(D7, [r7], [r7], [[1], [1], [2]])
    xa = bc_image(sa, 2); xb = bc_image(sb, 3)
    for _ in 1:2
        @test bc_image(sa, 2) == xa
        @test bc_image(sb, 3) == xb
    end
    @test order(xa) == 2 && !is_zero(xb)
    # elements of different groups cannot be added
    @test throws("different group", () -> xa + xb)
end

@testset "T4 corrupted certificates" begin
    S3 = symmetric_group(3); c3 = cperm(S3, [1, 2, 3])
    x = bc_image(BCSymbol(S3, [c3], [c3], [[1], [1]]), 2)
    cert = certificate_nonzero(x)
    dir = mktempdir()
    good = joinpath(dir, "good.txt")
    write_certificate(good, cert)
    base = readlines(good)
    @test verify(good) && verify_with_group(read_certificate(good))
    # write a modified copy and return its path
    function variant(name, f)
        lines = f(copy(base))
        path = joinpath(dir, name * ".txt")
        write(path, join(lines, "\n") * "\n")
        return path
    end
    replace_line(lines, prefix, new) = (i = findfirst(l -> startswith(l, prefix), lines); lines[i] = new; lines)
    function bump_int(line, pos)
        w = split(line); w[pos] = string(parse(Int, w[pos]) + 1); return join(w, " ")
    end
    idx(prefix) = findfirst(l -> startswith(l, prefix), base)
    # (name, edit, expected verify result, expected verify_with_group result or nothing when the file cannot be read)
    cases = [
        ("f entry", ls -> (i = idx("f "); ls[i] = bump_int(ls[i], 2); ls), false),
        ("term coefficient", ls -> (i = idx("term "); ls[i] = bump_int(ls[i], 3); ls), false),
        ("perm entry", ls -> (i = idx("perm "); ls[i] = bump_int(ls[i], 3); ls), false),
        ("swap gen entries", ls -> begin
            i = idx("gen "); w = split(ls[i])
            tmp = w[2]; w[2] = w[3]; w[3] = tmp
            ls[i] = join(w, " "); ls
        end, false),
        ("delete gen line", ls -> (i = idx("gen "); deleteat!(ls, i); j = idx("ngens"); ls[j] = "ngens $(parse(Int, split(ls[j])[2]) - 1)"; ls), false),
        ("modulus", ls -> replace_line(ls, "modulus", "modulus 3"), false),
        ("n", ls -> replace_line(ls, "n ", "n 3"), false),
        ("block_d", ls -> replace_line(ls, "block_d", "block_d 6"), false),
    ]
    for (name, edit, want) in cases
        path = variant(replace(name, " " => "_"), edit)
        @test verify(path) == want
    end
    # corruptions the standalone verifier cannot see, caught by verify_with_group
    unseen = [
        ("fingerprint", ls -> replace_line(ls, "group_fingerprint", "group_fingerprint " * repeat("0", 64))),
        ("ggen", ls -> (i = idx("ggen "); ls[i] = "ggen (1,3)"; ls)),
        ("orbitsize", ls -> replace_line(ls, "block_orbitsize", "block_orbitsize 5")),
        ("no perms", ls -> begin
            filter!(l -> !startswith(l, "perm "), ls)
            replace_line(ls, "nperms", "nperms 0")
        end),
    ]
    for (name, edit) in unseen
        path = variant("unseen_" * name, edit)
        @test verify(path)                                   # the relations it can see still hold
        @test !verify_with_group(read_certificate(path))
    end
    # the real stabilizer action is nontrivial here, so dropping the perms must be caught by the group check only
    @test length(cert.perms) >= 1
    # unreadable files: verify returns false and never throws, read_certificate throws ArgumentError
    trunc = variant("truncated", ls -> ls[1:end-1])
    @test !verify(trunc)
    @test_throws ArgumentError read_certificate(trunc)
    wrong = variant("wrong_header", ls -> (ls[1] = "EBNZCERT 2"; ls))
    @test !verify(wrong)
    @test_throws ArgumentError read_certificate(wrong)
    empty_path = joinpath(dir, "empty.txt"); write(empty_path, "")
    junk = joinpath(dir, "junk.txt"); write(junk, "\0\xff garbage\nEND\n")
    @test !verify(empty_path) && !verify(junk)
    # standalone process: exit code and message
    verifier = joinpath(@__DIR__, "..", "verifier", "verify_nonzero.jl")
    function run_verifier(path)
        out = IOBuffer()
        proc = run(pipeline(ignorestatus(`$(Base.julia_cmd()) --startup-file=no $verifier $path`); stdout = out, stderr = devnull))
        return proc.exitcode, strip(String(take!(out)))
    end
    @test run_verifier(good) == (0, "VALID")
    code, msg = run_verifier(variant("proc_bad", ls -> (i = idx("f "); ls[i] = bump_int(ls[i], 2); ls)))
    @test code != 0 && startswith(msg, "INVALID")
end

@testset "certificates for matrix and polycyclic groups" begin
    P = small_group(27, 3)
    h = first(filter(g -> order(g) == 3, gens(P)))
    xp = bc_image(BCSymbol(P, [h], [], [[1]]), 2)
    @test !is_zero(xp)
    cert = certificate_nonzero(xp)
    @test verify(cert)
    # elements of a polycyclic group are not plain GAP data: no generators are written
    @test isempty(cert.ggens)
    @test throws("no group generators", () -> verify_with_group(cert))
    GL = general_linear_group(2, 3)
    found = nothing
    for g in collect(GL), betas in ([[1], [1]], [[1]], [[1], [2]])
        order(g) in (3, 4, 8) || continue
        x = bc_image(BCSymbol(GL, [g], [], betas), 2)
        is_zero(x) || (found = x; break)
    end
    @test found !== nothing
    cert = certificate_nonzero(found)
    @test verify(cert) && verify_with_group(cert)
    @test length(cert.ggens) == length(gens(GL))
end

end
