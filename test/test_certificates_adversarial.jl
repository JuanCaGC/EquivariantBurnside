module TestCertificatesAdversarial
using Test, Oscar, EquivariantBurnside
const B = EquivariantBurnside

function replace_line(text, key, transform)
    lines = split(chomp(text), '\n')
    i = findfirst(l -> startswith(l, key * " "), lines)
    isnothing(i) && error("Missing field $key")
    lines[i] = transform(lines[i])
    join(lines, "\n") * "\n"
end
function group_verdict(path)
    try
        B.verify_with_group(B.read_certificate(path))
    catch e
        println("Group verifier rejected with ", sprint(showerror, e))
        false
    end
end
function corrupt(path, original, label, transform, mode)
    modified = transform(original)
    @test modified != original
    write(path, modified)
    # File verification must report malformed arithmetic data with false, never throw.
    pure = B.verify(path)
    trusted = group_verdict(path)
    println("CORRUPTION ", label, " verify=", pure, " group=", trusted)
    if mode == :pure
        @test pure === false
    elseif mode == :group
        @test trusted === false
    elseif mode == :both
        @test pure === false
        @test trusted === false
    else
        @test pure === false || trusted === false
    end
end

@testset "Adversarial certificates" begin
    outdir = mktempdir()
    s3 = GAP.Globals.SymmetricGroup(3)
    h3 = GAP.evalstr("(1,2,3)")
    d7 = GAP.evalstr("DihedralGroup(IsPermGroup,14)")
    h7 = GAP.evalstr("First(AsList(DihedralGroup(IsPermGroup,14)), x->Order(x)=7)")
    x = bc_image(BCSymbol(s3, [h3], [], [[1], [1]]), 2)
    cls = BCClass(d7, 3)
    for w in ([1,1,2], [2,4,6], [2,3,6])
        push!(cls, BCSymbol(d7, [h7], [], [[v] for v in w]))
    end
    for (label, element) in (("s3", x), ("d7", bc_image(cls)))
        @test order(element) == 2
        cert = B.certificate_nonzero(element)
        @test B.verify(cert)
        @test B.verify_with_group(cert)
        path = joinpath(outdir, label * ".txt")
        B.write_certificate(path, cert)
        @test B.read_certificate(path) == cert
        @test B.verify(path)
    end
    original = read(joinpath(outdir, "s3.txt"), String)
    path = joinpath(outdir, "corrupt.txt")
    # Pure verifier must reject f modified at the nonzero term coordinate.
    term = split(first(filter(l -> startswith(l, "term "), split(original, '\n'))))
    pos = parse(Int, term[2])
    corrupt(path, original, "f", t -> replace_line(t, "f", l -> begin
        v = split(l)
        v[pos + 1] = string(1 - parse(Int, v[pos + 1]))
        join(v, " ")
    end), :pure)
    # Pure verifier must reject the doubled class of order two.
    corrupt(path, original, "coefficient", t -> replace_line(t, "term", l -> begin
        v = split(l)
        v[3] = string(2 * parse(Int, v[3]))
        join(v, " ")
    end), :pure)
    # Pure verifier must reject a permutation that does not fix the zero character.
    corrupt(path, original, "perm", t -> replace_line(t, "perm", l -> begin
        v = split(l)
        v[2] = "2"
        join(v, " ")
    end), :pure)
    # Pure verifier must reject an unsorted generator tuple.
    corrupt(path, original, "gen swap", t -> begin
        lines = split(chomp(t), '\n')
        i = findfirst(l -> startswith(l, "gen ") && length(unique(split(l)[2:end])) > 1, lines)
        v = split(lines[i])
        v[2], v[3] = v[3], v[2]
        lines[i] = join(v, " ")
        join(lines, "\n") * "\n"
    end, :pure)
    # Pure verifier must reject an incomplete generator enumeration.
    corrupt(path, original, "gen deletion", t -> begin
        lines = split(chomp(t), '\n')
        deleteat!(lines, findfirst(l -> startswith(l, "gen "), lines))
        replace_line(join(lines, "\n") * "\n", "ngens", l -> "ngens " * string(parse(Int, split(l)[2]) - 1))
    end, :pure)
    # Pure verifier must reject modulus one because every class evaluates to zero.
    corrupt(path, original, "modulus", t -> replace_line(t, "modulus", l -> "modulus 1"), :pure)
    # Only the group verifier must detect the missing inversion action of S3.
    corrupt(path, original, "perms deletion", t -> replace_line(join(filter(l -> !startswith(l, "perm "), split(chomp(t), '\n')), "\n") * "\n", "nperms", l -> "nperms 0"), :group)
    # Pure verifier must reject n inconsistent with generator tuple lengths.
    corrupt(path, original, "n", t -> replace_line(t, "n", l -> "n 3"), :pure)
    # Both verifiers must reject inconsistent dual order and block generator orders.
    corrupt(path, original, "block_d", t -> replace_line(t, "block_d", l -> "block_d 5"), :both)
    # Only the group verifier binds the fingerprint to the generating tuple.
    corrupt(path, original, "fingerprint", t -> replace_line(t, "group_fingerprint", l -> "group_fingerprint " * repeat("0", 64)), :group)
    # Only the group verifier sees a changed group generating tuple.
    corrupt(path, original, "ggen", t -> replace_line(t, "ggen", l -> "ggen ()"), :group)
    # Spec ambiguous: neither verifier explicitly promises to check orbit size.
    corrupt(path, original, "block_orbitsize", t -> replace_line(t, "block_orbitsize", l -> "block_orbitsize 999"), :either)
    # Pure parser must reject a truncated version 1 document.
    corrupt(path, original, "truncated", t -> replace(t, r"END\s*$" => ""), :pure)
    # Pure parser must reject an unknown header.
    corrupt(path, original, "header", t -> replace(t, "EBNZCERT 1" => "NOTACERT 1"), :pure)
    write(joinpath(outdir, "invalid.txt"), replace(original, "EBNZCERT 1" => "NOTACERT 1"))

    pc = small_group(27, 3)
    h = first(filter(g -> !isone(g), gens(pc)))
    px = bc_image(BCSymbol(pc, [h], [], [[1], [1]]), 2)
    @test !is_zero(px)
    pc_cert = B.certificate_nonzero(px)
    pc_path = joinpath(outdir, "pc.txt")
    B.write_certificate(pc_path, pc_cert)
    has_ggen = any(l -> startswith(l, "ggen "), readlines(pc_path))
    println("PC CERTIFICATE has_ggen=", has_ggen)
    if has_ggen
        @test B.verify_with_group(pc_cert)
    else
        @test_throws ArgumentError B.verify_with_group(pc_cert)
        err = try
            B.verify_with_group(pc_cert)
            nothing
        catch e
            e
        end
        @test err isa ArgumentError && occursin("no group generators", sprint(showerror, err))
    end
end

# Source constraints are checked after the independent first execution.
begin
    @testset "Standalone source constraints" begin
        source = read(joinpath(@__DIR__, "..", "verifier", "verify_nonzero.jl"), String)
        @test !occursin(r"\b(using|import|include)\b", source)
        @test length(split(chomp(source), '\n')) <= 150
    end
end
end
