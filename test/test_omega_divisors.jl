module TestOmegaDivisors
include("g1_adversarial_helpers.jl")

# Ignore fields only, using the same simultaneous conjugation key as compare_fields.
function divisor_sum(cls)
    out = Dict{Any,Int}()
    for (c, s) in values(cls.terms)
        s.d == cls.n - 1 && length(s.beta) == 1 || continue
        k = minimum(EB._ikey(cls, s, g)[1:6] for g in cls.elems)
        out[k] = get(out, k, 0) + c
    end
    filter!(p -> last(p) != 0, out)
end

function check_fields(rep, cls, name)
    @test cls.n == 3
    @test isempty(cls.I)
    @test first(field_faithful(cls))
    for (c, s) in values(cls.terms)
        @test c > 0
        @test s.d == 2 && length(s.beta) == 1 && isempty(s.gamma)
        @test !isempty(s.F)
        @test sum(f.dim - 1 for f in s.F) == 2
        for f in s.F
            @test Set(keys(f.mat)) == Set(s.Y)
            @test Set(keys(f.inv)) == Set(s.Y)
            for g in s.Y
                @test projective_invariant(f.mat[g]) == f.inv[g]
                # Check every pair, rather than closure on generators.
                for h in s.Y
                    @test f.mat[g*h] == f.mat[g]*f.mat[h]
                end
            end
        end
        sig = field_fixed_signature(s)
        @test get(sig, Set(s.A), false)
        for (B, fixed) in sig, (B2, fixed2) in sig
            fixed && issubset(B2, B) && @test fixed2
        end
        @test compare_fields(cls, s, deepcopy(s)) == :equal
        certificate = certify_incompressible_dim3(s)
        @test !certificate.certified
        # A scalar fixing the first block pointwise is the identity on V.
        @test intersect(Set(s.A), Set(rep.C)) == Set([one(rep.P)])
        if length(rep.C) > 1
            @test all(Set(a^g for a in s.A) != Set(rep.C) for g in rep.els)
        end
    end
end

@testset "Omega agreement with the full recursion" begin
    # D4 has order eight and acts faithfully on a plane plus a trivial line.
    d4 = "Group(DiagonalMat([E(4),-E(4),1]),[[0,1,0],[1,0,0],[0,0,1]])"
    for (name, m, code) in (("C5xS3",5,S3_CODE), ("C5xA4",5,A4_CODE),
                             ("C3xS3",3,S3_CODE), ("C4xD4",4,d4))
        started = time()
        rep = linrep(scalar_extension(matrix_group(code),m))
        psi = plus_divisor_symbols(rep)
        @test psi == plus_divisor_symbols(rep, omega=false)
        name == "C5xS3" && @test length(psi) == 2
        full = projective_plus_class(rep)
        combined = plus_divisor_symbols(rep, omega=true)
        @test divisor_sum(full) == divisor_sum(combined)
        omega = omega_divisor_symbols(rep)
        @test !isempty(omega.terms)
        @test divisor_sum(combined) == divisor_sum(psi + omega)
        check_fields(rep, omega, name)
        println("SMALL $name full_divisors=$(length(divisor_sum(full))) psi=$(length(psi)) omega=$(length(omega)) seconds=$(round(time()-started,digits=3))")
        flush(stdout)
    end
end

@testset "Omega reference counts and block fields" begin
    for (name, m, kind, expected) in (
        ("C5xS4",5,:S4,[(2,20),(2,40),(5,120),(5,120)]),
        ("C5xA5",5,:A5,[(2,20),(5,300),(5,300)]),
        ("C7xA5",7,:A5,[(2,28),(7,420),(7,420)]))
        started = time()
        base = kind == :S4 ? EB.DCP.standard_symmetric(4) : irreducible_three("AlternatingGroup(5)")
        rep = linrep(scalar_extension(base,m))
        combined = plus_divisor_symbols(rep, omega=true)
        elapsed = time()-started
        @test sort([(length(s.A),length(s.Y)) for (_,s) in values(combined.terms)]) == expected
        @test all(c == 1 for (c,_) in values(combined.terms))
        name == "C5xS4" && @test elapsed < 300
        omega = omega_divisor_symbols(rep)
        check_fields(rep, omega, name)
        for (_,s) in values(omega.terms)
            # The standard S4 plane block comes first only for the order 20 normalizer.
            dims = sort([f.dim for f in s.F])
            @test dims == (name == "C5xS4" && length(s.Y) == 20 ? [3] : [2,2])
        end
        println("REFERENCE $name pairs=$expected coefficients=$(sort([c for (c,_) in values(combined.terms)])) construction_seconds=$(round(elapsed,digits=3)) total_seconds=$(round(time()-started,digits=3))")
        flush(stdout)
    end
end

@testset "Omega supported dimension" begin
    for d in (2,4)
        rep = linrep(matrix_group("Group(E(5)*IdentityMat($d))"))
        @test_throws ArgumentError omega_divisor_symbols(rep)
        @test_throws ArgumentError plus_divisor_symbols(rep, omega=true)
        @test length(plus_divisor_symbols(rep)) == 2
    end
end
end
