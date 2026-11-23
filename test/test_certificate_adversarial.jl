module TestCertificateAdversarial
include("g1_adversarial_helpers.jl")

@testset "Divisor characters and independently classified normal subgroups" begin
    for (name, base, quotient_order, in_pgl2) in (
        ("S4", matrix_group(S4_CODE), 24, true),
        ("A5", irreducible_three("AlternatingGroup(5)"), 60, true),
        ("PSL2F7", irreducible_three("PSL(2,7)"), 168, false))
        @testset "$name" begin
            rep = linrep(scalar_extension(base, 5))
            cls = plus_divisor_symbols(rep)
            @test length(cls.terms) == 2
            scalar = GG.E(5) * GG.One(rep.G)
            cgen = only(g for g in rep.C if rep.mats[g] == scalar)
            @test Set(s.beta[1][cgen] for (c,s) in values(cls.terms)) == Set([1//5,4//5])
            @test all(length(s.Y) == 5*quotient_order for (c,s) in values(cls.terms))
            for (c,s) in values(cls.terms)
                @test c == 1
                @test s.d == 2
                @test length(s.A) == 5
                @test length(s.beta) == 1
                @test isempty(s.gamma)
                result = certify_incompressible_dim3(s)
                @test result.certified
                @test length(result.cases) == 1
                case = only(result.cases)
                @test case.N_over_A == 1
                @test case.in_PGL2 == in_pgl2
                if in_pgl2
                    # The recorded subgroup is the preimage C5 times a Klein four.
                    @test case.witness == 20
                else
                    @test isnothing(case.witness)
                end
            end
            @test first(field_faithful(cls))
        end
    end
end

@testset "No false incompressibility for cyclic and S3 actions" begin
    for code in (C5_CODE, S3_CODE)
        rep = linrep(scalar_extension(matrix_group(code), 7))
        cls = plus_divisor_symbols(rep)
        for (c,s) in values(cls.terms)
            result = certify_incompressible_dim3(s)
            @test !result.certified
            expected_orders = code == C5_CODE ? Set([1,5]) : Set([1,3])
            @test Set(case.N_over_A for case in result.cases) == expected_orders
            @test all(case.in_PGL2 for case in result.cases)
            @test all(isnothing(case.witness) for case in result.cases)
        end
    end
    line = plus_divisor_symbols(linrep(scalar_extension(matrix_group(Q8_CODE), 5)))
    for (c,s) in values(line.terms)
        @test_throws ArgumentError certify_incompressible_dim3(s)
    end
end
end
