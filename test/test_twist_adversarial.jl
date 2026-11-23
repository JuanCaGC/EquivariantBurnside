module TestTwistAdversarial
include("g1_adversarial_helpers.jl")

@testset "Scalar twists fix the nonabelian direct factor" begin
    base = matrix_group(S4_CODE)
    for n in (5, 7, 8)
        rep = linrep(scalar_extension(base, n))
        for k in 1:n-1
            if gcd(k,n) != 1
                @test_throws ArgumentError epsilon_twist(rep, base, k)
                continue
            end
            f = epsilon_twist(rep, base, k)
            els = rep.els
            @test length(Set(f(g) for g in els)) == length(els)
            for g in els, h in gens(rep.P)
                @test f(g*h) == f(g)*f(h)
            end
            for g in els
                if rep.mats[g] in base
                    @test f(g) == g
                end
                if g in rep.C
                    @test f(g) == g^k
                end
            end
            answer = compare_plus_divisors(rep, f)
            @test answer.equal == (k in (1, n-1))
            @test answer.certified
        end
        @test_throws ArgumentError epsilon_twist(rep, base, 0)
        @test_throws ArgumentError epsilon_twist(rep, scalar_extension(base,n), 1)
        trivial = GG.TrivialSubgroup(base)
        @test_throws ArgumentError epsilon_twist(rep, trivial, 1)
    end
end

@testset "The certified flag is false when the plane action has no Klein obstruction" begin
    # S3 permuting the coordinates has no Klein four subgroup in its image, so no divisor symbol of the class of P(1 + V) is
    # certified incompressible and the flag must be false, also for the twist k = 2 of the scalar group C5
    base = matrix_group(S3_CODE)
    rep = linrep(scalar_extension(base, 5))
    f = epsilon_twist(rep, base, 2)
    answer = compare_plus_divisors(rep, f)
    @test !answer.certified
end
end
