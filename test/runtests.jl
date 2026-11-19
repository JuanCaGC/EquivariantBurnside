using Test

@testset "EquivariantBurnside" begin
    @testset "structure_oscar" begin
        include("test_structure_oscar.jl")
    end
    @testset "validate" begin
        include("test_validate.jl")
    end
    @testset "certificates" begin
        include("test_certificates.jl")
    end
    @testset "bcclass" begin
        include("test_bcclass.jl")
    end
    @testset "ex75" begin
        include("test_ex75.jl")
    end
    @testset "dcp" begin
        include("test_dcp.jl")
    end
    @testset "tom" begin
        include("test_tom.jl")
    end
    @testset "symbols core" begin
        include("test_symbols_core.jl")
    end
    @testset "symbols errors and certificates" begin
        include("test_symbols_errors.jl")
    end
    @testset "symbols adversarial (independent, Codex)" begin
        include("test_symbols_adversarial.jl")
    end
    @testset "certificates adversarial (independent, Codex)" begin
        include("test_certificates_adversarial.jl")
    end
end
