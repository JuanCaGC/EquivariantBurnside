using Test

@testset "EquivariantBurnside" begin
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
end
