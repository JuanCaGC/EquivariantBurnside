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
    @testset "transport and automorphisms" begin
        include("test_transport.jl")
    end
    @testset "audit of the engine against the definition" begin
        include("test_audit_theta2.jl")
    end
    @testset "restriction correction: models and Example 7.5" begin
        include("test_phi_models.jl")
    end
    @testset "toric surfaces and affine actions" begin
        include("test_toric.jl")
    end
    @testset "fixed loci of affine actions" begin
        include("test_toric_loci.jl")
    end
    @testset "toric adversarial (independent, Codex)" begin
        include("test_toric_adversarial.jl")
    end
    @testset "fixed loci adversarial (independent, Codex)" begin
        include("test_toric_loci_adversarial.jl")
    end
    @testset "transport adversarial (independent, Codex)" begin
        include("test_transport_adversarial.jl")
    end
    @testset "correction adversarial (independent, Codex)" begin
        include("test_correction_adversarial.jl")
    end
    @testset "toric surfaces with reflections" begin
        include("test_toric_reflections.jl")
    end
    @testset "toric reflections adversarial" begin
        include("test_toric_reflections_adversarial.jl")
    end
    @testset "toric glide reflection boundary points" begin
        include("test_toric_glide.jl")
    end
    @testset "projective line actions" begin
        include("test_projective_line.jl")
    end
    @testset "indexed symbols and psi, tau, eta" begin
        include("test_indexed.jl")
    end
    @testset "indexed omega, restriction and product" begin
        include("test_indexed_ops.jl")
    end
    @testset "recursion for P(V)" begin
        include("test_recursion.jl")
    end
    @testset "incompressible part of the class" begin
        include("test_incompressible.jl")
    end
end
