@testset "simplicial_cohomology" begin
    K = torus()
    CZ = Oscar.SimplicialCoComplex(ZZ, K)

    @test typeof(CZ) <: Oscar.SimplicialCoComplex

    AK = SimplicialCohomologyRing(CZ)

    @test AK <: Oscar.SimplicialCohomologyRing

    @test base_ring(AK) == ZZ
end