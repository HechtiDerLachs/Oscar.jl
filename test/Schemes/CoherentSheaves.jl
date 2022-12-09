@testset "coherent sheaves" begin
    IP2 = projective_space(QQ, 2)
    X = covered_scheme(IP2)
    OX = StructureSheafOfRings(X)
    L = tautological_bundle(IP2)
    U = affine_charts(X)
    L(U[1])
    C = default_covering(X)
    (U12, U21) = glueing_domains(C[U[1], U[2]])
    rho = L(U[1], U21)
    @test rho(L(U[1])[1]) == inv(gens(OO(U21))[1])*L(U21)[1]
    W = PrincipalOpenSubset(U[2], [complement_equation(U21), gens(OO(U[2]))[2]])
    rr = L(U[1], W)
    rrr = L(U21, W)
    @test rr == compose(rho, rrr)

    M1 = oscar.cotangent_sheaf(X)
    rho = M1(U[1], U21)
    @test rho(M1(U[1])[1]) in M1(U21)
end
