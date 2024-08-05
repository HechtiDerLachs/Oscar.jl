@testset "ExteriorAlgebra" begin
  @testset "exterior_algebra constructor, R=$R, n=$n" for (R, n) in [
    (QQ, 1)   # --> special case (is commutative)
    (QQ, 2)   # --> first general case
    (QQ, 99)  # --> Also tried with 999 indets, but takes a long time [~19s]
    (GF(2), 2)  # BUG??  not recognized as commutative!!
    (GF(3), 4)
    (residue_field(ZZ, 2)[1], 2)
    (residue_field(ZZ, 3)[1], 4)
    (GF(1180591620717411303449), 2)
    (residue_field(ZZ, 1180591620717411303449)[1], 2)
    (ZZ, 3) # coeffs not field
    (residue_ring(ZZ, 4)[1], 3) # coeffs not field
  ]
    A, g = exterior_algebra(R, n)
    @test A isa PBWAlgQuo
    @test g isa Vector{elem_type(A)}
    @test length(g) == n
    @test ngens(A) == n
    @test gens(A) == g
  end

  @testset "constructor with no variables" begin
    @test_throws ArgumentError exterior_algebra(QQ, 0)
    @test_throws ArgumentError exterior_algebra(QQ, Symbol[])
    @test_throws ArgumentError exterior_algebra(ZZ, 0)
    @test_throws ArgumentError exterior_algebra(ZZ, Symbol[])
  end

  @testset "computational test, R=$R" for R in [QQ, ZZ]
    E, (e1, e2, e3, e4, e5, e6) = exterior_algebra(R, 6)
    fac1 =
      e1 +
      2 * e1 * e2 +
      3 * e1 * e2 * e3 +
      4 * e1 * e2 * e3 * e4 +
      5 * e1 * e2 * e3 * e4 * e5 +
      6 * e1 * e2 * e3 * e4 * e5 * e6
    fac2 =
      e6 +
      2 * e5 * e6 +
      3 * e4 * e5 * e6 +
      4 * e3 * e4 * e5 * e6 +
      5 * e2 * e3 * e4 * e5 * e6 +
      6 * e1 * e2 * e3 * e4 * e5 * e6
    prod12 = fac1 * fac2
    prod21 = fac2 * fac1
    expected12 =
      35 * e1 * e2 * e3 * e4 * e5 * e6 +
      4 * e1 * e2 * e3 * e4 * e6 +
      6 * e1 * e2 * e3 * e5 * e6 +
      6 * e1 * e2 * e4 * e5 * e6 +
      4 * e1 * e3 * e4 * e5 * e6 +
      3 * e1 * e2 * e3 * e6 +
      4 * e1 * e2 * e5 * e6 +
      3 * e1 * e4 * e5 * e6 +
      2 * e1 * e2 * e6 +
      2 * e1 * e5 * e6 +
      e1 * e6
    expected21 =
      -3 * e1 * e2 * e3 * e4 * e5 * e6 +
      4 * e1 * e2 * e3 * e4 * e6 +
      6 * e1 * e2 * e3 * e5 * e6 +
      6 * e1 * e2 * e4 * e5 * e6 +
      4 * e1 * e3 * e4 * e5 * e6 - 3 * e1 * e2 * e3 * e6 + 4 * e1 * e2 * e5 * e6 -
      3 * e1 * e4 * e5 * e6 +
      2 * e1 * e2 * e6 +
      2 * e1 * e5 * e6 - e1 * e6
    @test is_zero(prod12 - expected12)
    @test is_zero(prod21 - expected21)

    @test is_zero(fac1 * prod12)
    @test is_zero(prod12 * fac1)
    @test is_zero(fac2 * prod12)
    @test is_zero(prod12 * fac2)

    @test is_zero(fac1 * prod21)
    @test is_zero(prod21 * fac1)
    @test is_zero(fac2 * prod21)
    @test is_zero(prod21 * fac2)
  end
end

@testset "BGGHelpers" begin 
  R, (t,) = polynomial_ring(QQ, [:t])
  S, (x, y, z) = graded_polynomial_ring(R, [:x, :y, :z])
  E = Oscar._exterior_algebra(S)

  h = Oscar.BGGHelper(E, S, 3)
  morphism(h)

  f = 2*x^3 + 7*x*y^2 - 5*x*y*z
  v = h(f)
  ff = h(v)
  f == ff

  g = x^3 
  v = h(g)
  phi = morphism(h)
  w = phi(domain(phi)(map_entries(E, v)))
  for (i, c) in coordinates(w)
    if i == 1
      @test h(sparse_row(R, [i], [one(R)]), :codomain) == x^4
      @test c == gen(E, 1)
    elseif i == 2
      @test h(sparse_row(R, [i], [one(R)]), :codomain) == x^3*y
      @test c == gen(E, 2)
    elseif i == 3
      @test h(sparse_row(R, [i], [one(R)]), :codomain) == x^3*z
      @test c == gen(E, 3)
    end
  end

  K = kernel(phi)
  res = resolution(phi)
  @test !iszero(res[2])
end

