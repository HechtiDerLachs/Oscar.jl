@testset "globally finite polynomial maps" begin
  R, (y,) = polynomial_ring(QQ, [:y])
  S, (x,) = polynomial_ring(QQ, [:x])

  f = x*(1-x^2)

  phi = hom(R, S, [f])

  Oscar._codomain_as_module(phi)

  R, (y1, y2) = polynomial_ring(QQ, [:y1, :y2])
  phi = hom(R, S, [x^2, x^3])

  M, to, from = Oscar._codomain_as_module(phi)
  h1 = rand(S, 1:10, 1:10, 1:10)
  h2 = rand(S, 1:10, 1:10, 1:10)
  @test from(to(h1^2+ h1*h2 + 7*h2)) == h1^2 + h1*h2 + 7*h2
end

@testset "Ae-codimension" begin
  S, (x, y) = QQ[:x, :y]
  R, (u, v, w) = QQ[:u, :v, :w]
  f = hom(R, S, [x, y^2, x*y])
  g = [one(S), y]

  prep = Oscar.MalgrangePreparator(f, g)

  prep(x)

  F = FreeMod(S, 2)
  Fprep = prep(F)
  Fprep(F[1])

  Oscar.ae_codimension(f)

  k = 5
  f = hom(R, S, [x, y^2, y^3 + x^(2*k+1)*y])

  @test Oscar.ae_codimension(f) == 10
end

