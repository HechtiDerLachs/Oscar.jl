@testset "comparison from orderings" begin
  R, (x,y,z) = QQ["x", "y", "z"]
  o = negdegrevlex([z])*degrevlex([x,y])
  lt = lt_from_ordering(o)
  lead_t = leading_term_from_ordering(o)
  lead_c = leading_coefficient_from_ordering(o)
  lead_e = leading_exponent_vector_from_ordering(o)

  f = -x^2 + 2*y^3 -5*x^5*z^2
  
  @test lead_t(f) == 2*y^3
  @test lead_c(f) == QQ(2)
  @test lead_e(f) == [0, 3, 0]

  g = 7*x^2*y*z^3

  @test lt(g, f) == true
  @test lt(f, g) == false
end
