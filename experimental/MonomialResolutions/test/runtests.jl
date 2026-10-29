@testset "Squarefree monomial resolutions" begin
  R, (x, y) = QQ[:x, :y]
  f = x*y
  v = Oscar.BinVec(f)
  @test "$(v)" == "1*[11]*e_1"
  v = Oscar.BinVec(-f)
  @test "$(v)" == "-1*[11]*e_1"
  F = FreeMod(R, 3)
  u = x*F[1] + F[2]
  v = x*F[1] + y*F[2]
  w = x*F[1] + x*y*F[3]
  vv = Oscar.BinVec(v)
  ww = Oscar.BinVec(w)
  uu = Oscar.BinVec(u)
  @test "$(vv - ww)" == "1*[01]*e_2 + -1*[11]*e_3" 
  @test "$(5*uu)" ==  "-1*[11]*e_1 + -1*[01]*e_2"
  
  g = Oscar.BinVec.([x, y, x*y])
  @test length(Oscar.interreduce!(g)) == 2
  gb = Oscar.groebner_basis!(g)
  s1 = Oscar._syzygies(gb)
  s2 = Oscar._syzygies(s1)
  @test is_one(length(s2))
  
  #=
  I = load("some_file_with_monomial_generators.mrdi")
  g = Oscar.BinVec.(I[1:20])
  g = Oscar.interreduce!(Oscar.groebner_basis!(g))
  s = [g]
  while !is_empty(last(s))
    @show "next"
    @time next = Oscar._syzygies(last(s))
    @show length(next)
    @time next = Oscar.interreduce!(next)
    @show length(next)
    push!(s, next)
  end
  =#
  
end

