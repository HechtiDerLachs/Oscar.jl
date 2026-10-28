@testset "Squarefree monomial resolutions" begin
  R, (x, y) = QQ[:x, :y]
  f = x*y
  v = Oscar.BinVec(f)
  @test "$(v)" == "1*[11]*e_1"
end

