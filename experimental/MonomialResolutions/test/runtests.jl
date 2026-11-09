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

@testset "more resolutions" begin
n = 10
sample = [UInt(rand(1:2^(n-1))) for _ in 1:2^(n-4)]
bv = interreduce!(Oscar.BinVec.(sample))
R, x = polynomial_ring(QQ, n)
F = FreeMod(R, 1)
v = F.(bv)
syz_count = 0
while !isempty(bv)
  syz_count += 1
  @show syz_count
  @time bw = Oscar._syzygies(bv)
  #@time bw = interreduce!(Oscar.groebner_basis!(bw))
  @time bw = interreduce!(bw)
  @time w = syzygy_generators(v)
  is_empty(bw) && break
  F = parent(first(w))
  ww = F.(bw)
  I = sub_object(F, w)
  J = sub_object(F, ww)
  tst = I == J
  @test tst
  !tst && break
  bv = bw
  v = ww
end
  
end

@testset "even more resolutions" begin
n = 14
sample = [UInt(rand(1:2^(n-1))) for _ in 1:2^(n-2)]
bv = interreduce!(Oscar.BinVec.(sample))
R, x = polynomial_ring(GF(3), n)
F = FreeMod(R, 1)
v = F.(bv)
res, _ = free_resolution(Oscar.SimpleFreeResolution, sub_object(F, v));
@time res[n];
sres = simplify(res);
@time bres = Oscar.resolution!(bv);
alt_res = simplify(Oscar._to_resolution(bres, R));
[ngens(sres[i]) for i in 0:length(bres)-1]
[ngens(alt_res[i]) for i in 1:length(bres)]

syz_count = 0
@time while !isempty(bv)
  syz_count += 1
  @show syz_count
  @time bw = Oscar._syzygies(bv)
  #@time bw = interreduce!(Oscar.groebner_basis!(bw))
  @time bw = interreduce!(bw)
  is_empty(bw) && break
  bv = bw
end
  
end

