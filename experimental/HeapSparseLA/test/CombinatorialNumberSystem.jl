@testset "Combinatorial number system: encoding and decoding" begin
	s = [2, 6, 9, 11]
	@test s == Oscar.decode(Oscar.encode(s), length(s) - 1)
	@test 49 == Oscar.encode(Oscar.decode(49, 3))
end
