using LinearAlgebra

@testset "Vietoris Rips coboundary maps" begin
	# Generate random points and compute their distance matrix
	# See https://samuelalbanie.com/files/Euclidean_distance_trick.pdf for the computation of the distance matrix
	p = rand(10, 3)
	gram = p * p'
	distances = sqrt.(diag(gram) .+ diag(gram)' .- 2 .* gram)
	# Generate the Vietoris-Rips coboundary matrices and check that they have coboundary property
	V = Oscar.vietoris_rips_complex(distances)
	δ = zero_matrix(QQ, 0, length(V.simplices))
	for _ in 1:5
		V, δ2 = Oscar.coboundary_map(V)
		@test iszero(δ * δ2)
		δ = δ2
	end
end
