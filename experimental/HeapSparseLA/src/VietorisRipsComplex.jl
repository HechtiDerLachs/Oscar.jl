# Generates the coboundary matrices of a diameter-filtered Vietoris-Rips complex.
# A Vietoris-Rips complex on a point cloud X is the abstract simplicial complex
# VR(X) ≔ 2^X. It is filtered by the diameter diam σ ≔ max{d(x, y) | x, y ∈ σ}.
# In practise, one truncates VR(X) at a fixed cutoff value t, i.e.,
# VR(X) ≔ {σ ∈ 2^X | diam σ ≤ t}.

#TODO Use UInt instead of Int, where applicable.
#TODO Take diameter into consideration

include("CombinatorialNumberSystem.jl")

""" Represents one stage during the computation of Vietoris-Rips coboundary maps."""
struct VietorisRipsComplex
	distances::Array{Float64, 2}
  #TODO Probably, we want the neighbors in order of increasing distances:
  # This would at least create the cofaces of each simplex in the correct order.
  # How to we create the list of next-dim simplices in the correct order?
	neighbors::Vector{Vector{Int}}
	dimension::Int
	simplices::Vector{Tuple{Float64, Int}}
end

"""
	vietoris_rips_complex(distances[, cutoff])
	
Creates a new Vietoris-Rips complex. If `cutoff` is a finite value, then all points
with distance larger or equal `cutoff` are considered not adjacent. For reasonably
large point clouds, one wants to set a point cloud."""
function vietoris_rips_complex(distances::Array{Float64, 2}, cutoff = Inf::Float64)
  #TODO Beyond maximum(distances), the Vietoris-Rips complex is contractible, so this would make a natural cutoff value.
	@req is_symmetric(distances) && all(distances .>= 0) "Matrix must be a distance matrix"
	n = size(distances, 1)
	VietorisRipsComplex(
		distances, # distance matrix
		[[j for j in 1:n if distances[i, j] < cutoff && i != j] for i in 1:n], # list (length n) of lists of the neighbors of the points
    0, # dimension
		collect(zip(Iterators.repeated(0), 1:n)), # list of pairs (0-dim simplices, their diameters)
	)
end


"""
	coboundary_map(K :: VietorisRipsComplex)
	
The next coboundary map of a Vietoris-Rips complex.

Returns the next piece of data, plus the actual coboundary matrix.

# Examples
```jldoctest
julia> distance_matrix = [0.0 1.0 2.0 3.0; 1.0 0.0 1.0 2.0; 2.0 1.0 0.0 1.0; 3.0 2.0 1.0 0.0];

julia> V = Oscar.vietoris_rips_complex(distance_matrix);

julia> V, δ0 = Oscar.coboundary_map(V); δ0
[ 1    1    0    1    0    0]
[-1    0    1    0    1    0]
[ 0   -1   -1    0    0    1]
[ 0    0    0   -1   -1   -1]

julia> V, δ1 = Oscar.coboundary_map(V); δ1
[ 1    1    0    0]
[-1    0    1    0]
[ 1    0    0    1]
[ 0   -1   -1    0]
[ 0    1    0   -1]
[ 0    0    1    1]
```"""
function coboundary_map(K::VietorisRipsComplex)
	# Algorithm taken from https://gitlab.com/flenzen/2pac/-/blob/main/CliqueComplex.cpp
	coboundary_columns = [Vector{Tuple{Float64, Int, Int}}() for _ in 1:length(K.simplices)]
	simplices_next_dim = Vector{Tuple{Float64, Int}}()
	index_of_simplex_next_dim = Dict{Int, Int}()

	for (column_index, (diam, σ)) in enumerate(K.simplices)
		if K.dimension == 0
			# σ = {v} = v is a vertex.
			for n in K.neighbors[σ]
				coface = encode(sort([σ, n]))
				diameter = K.distances[σ, n]
				push!(coboundary_columns[column_index], (diameter, coface, n < σ ? -1 : 1))
        # Store all edges exactly once, in the correct order (see below for explanation)
        if n < σ
          push!(simplices_next_dim, (diameter, coface))
        end
			end
		else
			# σ = encode(xs) is a higher dimensional simplex
			xs = decode(σ, K.dimension)
			# Iterate through neighbors of ith and i+1st vertex in xs in parallel until a common neighbour is found.
			# If indices[i] has been incremented, it is out of sync with neighbor of i-1st vertex. Therefore, continue with i-1 and i.
			# Otherwise, continue with i+1, i+2. Eventually, we have a common neighbor of all vertices in σ,
			# viz the apex of a coface.
			neighbor_indices = [1 for _ in 1:length(xs)]
			i = 1
			while neighbor_indices[i] <= length(K.neighbors[xs[i]]) && neighbor_indices[i+1] <= length(K.neighbors[i+1])
				if K.neighbors[xs[i]][neighbor_indices[i]] < K.neighbors[xs[i+1]][neighbor_indices[i+1]]
					# The i-th neighbor index is behind
					neighbor_indices[i] += 1
					if i > 1
						i -= 1
					end
				elseif K.neighbors[xs[i]][neighbor_indices[i]] > K.neighbors[xs[i+1]][neighbor_indices[i+1]]
					neighbor_indices[i+1] += 1
				elseif (i += 1) == length(xs)
					# All indices[1],...,indices[i] point to the same common neighbor of all vertices xs,
					# so we have found a coface of σ
					apex = K.neighbors[xs[i]][neighbor_indices[i]]
					diameter = maximum(K.distances[v, apex] for v in xs; init = diam)
					coface = encode(sort([xs; [apex]]))
					coeff = 1
					for v in xs
						if v > apex
							break
						else
							coeff *= -1
						end
					end
					push!(coboundary_columns[column_index], (diameter, coface, coeff))
          # We also want to create a list of all next-dimensional simplices. We add a simplex to that list if 
          # the apex is the first vertex of the coface. This ensures uniqueness, and after thinking a while, also
          # produces simplices in the correct (lex) order.
          # Note that this is the only not thread-safe part.
          if apex < xs[1]
            push!(simplices_next_dim, (diameter, coface))
          end
					# Continue with finding more cofaces
					i = 1
					neighbor_indices[i] += 1
				end
			end
			# At this point, there are no more cofaces
		end
	end
  # Proably, the most natural way to regard the Vietoris-Rips coboundary matrix is the following:
  # it is a sparse matrix, with entries (diameter, simplex id in cns, coefficient), where the diameter
  # is only relevant for sorting. It is then a separate task to build the list of next-dimensional simplices.
  # However, this does not fit so nicely in the more general sparse matrix framework as of now.
  # Therefore, we re-order the simplices by grades.
  #index_to_simplex = [σ for (_, σ) in sort(simplices_next_dim)]
  sort!(simplices_next_dim)
  index_of_simplex_next_dim = Dict(σ => i for (i, (_, σ)) in enumerate(simplices_next_dim))

	#TODO Replace by (heap)-sparse matrix
	mat = zero_matrix(QQ, length(K.simplices), length(simplices_next_dim))
	for (j, column) in enumerate(coboundary_columns)
		for (_, i, coeff) in column
      mat[j, index_of_simplex_next_dim[i]] = coeff
		end
	end

	return VietorisRipsComplex(
		K.distances,
		K.neighbors,
		K.dimension + 1,
    simplices_next_dim
	), mat
end

