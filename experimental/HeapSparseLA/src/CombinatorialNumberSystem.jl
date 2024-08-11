# The combinatorial number system can encode a k-set of non-negative integers (viz an abstract simplex)
# between 1 and N by integers between 1 and binom(N, k).
# For compatibility reasons, we let vertices be 1-based, and the CNS encoding be 0-based.
# For combinatorial number system, see https://en.wikipedia.org/wiki/Combinatorial_number_system
# Algorithms taken from https://gitlab.com/flenzen/2pac/-/blob/main/CliqueComplex.cpp

#TODO Replace binomial by look-up-table version.
#TODO Replace Int by UInt
#TODO Maybe change to 1-based CNS encoding.

""" Encode simplex `xs` (ascendingly sorted list of 0-based vertices) in CNS."""
function encode(xs::Vector{Int})
  @req all(xs .> 0) "Can only decode positive numbers."
	@req issorted(xs) "xs must be sorted" #TODO Remove for efficiency?
	sum(binomial(v - 1, i) for (i, v) in enumerate(xs)) + 1
end

import Base.Iterators.countfrom
""" Decode a `dim`-dimensional simplex from CNS. Returns ascendingly sorted list of 1-indexed vertices."""
function decode(σ::Int, dim::Int)
  @req σ > 0 "Can only decode positive numbers."
  σ -= 1
	xs = Vector{Int}(undef, dim + 1) # The decoded vertices
	i = dim + 1 # Index of the decoded vertex in xs
	while i >= 1
		v = 1::Int # The next decoded vertex is the largest v with binom(v, i) <= σ
		while binomial(v - 1, i) <= σ
			v += 1
		end
		v -= 1
		xs[i] = v
		σ -= binomial(v - 1, i) # Now σ = {σ[1], ..., σ[i-1]}
		i -= 1
	end
	return xs
end

""" Returns the encoded faces of an encoded, `dim`-dimensional simplex in ascending order."""
function faces(σ::Int, dim::Int)
  @req σ > 0 "Can only decode positive numbers."
	if dim == 0
		return Vector{Int}()
	end
  σ -= 1
	fs = Vector{Int}() # faces
	sizehint!(fs, dim + 1)
	ρ = 0::Int
	i = dim + 1 # Index of vertex in simplex
	while i >= 1
		# Decode σ
		v = 1
		while binomial(v - 1, i) <= σ
			v += 1
		end
		v -= 1
		σ -= binomial(v - 1, i)
		push!(fs, ρ + σ) # The new face is [...,σ[i-1], σ[i+1],...]
		i -= 1
		ρ += binomial(v - 1, i)
	end
	return fs
end
