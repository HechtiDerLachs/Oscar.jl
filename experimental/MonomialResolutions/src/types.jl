# Bit-vector based encoding for elements of free modules 
# over the polynomial ring 𝔽₃[x₁, …, xₙ] with n ≤ 63 
# and where every component is a monomial of the form 
# c*xᵃ with aᵢ∈ {0, 1}.
mutable struct BinVec{CT}
  parent::Field
  entries::Vector{Union{Tuple{UInt, UInt, CT}, Tuple{UInt, UInt, Nothing}}} # entries are (i, e) with i the position in the module
                                     # and e the bit-vector with the first bit encoding 
                                     # the coefficient ±1 and the remainder the exponent 
                                     # vector a as above
  #
  # Example: -x₁x₃ ⋅e₁ + x₂⋅e₅ is encoded as [(1, 1 + 2 + 8), (5, 0 + 4)]. 
  #                                            |  |   |   |    |  |   |
  #   position first term ---------------------+  |   |   |    |  |   | 
  #   sign first term ----------------------------+   |   |    |  |   |
  #   non-zero exponents first term ------------------+---+    |  |   |
  #   position second term ------------------------------------+  |   |
  #   sign second term -------------------------------------------+   |
  #   non-zero exponents second term ---------------------------------+
  function BinVec(parent::Field)
    CT = elem_type(parent)
    return new{CT}(parent, Vector{Union{Tuple{UInt, UInt, CT}, Tuple{UInt, UInt, Nothing}}}())
  end

  function BinVec(parent::Field, pos::UInt, mon::UInt)
    CT = elem_type(parent)
    return new{CT}(parent, Union{Tuple{UInt, UInt, CT}, Tuple{UInt, UInt, Nothing}}[(pos, mon, nothing)])
  end
  
  function BinVec(parent::Field, pos::UInt, mon::UInt, coeff)
    CT = elem_type(parent)
    if is_one(coeff)
      return new{CT}(parent, Union{Tuple{UInt, UInt, CT}, Tuple{UInt, UInt, Nothing}}[(pos, mon << 1, nothing)])
    elseif coeff == -1
      return new{CT}(parent, Union{Tuple{UInt, UInt, CT}, Tuple{UInt, UInt, Nothing}}[(pos, (mon << 1) + UInt(1), nothing)])
    end
    return new{CT}(parent, Union{Tuple{UInt, UInt, CT}, Tuple{UInt, UInt, Nothing}}[(pos, mon << 1, coeff)])
  end
  
  function BinVec(parent::Field, pos::UInt, mon::UInt, ::Nothing)
    CT = elem_type(parent)
    return new{CT}(parent, Union{Tuple{UInt, UInt, CT}, Tuple{UInt, UInt, Nothing}}[(pos, mon << 1, nothing)])
  end
end

mutable struct SquarefreeMonomialResolution{T, CT}
  I::MPolyIdeal{T}
  g::Vector{BinVec{CT}}
  res::Vector{Vector{BinVec{CT}}}
  degs::Vector{Vector{UInt}}
  deg_buckets::Dict{Int, Dict}
  graded_parts::Dict{UInt, Dict}
  betti_numbers::Dict{Tuple{Int, UInt}, Int}

  function SquarefreeMonomialResolution(I::MPolyIdeal{T}) where {T}
    kk = coefficient_ring(base_ring(I))
    return new{T, elem_type(kk)}(I)
  end
end

