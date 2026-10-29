# Bit-vector based encoding for elements of free modules 
# over the polynomial ring 𝔽₃[x₁, …, xₙ] with n ≤ 63 
# and where every component is a monomial of the form 
# c*xᵃ with aᵢ∈ {0, 1}.
mutable struct BinVec
  entries::Vector{Tuple{UInt, UInt}} # entries are (i, e) with i the position in the module
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
  function BinVec()
    return new(Vector{Tuple{UInt, UInt}}())
  end

  function BinVec(pos::UInt, mon::UInt)
    return new([(pos, mon)])
  end
  
  function BinVec(list::Vector{Tuple{UInt, UInt}}; sort::Bool=true)
    sort && return new(sort!(list; by=first))
    return new(list)
  end
end

