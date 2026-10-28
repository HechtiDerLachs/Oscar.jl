### Constructors
function BinVec(pos::Int, exp::Vector{Int}, coeff)
  return BinVec(pos, _encode_binary_vector(exp, coeff))
end

function BinVec(v::FreeModElem{T}) where {T<:MPolyRingElem}
  res = BinVec()
  sizehint!(res.entries, length(coordinates(v)))
  for (i, c) in coordinates(v)
    push!(res.entries, (i, _encode_binary_vector(
        only(AbstractAlgebra.exponent_vectors(c)), 
        only(AbstractAlgebra.coefficients(c))))
      )
  end
  return res
end

function _encode_binary_vector(exp::Vector{Int}, coeff)
  mon = 0::Int
  if is_one(coeff) 
    mon += 1
  elseif !is_one(-coeff)
    error("coefficient must be 1 or -1")
  end
  @assert length(exp) <= 63 "rings with more than 63 variables are not supported"
  for (p, a) in enumerate(exp)
    is_zero(a) && continue
    @assert is_one(a) "monomial is not squarefree"
    mon += 1 << p
  end
  return mon
end

function BinVec(mon::MPolyRingElem)
  return BinVec(1, _encode_binary_vector(
                  only(AbstractAlgebra.exponent_vectors(mon)), 
                  only(AbstractAlgebra.coefficients(mon))
                 ))
end

function Base.show(io::IO, bv::BinVec)
  print(io, join([_binary_vector_to_str(mon)*"*e_$p" for (p, mon) in bv.entries], " + "))
end

function _binary_vector_to_str(mon::Int)
  res_str = (is_zero(mon%2) ? "-1" : "1") * "*[" 
  for k in 1:63
    1 << k > mon && break
    res_str = res_str * (is_zero((mon >> k)%2) ? "0" : "1")
  end
  return res_str * "]"
end

