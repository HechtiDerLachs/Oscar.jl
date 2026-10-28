### Constructors
function BinVec(pos::UInt, exp::Vector{UInt}, coeff)
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
  mon = UInt(0)
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
  return BinVec(UInt(1), _encode_binary_vector(
                  only(AbstractAlgebra.exponent_vectors(mon)), 
                  only(AbstractAlgebra.coefficients(mon))
                 ))
end

function Base.show(io::IO, bv::BinVec)
  print(io, join([_binary_vector_to_str(mon)*"*e_$p" for (p, mon) in bv.entries], " + "))
end

function _binary_vector_to_str(mon::UInt)
  res_str = (is_zero(mon%2) ? "-1" : "1") * "*[" 
  for k in 1:63
    1 << k > mon && break
    res_str = res_str * (is_zero((mon >> k)%2) ? "0" : "1")
  end
  return res_str * "]"
end

### arithmetic
function deepcopy_internal(a::BinVec, d::IdDict)
  res = BinVec()
  res.entries = deepcopy_internal(a.entries, d)
  return res
end

function +(a::BinVec, b::BinVec)
  return addmul!(deepcopy(a), b, 1)
end

function -(a::BinVec, b::BinVec)
  return addmul!(deepcopy(a), b, -1)
end

length(a::BinVec) = length(a.entries)

function addmul!(a::BinVec, b::BinVec, c)
  result = BinVec()
  sizehint!(result.entries, length(a)+length(b))
  i = 1
  j = 1
  while !(i>length(a) || j>length(b))
    p, mi = a.entries[i]
    q, mj = b.entries[j]
    if p < q
      push!(result.entries, (p, mi))
      i += 1
      continue
    elseif q < p
      if is_one(-c)
        mj = mj + (is_zero(mj%2) ? 1 : -1)
      end
      push!(result.entries, (q, mj))
      j += 1
      continue
    end
    # p == q
    if is_one(c)
      @assert (is_zero(mi%2) && is_one(mj%2)) || (is_one(mi%2) && is_zero(mj%2)) "addition not supported"
    elseif is_one(-c)
      @assert (is_zero(mi%2) && is_zero(mj%2)) || (is_one(mi%2) && is_one(mj%2)) "addition not supported"
    else
      error("scalar multiplication with scalars different from 1 and -1 not supported")
    end
    # in all cases the terms cancel out and we can skip this entry
    i += 1
    j += 1
  end
  while i <= length(a)
    push!(result.entries, a.entries[i])
    i += 1
  end
  while j <= length(b)
    q, mj = b.entries[j]
    if is_one(-c)
      mj = mj + (is_zero(mj%2) ? 1 : -1)
    end
    push!(result.entries, (q, mj))
    j += 1
  end

  return result
end

function mul!(e, a::BinVec)
  return mul!(UInt(e), a)
end

function mul!(e::UInt, a::BinVec)
  for (k, (p, mon)) in enumerate(a.entries)
    @assert is_zero((mon & e) >> 1) "result of multiplication would have a square"
    a.entries[k] = (p, ((xor(mon, e) >> 1) << 1) + (mon%2 + e%2)%2)
  end
  return a
end

function *(e, a::BinVec)
  return UInt(e)*a
end

function *(e::UInt, a::BinVec)
  return mul!(e::UInt, deepcopy(a))
end

function -(a::BinVec)
  return 1*a
end

lead(a::BinVec) = first(a.entries)
is_zero(a::BinVec) = is_empty(a.entries)

_binary_vector_lcm(a::UInt, b::UInt) = ((a >> 1) | (b >> 1)) << 1 + 1

function _binary_vector_divides(a::UInt, b::UInt)
  # a: 1100
  # b: 1010
  #    0010
end
