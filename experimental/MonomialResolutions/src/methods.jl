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

# Turn an exponent vector `exp` and a sign `coeff` into 
# a single `UInt` to be used in `BinVec`s. 
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

# Constructor from squarefree monomials
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
  @assert is_one(c) || is_one(-c) "scalar multiplication by elements different from ±1 is not allowed"
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
      push!(result.entries, (q, xor(mj, c == -1))) # xor does the change of signs 
      j += 1
      continue
    end
    # p == q
    mj_signed = xor(mj, c == -1)
    tst = xor(mi, mj_signed)
    @assert tst < 2 "more than one monomial is not allowed per component"
    if tst == 1 # different signs of the monomials, hence cancellation
      i += 1
      j += 1
      continue
    end
    # both monomials have the same signs, hence we get 2*m = -m over 𝔽₃
    push!(result.entries, (q, xor(mi, 1)))
    i += 1
    j += 1
  end
  while i <= length(a)
    push!(result.entries, a.entries[i])
    i += 1
  end
  while j <= length(b)
    q, mj = b.entries[j]
    push!(result.entries, (q, xor(mj, c == -1)))
    j += 1
  end

  return result
end

function addmul!(a::BinVec, b::BinVec, c::UInt)
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
      @assert (mj & c < 2) "multiplication leads to exponents > 1"
      push!(result.entries, (q, (mj >> 1 | c >> 1) << 1 + (mj%2 + c%2)%2))
      j += 1
      continue
    end
    # p == q
    @assert (mj & c < 2) "multiplication leads to exponents > 1"
    nj = (mj >> 1 | c >> 1) << 1 + (mj%2 + c%2)%2
    @assert xor(mi, nj) == 1 "terms do not cancel"
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
    @assert (mj & c < 2) "multiplication leads to exponents > 1"
    nj = (mj >> 1 | c >> 1) << 1 + (mj%2 + c%2)%2
    push!(result.entries, (q, nj))
    j += 1
  end

  return result
end

function Base.:(==)(a::BinVec, b::BinVec)
  return a.entries == b.entries
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
  # c: 0010
  (~a & b > 1) && return false, b
  return true, xor(a, b)
end

function _binary_vector_div(a::UInt, b::UInt)
  @assert (~a & b < 2) "division error"
  return xor(a, b)
end

function groebner_basis!(gens::Vector{BinVec})
  pairs_todo = [(i, j) for i in 1:length(gens)-1 for j in i+1:length(gens)]
  counter = 0
  zero_reductions = 0
  while !isempty(pairs_todo)
    counter += 1
    i, j = pop!(pairs_todo)
    u = gens[i]
    v = gens[j]
    p, m1 = lead(u)
    q, m2 = lead(v)
    p != q && continue # no cancellation possible
    l = _binary_vector_lcm(m1, m2)
    n1 = _binary_vector_div(l, m1)
    n2 = _binary_vector_div(l, m2)
    if is_zero(n2%2)
      n2 += 1
    else
      n2 -= 1
    end
    g = n1*u
    g = addmul!(g, v, n2)
    g = reduce!(g, gens)
    if is_zero(g) 
      zero_reductions += 1
      continue
    end
    n = length(gens)
    qq, _ = lead(g)
    append!(pairs_todo, [(i, n+1) for (i, g) in enumerate(gens) if lead(g)[1] == qq])
    push!(gens, g)
  end
  @show counter, zero_reductions
  return gens
end

function reduce!(a::BinVec, gens::Vector{BinVec})
  is_zero(a) && return a
  for b in gens
    a = reduce!(a, b)
    is_zero(a) && return a
  end
  return a
end

function reduce!(a::BinVec, b::BinVec)
  p, mon = lead(b)
  down = 1
  up = length(a)
  q, _ = last(a.entries)
  q < p && return a
  if p == q
    down = up
  end
  q, _ = first(a.entries)
  q > p && return a
  if p == q 
    up = down
  end
  while up != down
    middle = down + div(up - down, 2) + 1
    q, _ = a.entries[middle]
    if q == p
      up = down = middle
    elseif q < p
      down = middle
    else # q > p
      up = middle - 1
    end
  end
  q, e = a.entries[up]
  q != p && return a
  success, fac = _binary_vector_divides(e, mon)
  !success && return a
  if is_zero(fac%2)
    fac += 1
  else
    fac -= 1
  end
  a = addmul!(a, b, fac)
  return a
end

function interreduce!(gens::Vector{BinVec})
  result = sizehint!(Vector{BinVec}(), size(gens))
  for (k, v) in enumerate(gens)
    for g in result
      reduce!(g, v)
    end
    v = reduce!(v, result)
    is_zero(v) && continue
    push!(result, v)
  end
  return filter!(!is_zero, result)
end

function _syzygies(gens::Vector{BinVec})
  result = BinVec[]
  for (i, v) in enumerate(gens)
    p, m = lead(v)
    for j in i+1:length(gens)
      w = gens[j]
      q, n = lead(w)
      q > p && break
      # compute the s-polynomial and initialize the syzygy
      l = _binary_vector_lcm(m, n)
      s = _binary_vector_div(l, m)
      t = _binary_vector_div(l, n)
      rem = s*v
      if is_zero(t%2)
        t += 1
      else
        t -= 1
      end
      rem = addmul!(rem, w, t)
      new_syz = BinVec([(UInt(i), s), (UInt(j), t)])
      # tail reduction
      for k in j+1:length(gens)
        is_zero(rem) && break
        pp, mm = lead(rem)
        w = gens[k]
        q, n = lead(w)
        q != pp && continue # nothing to cancel here
        success, c = _binary_vector_divides(mm, n)
        !success && continue
        if is_zero(c%2)
          c += 1
        else
          c -= 1
        end
        rem = addmul!(rem, w, c)
        push!(new_syz.entries, (UInt(k), c))
      end
      @assert is_zero(rem) "remainder is not zero"
#     cc = BinVec()
#     for (p, c) in new_syz.entries
#       cc = addmul!(cc, gens[p], c)
#     end
#     @assert is_zero(cc)
      push!(result, new_syz)
    end
  end
  return result
end

function (F::FreeMod)(a::BinVec)
  R = base_ring(F)
  return F(sparse_row(R, [(Int(i), (-1)^(e%2)*prod(x^((e >> k)%2) for (k, x) in enumerate(gens(R)); init=one(R))) for (i, e) in a.entries]))
end

