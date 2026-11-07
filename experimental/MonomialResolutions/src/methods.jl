### Constructors
function BinVec(pos::UInt, exp::Vector{UInt}, coeff)
  is_zero(coeff) && return BinVec()
  return BinVec(pos, (exp << 1) | UInt(!is_one(coeff)))
end

function BinVec(exp::UInt, coeff=1)
  is_zero(coeff) && return BinVec()
  return BinVec(UInt(1), (exp << 1) | UInt(!is_one(coeff)))
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
  res_str = (is_zero(mon%2) ? "" : "-1*") * "[" 
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
      mj_c = mj | c # the product up to the first bit
      mj_c -= mj_c%2 # delete the first bit
      mj_c += (mj%2 + c%2)%2
      push!(result.entries, (q, mj_c))
      j += 1
      continue
    end
    # p == q
    @assert (mj & c < 2) "multiplication leads to exponents > 1"
    mj_c = mj | c # the product up to the first bit
    mj_c -= mj_c%2 # delete the first bit
    mj_c += (mj%2 + c%2)%2
    tst = xor(mi, mj_c)
    @assert tst < 2 "more than two monomials in one position are not supported"
    if tst == 1 # the case of cancellation
      i += 1
      j += 1
      continue
    end
    # no cancellation, hence arithmetic in 𝔽₃
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
    mj_c = mj | c # the product up to the first bit
    mj_c -= mj_c%2 # delete the first bit
    mj_c += (mj%2 + c%2)%2
    push!(result.entries, (q, mj_c))
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
  gens = interreduce!(gens)
  pairs_todo = [(i, j) for i in 1:length(gens)-1 for j in i+1:length(gens)]
  counter = 0
  nonzero_reductions = 0
  while !isempty(pairs_todo)
    counter += 1
    i, j = pop!(pairs_todo)
    u = gens[i]
    v = gens[j]
    isone(length(u)) && isone(length(v)) && continue # no tails to produce something new
    p, m1 = lead(u)
    q, m2 = lead(v)
    p != q && continue # no cancellation possible
    l = _binary_vector_lcm(m1, m2)
    n1 = _binary_vector_div(l, m1)
    n2 = _binary_vector_div(l, m2)
    g = n1*u
    g = addmul!(g, v, xor(n2, UInt(1)))
    g = reduce!(g, gens)
    is_zero(g) && continue
    n = length(gens)
    qq, _ = lead(g)
    nonzero_reductions += 1
    append!(pairs_todo, [(i, n+1) for (i, g) in enumerate(gens) if lead(g)[1] == qq])
    push!(gens, g)
  end
  @show counter, nonzero_reductions
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
  is_zero(b) && return a
  is_zero(a) && return a
  p, mon = lead(b)
  # find the index in `a` which has `p`
  down = 1
  up = length(a)
  q, _ = last(a.entries)
  q < p && return a # p is out of bounds for `a`, no cancellation possible
  if p == q # we hit the spot directly
    down = up
  end
  q, _ = first(a.entries)
  q > p && return a # again: out of bounds
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
  q != p && return a # no overlap and hence no cancellation
  success, fac = _binary_vector_divides(e, mon)
  !success && return a
  a = addmul!(a, b, xor(fac, UInt(1)))
  return a
end

function interreduce!(gens::Vector{BinVec})
  #inds = interreduce!(gens, 1, length(gens))
  #return gens[inds]
  result = sizehint!(Vector{BinVec}(), size(gens))
  for (k, v) in enumerate(gens)
    for (ind, g) in enumerate(result)
      result[ind] = reduce!(g, v)
    end
    result = filter!(!is_zero, result)
    v = reduce!(v, result)
    is_zero(v) && continue
    push!(result, v)
  end
  return result
end

function interreduce!(gens::Vector{BinVec}, lower::Int, upper::Int)
  upper == lower && return is_zero(gens[upper]) ? Int[] : [upper]
  mid = div(upper + lower, 2)
  a = interreduce!(gens, lower, mid)
  b = interreduce!(gens, mid+1, upper)
  result = sizehint!(Int[], length(a) + length(b))
  a_sub = sizehint!(Int[], length(a))
  #ga = gens[a]
  #gb = gens[b]
  for i in a
    f = gens[i]
    for j in b
      f = reduce!(f, gens[j])
      is_zero(f) && break
    end
    #f = reduce!(gens[i], gb)
    is_zero(f) && continue
    gens[i] = f
    push!(result, i)
    push!(a_sub, i)
  end
  for j in b
    f = gens[j]
    for i in a_sub # we need to compare only against non-zero elements 
      f = reduce!(f, gens[i])
      is_zero(f) && break
    end
    #f = reduce!(gens[j], ga)
    is_zero(f) && continue
    gens[j] = f
    push!(result, j)
  end
  return result
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
      t = xor(t, 1) # xor takes care of sign change
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
        c = xor(c, 1) # change sign of c
        !success && continue
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
# for (i, e) in a.entries
#   @show i, e
#   @show Int(i)
#   @show (-1)^(e%2)
#   @show prod(x^((e >> k)%2) for (k, x) in enumerate(gens(R)); init=one(R)) 
#   for (k, x) in enumerate(gens(R))
#     @show k, x
#     @show e >> k
#     @show e >> k %2
#     @show x^((e >> k)%2)
#   end
# end
  return F(sparse_row(R, [(Int(i), (-1)^(e%2)*prod(x^((e >> k)%2) for (k, x) in enumerate(gens(R)); init=one(R))) for (i, e) in a.entries]))
end

