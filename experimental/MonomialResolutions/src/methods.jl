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

function copy(a::BinVec)
  result = BinVec()
  result.entries = copy(a.entries)
  return result
end

function +(a::BinVec, b::BinVec)
  return addmul!(copy(a), b, 1)
end

function -(a::BinVec, b::BinVec)
  return addmul!(copy(a), b, -1)
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

function hash(a::BinVec, u::UInt)
  return hash(a.entries, u)
end

function mul!(e, a::BinVec)
  return mul!(UInt(e), a)
end

function mul!(e::UInt, a::BinVec)
  for (k, (p, mon)) in enumerate(a.entries)
    @assert is_zero((mon & e) >> 1) "result of multiplication would have a square"
    a.entries[k] = (p, (xor(mon, e) & ~UInt(1)) + (mon%2 + e%2)%2)
  end
  return a
end

function *(e, a::BinVec)
  return UInt(e)*a
end

function *(e::UInt, a::BinVec)
  return mul!(e::UInt, copy(a))
end

function -(a::BinVec)
  return 1*a
end

lead(a::BinVec) = first(a.entries)
is_zero(a::BinVec) = is_empty(a.entries)

_binary_vector_lcm(a::UInt, b::UInt) = (a | b) & ~UInt(1) #((a >> 1) | (b >> 1)) << 1 

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
  #@show counter, nonzero_reductions
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
    #result = filter!(!is_zero, result)
    v = reduce!(v, result)
    is_zero(v) && continue
    push!(result, v)
  end
  return filter!(!is_zero, result)
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
# for s in result
#   tst = BinVec()
#   for (p, a) in s.entries
#     tst = addmul!(tst, gens[p], a)
#   end
#   @assert is_zero(tst)
# end
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
  #return F(sparse_row(R, [(Int(i), (-1)^(e%2)*prod(x^((e >> k)%2) for (k, x) in enumerate(gens(R)); init=one(R))) for (i, e) in a.entries]))
  kk = coefficient_ring(R)
  n = ngens(R)
  entries = sizehint!(Tuple{Int, elem_type(R)}[], length(a.entries))
  for (i, e) in a.entries
    d = [0 for _ in 1:n]
    for (k, c) in enumerate(digits(e >> 1; base=2))
      d[k] = c
    end
    #d = digits(e >> 1; base=2)
    #append!(d, [0 for _ in (length(d)+1):n])
    push!(entries, (i, R([is_zero(e%2) ? one(kk) : -one(kk)], [d])))
  end
  return F(sparse_row(R, entries))
end

function _lt(a::BinVec, b::BinVec)
  p, e = lead(a)
  q, f = lead(b)
  p < q && return false
  p > q && return true
  return e < f
end

function resolution!(g::Vector{BinVec}; 
    is_minimal::Bool=false, is_sorted::Bool=false, 
    upper_bound::Union{AbstractAlgebra.PosInf, Int}=AbstractAlgebra.PosInf()
  )
  if !is_minimal
    g = interreduce!(g)
  end
  if !is_sorted
    g = sort!(g; lt=_lt)
  end
  result = Vector{BinVec}[g]
  #@show length(g)
  while !isempty(last(result)) && length(result) <= upper_bound
    @show length(result)
    vd = last(result)
    @show length(vd)
    lookup = Dict{Int, Int}()
    q = 0
    for (k, v) in enumerate(vd)
      p, _ = lead(v)
      p == q && continue
      @assert p > q
      #haskey(lookup, p) && continue
      lookup[p] = k
      q = p
    end
    #vvd = interreduce!(groebner_basis!(deepcopy(vd)))
    #alt_syz = interreduce!(_syzygies(vd))
    #@show length(vvd)
    #@show length(alt_syz)
    next = BinVec[]
    #@show length(vd)
    p = UInt(0)
    init = 0
    while init < length(vd)
      p, e = lead(vd[init+1])
      #@show init, p
      leads = [e]
      lleads = [BinVec([(p, e)])]
      for i in (init+2):length(vd)
        q, e = lead(vd[i])
        q > p && break
        push!(leads, e)
        push!(lleads, BinVec([(q, e)]))
      end
      #@show length(leads)
      min_pairs = minimal_pairs(lleads)
      #min_pairs = minimal_pairs(leads)
      #@assert length(min_pairs) == length(alt_min_pairs)
#     if length(min_pairs) != length(alt_min_pairs)
#       for (i, b) in enumerate(vd)
#         @show i, b
#       end
#       for p in min_pairs
#         @show p
#       end
#       for q in alt_min_pairs
#         @show q
#       end
#       more = [p for p in alt_min_pairs if !(p in min_pairs)]
#       for r in more
#         @show r
#       end
#       error()
#     end
      #@show length(min_pairs)
      for (i, j, ee) in min_pairs
        #@show i, j, ee
        a = vd[init+i]
        b = vd[init+j]
        #@show a
        #@show b
        pp, e = lead(a)
        qq, f = lead(b)
        @assert pp == qq
        #@show e, f, ee
        # form the s-polynomial
        s = _binary_vector_div(ee, e)
        t = _binary_vector_div(ee, f)
        t = xor(t, 1) # put a negative sign on t
        rem = addmul!(s*a, b, t)
        @assert is_zero(rem) || first(lead(rem)) > pp
        new_syz = BinVec([(UInt(i+init), s), (UInt(j+init), t)])
        sizehint!(new_syz.entries, length(rem))
        # tail reduction
        #for k in (init+length(leads)+1):length(vd)
        old_lead = (UInt(0), UInt(0))
        while !is_zero(rem)
          pp, mm = lead(rem)
          (pp, mm) == old_lead && error("no cancellation happened")
          ind = lookup[pp]
          isnothing(ind) && error("non-trivial term in remainder, but nothing to cancel it")
          for k in ind:length(vd)
            w = vd[k]
            q, nn = lead(w)
            q > pp && break # nothing to cancel here
            success, c = _binary_vector_divides(mm, nn)
            !success && continue
            #@show k, w, c
            c = xor(c, 1) # change sign of c
            rem = addmul!(rem, w, c)
            push!(new_syz.entries, (UInt(k), c))
            break
          end
          old_lead = (pp, mm)
        end
        if !is_zero(rem)
          @show Int(qq)
          @show a
          @show b
          @show ee
          @show new_syz
          @show rem
        end
        @assert is_zero(rem) "remainder is not zero"
        push!(next, new_syz)
      end
      init += length(leads)
    end
#   @show length(next)
#   @show length(alt_syz)
#   for a in next
#     @show a
#   end
#   for b in alt_syz
#     @show b
#   end
#   @show all(a in alt_syz for a in next)
#   @show all(a in next for a in alt_syz)
#   for c in setdiff(alt_syz, next)
#     @show c
#   end
    push!(result, next) #interreduce!(groebner_basis!(next)))
    #return next
    #push!(result, Vector{BinVec}[])
  end
  return result
end

function minimal_pairs(v::Vector{BinVec})
  s = interreduce!(_syzygies(v))
  result = sizehint!(Tuple{Int, Int, UInt}[], div(length(v)^2, 2))
  for ss in s
    @assert length(ss.entries) == 2
    (i, a), (j, b) = ss.entries
    _, e = lead(v[i])
    _, f = lead(v[j])
    ee = _binary_vector_lcm(e, f)
    success, q = _binary_vector_divides(ee, a)
    @assert success && q == e
    success, q = _binary_vector_divides(ee, b)
    @assert success && xor(q, f) < 2
    push!(result, (i, j, ee))
  end
  return result
end

function minimal_pairs(g::Vector{UInt})
  n = length(g)
  lcms = Union{UInt, Nothing}[a | b for (i, a) in enumerate(g), (j, b) in enumerate(g)]
  # we apply the chain criterion: If (i, j) produces an lcm which is divisible by k, 
  # then (i, k) and (j, k) can be used instead of (i, j)
  for i in 1:(n-1)
    for j in (i+1):n
      e = lcms[i, j]::UInt
      #for (k, f) in enumerate(g)
      for k in (i+1):(j-1)
        f = g[k]
        if first(_binary_vector_divides(e, f))
          lcms[i, j] = nothing
          break
        end
      end
    end
  end
#     cancel = false
#     for s in 1:(i-1)
#       for t in (s+1):n
#         f = lcms[s, t]
#         isnothing(f) && continue
#         if first(_binary_vector_divides(f, e))
#           lcms[i, j] = nothing
#           cancel = true
#           break
#         elseif first(_binary_vector_divides(e, f))
#           lcms[s, t] = nothing
#         end
#       end
#       cancel && break
#     end
#   end
# end
  result = Tuple{Int, Int, UInt}[]
  for i in 1:(n-1)
    append!(result, [(i, j+i, e) for (j, e) in enumerate(lcms[i, (i+1):end]) if !isnothing(e)])
  end
  return result
end

function _to_resolution(phis::Vector{Vector{BinVec}}, R::MPolyRing)
  F = FreeMod(R, 1)
  maps = FreeModuleHom[]
  for phi in phis
    m = length(phi)
    G = FreeMod(R, m)
    push!(maps, hom(G, F, F.(phi)))
    F = G
  end
  return SimpleComplexWrapper(ComplexOfMorphisms(reverse(maps); check=false))
end

