export MPolyLocalizedIdeal
export gens, base_ring, saturated_ideal, intersect, quotient

########################################################################
# Ideals in localizations of multivariate polynomial rings             #
########################################################################
# 
# If 𝕜 is a Noetherian ring, any localization W = R[U⁻¹] of a multi-
# variate polynomial ring R = 𝕜[x₁,…,xₙ] is again Noetherian and 
# any ideal I ⊂ W is of the form I = I'⋅ W for some ideal I' ⊂ R. 
# This correspondence is not 1:1 but for any ideal I ⊂ W we always 
# have that 
#
#   J = { x∈ R | ∃ u ∈ U : u⋅x ∈ I }
#
# is the unique element which is maximal among all ideals I' in R for 
# which I = I'⋅W. We call this the `saturated ideal` I': U of the localization.
#
# Since computation of the saturated ideal might be expensive, 
# we usually only cache a 'pre-saturated ideal' I' ⊂ J ⊂ I': U.

@Markdown.doc """
    MPolyLocalizedIdeal{
        LocRingType<:MPolyLocalizedRing, 
        LocRingElemType<:MPolyLocalizedRingElem
      } <: AbsLocalizedIdeal{LocRingElemType}

Ideals in localizations of polynomial rings.
"""
@attributes mutable struct MPolyLocalizedIdeal{
    LocRingType<:MPolyLocalizedRing, 
    LocRingElemType<:MPolyLocalizedRingElem
  } <: AbsLocalizedIdeal{LocRingElemType}
  # the initial set of generators, not to be changed ever!
  gens::Vector{LocRingElemType}
  # the ambient ring for this ideal
  W::LocRingType

  # fields for caching 
  map_from_base_ring::Hecke.Map

  pre_saturated_ideal::MPolyIdeal
  pre_saturation_data::MatrixElem

  is_saturated::Bool
  saturated_ideal::MPolyIdeal
 
  function MPolyLocalizedIdeal(
      W::MPolyLocalizedRing, 
      gens::Vector{LocRingElemType};
      map_from_base_ring::Hecke.Map = MapFromFunc(
          x->W(x),
          y->(isone(denominator(y)) ? numerator(y) : divexact(numerator(y), denominator(y))),
          base_ring(W), 
          W
        )
    ) where {LocRingElemType<:AbsLocalizedRingElem}
    for f in gens
      parent(f) == W || error("generator is not an element of the given ring")
    end

    I = new{typeof(W), LocRingElemType}()
    I.gens = gens
    I.W = W
    I.map_from_base_ring = map_from_base_ring
    I.is_saturated=false
    return I
  end
end
 
### required getter functions
gens(I::MPolyLocalizedIdeal) = copy(I.gens)
base_ring(I::MPolyLocalizedIdeal) = I.W

### type getters
ideal_type(::Type{MPolyLocalizedRingType}) where {MPolyLocalizedRingType<:MPolyLocalizedRing} = MPolyLocalizedIdeal{MPolyLocalizedRingType, elem_type(MPolyLocalizedRingType)}
ideal_type(L::MPolyLocalizedRing) = ideal_type(typeof(L))

### additional getter functions 
map_from_base_ring(I::MPolyLocalizedIdeal) = I.map_from_base_ring
is_saturated(I::MPolyLocalizedIdeal) = I.is_saturated
ngens(I::MPolyLocalizedIdeal) = length(I.gens)
getindex(I::MPolyLocalizedIdeal, k::Int) = copy(I.gens[k])

function Base.in(a::RingElem, I::MPolyLocalizedIdeal)
  L = base_ring(I)
  parent(a) == L || return L(a) in I
  b = numerator(a)
  b in pre_saturated_ideal(I) && return true
  is_saturated(I) && return false
  R = base_ring(L)
  J = pre_saturated_ideal(I)
  (success, x, u) = has_solution(generator_matrix(J), MatrixSpace(R, 1, 1)([b]), inverted_set(L))
  !success && return false
  # cache the intermediate result
  extend_pre_saturated_ideal!(I, b, x, u, check=false)
  return true
end

function coordinates(a::RingElem, I::MPolyLocalizedIdeal; check::Bool=true)
  L = base_ring(I)
  parent(a) == L || return coordinates(L(a), I, check=check)
  if check 
    a in I || error("the given element is not in the ideal")
  end
  J = pre_saturated_ideal(I)
  R = base_ring(J)
  p = numerator(a)
  if p in J
    q = denominator(a)
    # caching has been done during the call of `in`, so the following will work
    x = coordinates(p, pre_saturated_ideal(I))
    return L(one(q), q, check=false)*change_base_ring(L, x)*pre_saturation_data(I)
  else
    (success, x, u) = has_solution(generator_matrix(J), MatrixSpace(R, 1, 1)([p]), inverted_set(L), check=false)
    !success && error("check for membership was disabled, but element is not in the ideal")
    # cache the intermediate result
    result = L(one(R), u*denominator(a), check=false)*change_base_ring(L, x)*pre_saturation_data(I)
    extend_pre_saturated_ideal!(I, p, x, u, check=false)
    return result
  end
end

generator_matrix(J::MPolyIdeal) = MatrixSpace(base_ring(J), ngens(J), 1)(gens(J))

@Markdown.doc """
    saturated_ideal(I::MPolyLocalizedIdeal)

Given an ideal `I` of a localization, say, `Rloc` of a multivariate polynomial ring, say, `R`,
return the largest ideal of `R` whose extension to `Rloc` is `I`. This is the preimage of `I`
under the localization map.

!!! note
    The function does not neccessarily return a minimal set of generators for the resulting ideal.
# Examples
```jldoctest
julia> R, (x,) = PolynomialRing(QQ, ["x"])
(Multivariate Polynomial Ring in x over Rational Field, fmpq_mpoly[x])

julia> U = powers_of_element(x)
powers of fmpq_mpoly[x]

julia> Rloc, iota = Localization(R, U);

julia> I = ideal(Rloc, [x+x^2])
ideal in localization of Multivariate Polynomial Ring in x over Rational Field at the powers of fmpq_mpoly[x] generated by the elements (x^2 + x)//1

julia> saturated_ideal(I)
ideal(x + 1)

julia> U = complement_of_ideal(R, [0])
complement of maximal ideal corresponding to point with coordinates fmpq[0]

julia> Rloc, iota = Localization(R, U);

julia> I = ideal(Rloc, [x+x^2])
ideal in localization of Multivariate Polynomial Ring in x over Rational Field at the complement of maximal ideal corresponding to point with coordinates fmpq[0] generated by the elements (x^2 + x)//1

julia> saturated_ideal(I)
ideal(x)
```
"""
function saturated_ideal(I::MPolyLocalizedIdeal)
  if !isdefined(I, :saturated_ideal)
    error("method `saturated_ideal` is not implemented for ideals of type $(typeof(I))")
  end
  return I.saturated_ideal
end

function pre_saturated_ideal(I::MPolyLocalizedIdeal)
  if !isdefined(I, :pre_saturated_ideal)
    W = base_ring(I)
    I.pre_saturated_ideal = ideal(base_ring(W), numerator.(gens(I)))
    r = length(gens(I))
    A = zero(MatrixSpace(W, r, r))
    for i in 1:r
      A[i, i] = denominator(gens(I)[i])
    end
    I.pre_saturation_data = A
  end
  return I.pre_saturated_ideal
end

function pre_saturation_data(I::MPolyLocalizedIdeal)
  if !isdefined(I, :pre_saturation_data)
    pre_saturated_ideal(I)
  end
  return I.pre_saturation_data
end

function extend_pre_saturated_ideal!(
    I::MPolyLocalizedIdeal, f::PT, x::MatrixElem{PT}, u::PT;
    check::Bool=true
  ) where {PT <: MPolyElem}
  nrows(x) == 1 || error("matrix must be a row vector")
  L = base_ring(I)
  R = base_ring(L)
  J = pre_saturated_ideal(I)
  if check
    u*f == dot(x, gens(J)) || error("input is not coherent")
  end
  J_ext = ideal(R, vcat(gens(J), [f]))
  T = pre_saturation_data(I)
  T_ext = vcat(T, L(one(u), u, check=false)*change_base_ring(L, x)*T)
  I.pre_saturated_ideal = J_ext
  I.pre_saturation_data = T_ext
  return I
end

function extend_pre_saturated_ideal!(
    I::MPolyLocalizedIdeal, f::Vector{PT}, x::MatrixElem{PT}, u::Vector{PT};
    check::Bool=true
  ) where {PT <: MPolyElem}
  L = base_ring(I)
  R = base_ring(L)
  J = pre_saturated_ideal(I)
  n = length(f)
  n == length(u) == nrows(x) || error("input dimensions are not compatible")
  if check
    for i in 1:n
      u[i]*f[i] == dot(x[i, :], gens(J)) || error("input is not coherent")
    end
  end
  J_ext = ideal(R, vcat(gens(J), f))
  T = pre_saturation_data(I)
  T_ext = vcat(T, 
               diagonal_matrix([L(one(v), v, check=false) for v in u])*
               change_base_ring(L, x)*T
              )
  I.pre_saturated_ideal = J_ext
  I.pre_saturation_data = T_ext
  return I
end

function coordinate_shift(
    L::MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}
  )
  if !has_attribute(L, :coordinate_shift)
    U = inverted_set(L)
    a = point_coordinates(U)
    R = base_ring(L)
    Ls = MPolyLocalizedRing(R, MPolyComplementOfKPointIdeal(R, [0 for i in 1:ngens(R)]))
    xs = [ x + a for (x, a) in zip(gens(base_ring(L)), a) ]
    xs_inv = [ x - a for (x, a) in zip(gens(base_ring(L)), a) ]
    shift = MapFromFunc(
                f -> Ls(evaluate(numerator(f), xs), evaluate(denominator(f), xs), check=false),
                g -> L(evaluate(numerator(g), xs_inv), evaluate(denominator(g), xs_inv), check=false),
                L, Ls
              )
    set_attribute!(L, :coordinate_shift, shift)
  end
  return get_attribute(L, :coordinate_shift)::Hecke.Map
end


function saturated_ideal(
    I::MPolyLocalizedIdeal{LRT};
    with_generator_transition::Bool=false
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}
  if !isdefined(I, :saturated_ideal)
    is_saturated(I) && return pre_saturated_ideal(I)
    J = pre_saturated_ideal(I)
    pdec = primary_decomposition(J)
    L = base_ring(I)
    R = base_ring(L)
    result = ideal(R, [one(R)])
    for (Q, P) in pdec
      if all(x->iszero(evaluate(x, point_coordinates(inverted_set(L)))), gens(P))
        result = intersect(result, Q)
      end
    end
    I.saturated_ideal = result
    if with_generator_transition
      error("computation of the transition matrix for the generators is not supposed to happen because of using local orderings")
      for g in gens(result) 
        g in I || error("generator not found") # assures caching with transitions
      end
    end
  end
  return I.saturated_ideal
end

function saturated_ideal(
    I::MPolyLocalizedIdeal{LRT};
    strategy::Symbol=:iterative_saturation,
    with_generator_transition::Bool=false
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyPowersOfElement}}
  if !isdefined(I, :saturated_ideal)
    is_saturated(I) && return pre_saturated_ideal
    L = base_ring(I)
    R = base_ring(L)
    if strategy==:iterative_saturation
      Jsat = pre_saturated_ideal(I)
      for d in denominators(inverted_set(L))
        if !is_unit(d) && !iszero(Jsat)
          Jsat = saturation(Jsat, ideal(R, d))
        end
        if with_generator_transition
          cache = Vector()
          for g in gens(Jsat)
            (k, dttk) = Oscar._minimal_power_such_that(d, p->(p*g in pre_saturated_ideal(I)))
            if k > 0
              push!(cache, (g, coordinates(dttk*g, pre_saturated_ideal(I)), dttk))
            end
          end
          if length(cache) > 0
            extend_pre_saturated_ideal!(I, 
                                        elem_type(R)[g for (g, x, u) in cache],
                                        vcat(dense_matrix_type(R)[x for (g, x, u) in cache]),
                                        [u for (g, x, u) in cache], 
                                        check=false
                                       )
          end
        end
      end
      I.saturated_ideal = Jsat
    elseif strategy==:single_saturation
      d = prod(denominators(inverted_set(L)))
      Jsat = pre_saturated_ideal(I)
      if !is_unit(d) && !iszero(pre_saturated_ideal(I))
        Jsat = saturation(Jsat, ideal(R, d))
      end
      if with_generator_transition
        cache = Vector()
        for g in gens(Jsat)
          (k, dttk) = Oscar._minimal_power_such_that(d, p->(p*g in pre_saturated_ideal(I)))
          if k > 0
            push!(cache, (g, coordinates(dttk*g, pre_saturated_ideal(I)), dttk))
          end
        end
        if length(cache) > 0
          extend_pre_saturated_ideal!(I, 
                                      elem_type(R)[g for (g, x, u) in cache],
                                      vcat(dense_matrix_type(R)[x for (g, x, u) in cache]),
                                      [u for (g, x, u) in cache], 
                                      check=false
                                     )
        end
      end
      I.saturated_ideal = Jsat
    else
      error("strategy $strategy not implemented")
    end
  end
  return I.saturated_ideal
end

function saturated_ideal(
    I::MPolyLocalizedIdeal{LRT};
    with_generator_transition::Bool=false
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyProductOfMultSets}}
  if !is_saturated(I)
    W = base_ring(I)
    R = base_ring(W)
    J = ideal(R, numerator.(gens(I)))
    for U in sets(inverted_set(W))
      L, _ = Localization(U)
      J = saturated_ideal(L(J))
    end
    if with_generator_transition
      for g in gens(J)
        g in I
      end
    end
    I.is_saturated = true
  end
  return pre_saturated_ideal(I)
end

function cache_transitions_for_saturation(I::MPolyLocalizedIdeal) 
  for g in saturated_ideal(I)
    g in I
  end
  return I
end


# the following overwrites the membership test 
# assuming that direct computation of the saturation 
# is cheaper when localizing at powers of elements.
function Base.in(
    a::RingElem, 
    I::MPolyLocalizedIdeal{LocRingType}
  ) where {
    LocRingType<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyPowersOfElement}
  }
  L = base_ring(I)
  parent(a) == L || return L(a) in I
  b = numerator(a)
  return b in saturated_ideal(I)
end


### Conversion of ideals in the original ring to localized ideals
function (W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST})(I::MPolyIdeal{RET}) where {BRT, BRET, RT, RET, MST}
  return MPolyLocalizedIdeal(W, W.(gens(I)))
end

### required constructors 
function ideal(
    W::MPolyLocalizedRing, f
  )
  return MPolyLocalizedIdeal(W, [W(f)])
end

@doc Markdown.doc"""    
    ideal(Rloc::MPolyLocalizedRing, V::Vector)

Given a localization `Rloc` of a multivariate polynomial ring, and given a vector `V` of 
elements of `Rloc`, create the ideal of `Rloc` which is generated by the entries of `V`.
"""
function ideal(
    W::MPolyLocalizedRing,
    gens::Vector
  )
  return MPolyLocalizedIdeal(W, W.(gens))
end

function ideal(
    W::MPolyLocalizedRing,
    I::Ideal
  )
  return MPolyLocalizedIdeal(W, W.(gens(I)))
end

### additional functionality
function issubset(I::IdealType, J::IdealType) where {IdealType<:MPolyLocalizedIdeal}
  base_ring(I) == base_ring(J) || error("ideals do not belong to the same ring")
  for g in gens(I)
    g in J || return false
  end
  return true
end

==(I::IdealType, J::IdealType) where {IdealType<:MPolyLocalizedIdeal} = (issubset(I, J) && issubset(J, I))

function +(I::IdealType, J::IdealType) where {IdealType<:MPolyLocalizedIdeal}
  return ideal(base_ring(I), vcat(gens(I), gens(J)))
end

# TODO: The following method can probably be fine tuned for specific localizations.
function intersect(I::IdealType, J::IdealType) where {IdealType<:MPolyLocalizedIdeal}
  return base_ring(I)(intersect(pre_saturated_ideal(I), pre_saturated_ideal(J)))
end

# TODO: The following method can probably be fine tuned for specific localizations.
function quotient(I::IdealType, J::IdealType) where {IdealType<:MPolyLocalizedIdeal}
  #return base_ring(I)(quotient(saturated_ideal(I), saturated_ideal(J)))
  return base_ring(I)(quotient(pre_saturated_ideal(I), pre_saturated_ideal(J)))
end


function Base.show(io::IO, I::MPolyLocalizedIdeal) 
  print(io, "ideal in $(base_ring(I)) generated by the elements ") 
  n = length(gens(I))
  for i in (1:n-1)
    print(io, "$(gens(I)[i]), ")
  end
  print(io, last(gens(I)))
end

@attr function shifted_ideal(
    I::MPolyLocalizedIdeal{LRT, LRET}
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}, LRET}
  L = base_ring(I)
  R = base_ring(L)
  shift, tfihs = base_ring_shifts(L)
  return ideal(R, shift.(gens(pre_saturated_ideal(I))))
end

function Base.in(
    a::RingElem, 
    I::MPolyLocalizedIdeal{LocRingType}
  ) where {
    LocRingType<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}
  }
  L = base_ring(I)
  parent(a) == L || return L(a) in I
  L = base_ring(I)
  R = base_ring(L)
  shift, tfihs = base_ring_shifts(L)
  Is = shifted_ideal(I)
  # We have to call for that groebner basis once manually. 
  # Otherwise the ideal membership will complain about the ordering not being global.
  o = negdegrevlex(gens(R))
  groebner_basis(Is, ordering=o, enforce_global_ordering=false)
  return ideal_membership(shift(numerator(a)), Is, ordering=o)
end

function coordinates(
    a::RingElem,
    I::MPolyLocalizedIdeal{LRT} 
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}
  L = base_ring(I)
  L == parent(a) || return coordinates(L(a), I)
  R = base_ring(L)
  J = shifted_ideal(I)
  shift, tfihs = base_ring_shifts(L)
  p = shift(numerator(a))
  o = negdegrevlex(gens(R))
  x, u = Oscar.lift(p, J, o)
  T = pre_saturation_data(I)
  return L(one(base_ring(L)), tfihs(u)*denominator(a), check=false)*change_base_ring(L, map_entries(tfihs,x))*T
end

########################################################################
# The next method is based on the following observation: 
#
#     p//q ∈ I ⋅ U⁻¹ ⋅ V⁻¹ ⊂ R[U⁻¹⋅V⁻¹] 
#   ⇔ ∃ u ∈ U, v∈ V : u ⋅ v ⋅ p ∈ I
#   ⇔ ∃ v ∈ V : v ⋅ p ∈ I : U 
#
# So, to compute the coordinates of p//q in I, we can proceed 
# inductively, by caching J = I : U and computing the coordinates 
# of p in J over R[V⁻¹]. 
#
# In particular for the case where U is the localization at a 
# hypersurface and V the localization at the complement of a prime 
# ideal, computing and working with the saturation in the first case 
# is quicker, while using local orderings/ the Posur method is favourable 
# in the second case. Since this situation will be of particular 
# interest, we provide a special path for that.
function coordinates(
    a::RingElem,
    I::MPolyLocalizedIdeal{LRT} 
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyProductOfMultSets}}
  L = base_ring(I)
  parent(a) == L || return coordinates(L(a), I)

  R = base_ring(L)
  U = sets(inverted_set(base_ring(I)))

  if length(U) == 1 
    if !has_attribute(I, :popped_ideal)
      W, _ = Localization(R, U[1])
      popped_ideal = W(pre_saturated_ideal(I))
      set_attribute!(I, :popped_ideal, popped_ideal)
    end
    popped_ideal = get_attribute(I, :popped_ideal)
    return L(one(R), denominator(a), check=false)*map_entries(x->L(x, check=false), coordinates(numerator(a), popped_ideal))*pre_saturation_data(I)
  end

  numerator(a) in pre_saturated_ideal(I) && return L(one(R), denominator(a), check=false)*map_entries(L, coordinates(numerator(a), pre_saturated_ideal(I)))*pre_saturation_data(I)

  i = findfirst(x->(typeof(x)<:MPolyPowersOfElement), U)
  if !isnothing(i)
    if !has_attribute(I, :popped_ideal)
      S = popat!(U, i)
      W, _ = Localization(base_ring(L), S)
      popped_ideal = ideal(W, pre_saturated_ideal(I))
      saturated_ideal(popped_ideal, with_generator_transition=true)
      set_attribute!(I, :popped_ideal, popped_ideal)
      Wnext, _ = Localization(R, MPolyProductOfMultSets(R, U))
      next_ideal = Wnext(pre_saturated_ideal(popped_ideal))
      set_attribute!(I, :next_ideal, next_ideal)
    end
    popped_ideal = get_attribute(I, :popped_ideal)
    next_ideal = get_attribute(I, :next_ideal)
    y = coordinates(numerator(a), next_ideal)
    x = map_entries(x->L(x, check=false), y)*map_entries(x->L(x, check=false), pre_saturation_data(popped_ideal))
    return L(one(R), denominator(a), check=false)*x
  else
    if !has_attribute(I, :popped_ideal)
      S = pop!(U)
      W, _ = Localization(base_ring(L), S)
      popped_ideal = ideal(W, pre_saturated_ideal(I))
      saturated_ideal(popped_ideal, with_generator_transition=true)
      set_attribute!(I, :popped_ideal, popped_ideal)
      Wnext, _ = Localization(R, MPolyProductOfMultSets(R, U))
      next_ideal = Wnext(pre_saturated_ideal(popped_ideal))
      set_attribute!(I, :next_ideal, next_ideal)
    end
    popped_ideal = get_attribute(I, :popped_ideal)
    next_ideal = get_attribute(I, :next_ideal)
    y = coordinates(numerator(a), next_ideal)
    x = map_entries(x->L(x, check=false), y)*map_entries(x->L(x, check=false), pre_saturation_data(popped_ideal))
    return L(one(R), denominator(a), check=false)*x
  end
end

function Base.in(
    a::RingElem,
    I::MPolyLocalizedIdeal{LRT} 
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyProductOfMultSets}}
  L = base_ring(I)
  parent(a) == L || return L(a) in I

  R = base_ring(L)
  U = sets(inverted_set(base_ring(I)))

  if length(U) == 1 
    if !has_attribute(I, :popped_ideal)
      W, _ = Localization(R, U[1])
      popped_ideal = W(pre_saturated_ideal(I))
      set_attribute!(I, :popped_ideal, popped_ideal)
    end
    popped_ideal = get_attribute(I, :popped_ideal)
    return numerator(a) in popped_ideal
  end

  numerator(a) in pre_saturated_ideal(I) && return true

  i = findfirst(x->(typeof(x)<:MPolyPowersOfElement), U)
  if !isnothing(i)
    if !has_attribute(I, :popped_ideal)
      S = popat!(U, i)
      W, _ = Localization(base_ring(L), S)
      popped_ideal = ideal(W, pre_saturated_ideal(I))
      saturated_ideal(popped_ideal, with_generator_transition=true)
      set_attribute!(I, :popped_ideal, popped_ideal)
      Wnext, _ = Localization(R, MPolyProductOfMultSets(R, U))
      next_ideal = Wnext(pre_saturated_ideal(popped_ideal))
      set_attribute!(I, :next_ideal, next_ideal)
    end
    next_ideal = get_attribute(I, :next_ideal)
    return numerator(a) in next_ideal
  else
    if !has_attribute(I, :popped_ideal)
      S = pop!(U)
      W, _ = Localization(base_ring(L), S)
      popped_ideal = ideal(W, pre_saturated_ideal(I))
      saturated_ideal(popped_ideal, with_generator_transition=true)
      set_attribute!(I, :popped_ideal, popped_ideal)
      Wnext, _ = Localization(R, MPolyProductOfMultSets(R, U))
      next_ideal = Wnext(pre_saturated_ideal(popped_ideal))
      set_attribute!(I, :next_ideal, next_ideal)
    end
    next_ideal = get_attribute(I, :next_ideal)
    return numerator(a) in next_ideal
  end
end


########################################################################
# special treatment of localization at orderings                       #
########################################################################

function Base.in(
    a::RingElem,
    I::MPolyLocalizedIdeal{LRT} 
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyLeadingMonOne}}
  parent(a) == base_ring(I) || return base_ring(I)(a) in I
  J = pre_saturated_ideal(I)
  p = numerator(a)
  o = ordering(inverted_set(parent(a)))
  # We have to call for that groebner basis once manually. 
  # Otherwise the ideal membership will complain about the ordering not being global.
  groebner_basis(J, ordering=o, enforce_global_ordering=false)
  return ideal_membership(p, J, ordering=o)
end

function coordinates(
    a::RingElem,
    I::MPolyLocalizedIdeal{LRT} 
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyLeadingMonOne}}
  L = base_ring(I)
  L == parent(a) || return coordinates(L(a), I)
  J = pre_saturated_ideal(I)
  p = numerator(a)
  o = ordering(inverted_set(parent(a)))
  x, u = Oscar.lift(p, J, o)
  T = pre_saturation_data(I)
  return L(one(base_ring(L)), u*denominator(a), check=false)*change_base_ring(L, x)*T
end

@attr function hilbert_series(
    I::MPolyLocalizedIdeal{LRT}
  ) where {LRT<:MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}
  L = base_ring(I)
  J = shifted_ideal(I)
  R = base_ring(L)
  o = negdegrevlex(gens(R))
  LJ = leading_ideal(J, ordering=o, enforce_global_ordering=false)
  RG, _ = grade(R, [1 for i in 1:ngens(R)])
  LJG = ideal(RG, RG.(gens(LJ)))
  Q, _ = quo(RG, LJG)
  hilbert_series(Q)
end

