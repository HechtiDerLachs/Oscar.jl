export MPolyComplementOfPrimeIdeal, MPolyComplementOfKPointIdeal, MPolyPowersOfElement, MPolyProductOfMultSets
export rand, sets, issubset, units_of

export MPolyLocalizedRing
export ambient_ring, point_coordinates, inverted_set, denominators, gens

export MPolyLocalizedRingElem
export numerator, denominator, fraction, parent, isunit, divexact
export reduce_fraction

export MPolyLocalizedIdeal
export gens, base_ring, groebner_bases, default_ordering, dim, saturated_ideal, intersection, quotient

export Localization, ideal

export LocalizedBiPolyArray, BiPolyArray
export oscar_gens, oscar_ring, singular_ring, singular_gens, ordering, shift
export groebner_basis, groebner_assure

export MPolyLocalizedRingHom
export domain, codomain, images

import AbstractAlgebra: Ring, RingElem
import Base: issubset

########################################################################
# General framework for localizations of multivariate polynomial rings #
########################################################################

########################################################################
# Multiplicatively closed sets in multivariate polynomial rings        #
########################################################################

abstract type AbsMPolyMultSet{BRT, BRET, RT, RET} <: AbsMultSet{RT, RET} end

########################################################################
# Powers of elements                                                   #
########################################################################

@Markdown.doc """
MPolyPowersOfElement{
    BaseRingType,
    BaseRingElemType, 
    RingType,
    RingElemType
  } <: AbsMPolyMultSet{
    BaseRingType,
    BaseRingElemType, 
    RingType, 
    RingElemType
  }

The set `S = { aᵏ : k ∈ ℕ₀ }` for some ``a ∈ R`` with ``R`` of type `BaseRingType`.
"""
mutable struct MPolyPowersOfElement{
    BaseRingType,
    BaseRingElemType, 
    RingType,
    RingElemType
  } <: AbsMPolyMultSet{
    BaseRingType,
    BaseRingElemType, 
    RingType, 
    RingElemType
  }

  R::RingType # the parent ring
  a::Vector{RingElemType} # the list of elements whose powers belong to this set

  function MPolyPowersOfElement(R::RingType, a::Vector{RingElemType}) where {RingType<:MPolyRing, RingElemType<:MPolyElem}
    for f in a 
      parent(f) == R || error("element does not belong to the given ring")
      !iszero(f) || error("can not localize at the zero element")
    end
    k = coefficient_ring(R)
    return new{typeof(k), elem_type(k), RingType, RingElemType}(R, a)
  end
end

### required getter functions
ambient_ring(S::MPolyPowersOfElement) = S.R

### additional constructors
MPolyPowersOfElement(f::RET) where {RET<:MPolyElem} = MPolyPowersOfElement(parent(f), [f])
units_of(R::RT) where {RT<:MPolyRing} = MPolyPowersOfElement(R, [one(R)])

### additional functionality
denominators(S::MPolyPowersOfElement) = copy(S.a)

### required functionality
function Base.in(
    f::RingElemType, 
    S::MPolyPowersOfElement{BaseRingType, BaseRingElemType, RingType, RingElemType}
  ) where {BaseRingType, BaseRingElemType, RingType, RingElemType}
  R = parent(f)
  R == ambient_ring(S) || return false
  if iszero(f) 
    return false
  end
  d = (length(denominators(S)) == 0 ? one(R) : prod(denominators(S)))
  # We need to check whether for some a ∈ R and k ∈ ℕ we have 
  #   a⋅f = dᵏ.
  (i, o) = ppio(f, d)
  return divides(one(R), o)[1]
end

### printing
function Base.show(io::IO, S::MPolyPowersOfElement)
  print(io, "powers of ")
  print(io, denominators(S))
end

### generation of random elements 
function rand(S::MPolyPowersOfElement, v1::UnitRange{Int}, v2::UnitRange{Int}, v3::UnitRange{Int})
  return prod([f^(abs(rand(Int))%10) for f in denominators(S)])::elem_type(ambient_ring(S))
end


########################################################################
# Complements of prime ideals                                          #
########################################################################

@Markdown.doc """
MPolyComplementOfPrimeIdeal{
    BaseRingType, 
    BaseRingElemType,
    RingType,
    RingElemType
  } <: AbsMPolyMultSet{
    BaseRingType, 
    BaseRingElemType,
    RingType,
    RingElemType
  }

The complement of a prime ideal `P ⊂ 𝕜[x₁,…,xₙ]` in a multivariate polynomial ring 
with elements of type `RingElemType` over a base ring `𝕜` of type `BaseRingType`.
"""
mutable struct MPolyComplementOfPrimeIdeal{
    BaseRingType, 
    BaseRingElemType,
    RingType,
    RingElemType
  } <: AbsMPolyMultSet{
    BaseRingType, 
    BaseRingElemType,
    RingType,
    RingElemType
  }

  # The parent polynomial ring 𝕜[x₁,…,xₙ]
  R::RingType
  # The prime ideal whose complement this is
  P::MPolyIdeal{RingElemType}

  function MPolyComplementOfPrimeIdeal(
      P::MPolyIdeal{RingElemType}; 
      check::Bool=false
    ) where {RingElemType}
    R = base_ring(P)
    check && (isprime(P) || error("the ideal $P is not prime"))
    return new{typeof(coefficient_ring(R)), elem_type(coefficient_ring(R)), typeof(R), elem_type(R)}(R, P)
  end
end

### required getter functions
ambient_ring(
    S::MPolyComplementOfPrimeIdeal) = S.R

### required functionality
function Base.in(
    f::RingElemType, 
    S::MPolyComplementOfPrimeIdeal{BaseRingType, BaseRingElemType, RingType, RingElemType}
  ) where {BaseRingType, BaseRingElemType, RingType, RingElemType}
  return !(f in prime_ideal(S))
end

### additional functionality
prime_ideal(S::MPolyComplementOfPrimeIdeal) = S.P

### printing
function Base.show(io::IO, S::MPolyComplementOfPrimeIdeal)
  print(io, "complement of ")
  print(io, prime_ideal(S))
end

### generation of random elements 
function rand(S::MPolyComplementOfPrimeIdeal, v1::UnitRange{Int}, v2::UnitRange{Int}, v3::UnitRange{Int})
  f = rand(ambient_ring(S), v1, v2, v3)
  if f in prime_ideal(S)
    return rand(S, v1, v2, v3)
  end
  return f
end


########################################################################
# Complements of maximal ideals corresponding to 𝕜-points              #
########################################################################

@Markdown.doc """
MPolyComplementOfKPointIdeal{
    BaseRingType,
    BaseRingElemType, 
    RingType,
    RingElemType
  } <: AbsMPolyMultSet{
    BaseRingType,
    BaseRingElemType, 
    RingType, 
    RingElemType
  }

Complement of a maximal ideal ``𝔪 = ⟨x₁-a₁,…,xₙ-aₙ⟩⊂ 𝕜[x₁,…xₙ]`` with ``aᵢ∈ 𝕜``.
"""
mutable struct MPolyComplementOfKPointIdeal{
    BaseRingType,
    BaseRingElemType, 
    RingType,
    RingElemType
  } <: AbsMPolyMultSet{
    BaseRingType,
    BaseRingElemType, 
    RingType, 
    RingElemType
  }

  # The parent polynomial ring 𝕜[x₁,…,xₙ]
  R::RingType
  # The coordinates aᵢ of the point in 𝕜ⁿ corresponding to the maximal ideal
  a::Vector{BaseRingElemType}

  function MPolyComplementOfKPointIdeal(R::RingType, a::Vector{T}) where {RingType<:MPolyRing, T<:RingElement}
    length(a) == length(gens(R)) || error("the number of variables in the ring does not coincide with the number of coordinates")
    n = length(a)
    kk = coefficient_ring(R)
    b = kk.(a) # fails if the input is not compatible
    S = new{typeof(kk), elem_type(kk), RingType, elem_type(R)}(R, b)
    return S
  end
end

### required getter functions
ambient_ring(S::MPolyComplementOfKPointIdeal) = S.R

### additional getter functions 
point_coordinates(S::MPolyComplementOfKPointIdeal) = S.a

### required functionality
function Base.in(
    f::RingElemType, 
    S::MPolyComplementOfKPointIdeal{BaseRingType, BaseRingElemType, RingType, RingElemType}
  ) where {BaseRingType, BaseRingElemType, RingType, RingElemType}
  parent(f) == ambient_ring(S) || return false
  return !(evaluate(f, point_coordinates(S)) == zero(ambient_ring(S)))
end

### printing
function Base.show(io::IO, S::MPolyComplementOfKPointIdeal)
  print(io, "point with coordinates ")
  print(io, point_coordinates(S))
end

### generation of random elements 
function rand(S::MPolyComplementOfKPointIdeal, v1::UnitRange{Int}, v2::UnitRange{Int}, v3::UnitRange{Int})
  f = rand(ambient_ring(S), v1, v2, v3)
  if !(f in S)
    return rand(S, v1, v2, v3)
  end
  return f
end


@Markdown.doc """
MPolyProductOfMultSets{
    BaseRingType,
    BaseRingElemType, 
    RingType,
    RingElemType
  } <: AbsMPolyMultSet{
    BaseRingType,
    BaseRingElemType, 
    RingType, 
    RingElemType
  }

A finite product `T⋅U = { a⋅b : a ∈ T, b∈ U}` of arbitrary other 
multiplicative sets in a multivariate polynomial ring.
"""
mutable struct MPolyProductOfMultSets{
    BaseRingType,
    BaseRingElemType, 
    RingType,
    RingElemType
  } <: AbsMPolyMultSet{
    BaseRingType,
    BaseRingElemType, 
    RingType, 
    RingElemType
  }
  R::RingType
  U::Vector{<:AbsMPolyMultSet{BaseRingType, BaseRingElemType, RingType, RingElemType}}

  function MPolyProductOfMultSets(R::RT, U::Vector{<:AbsMPolyMultSet{BRT, BRET, RT, RET}}) where {BRT<:Ring, BRET<:RingElement, RT<:MPolyRing, RET<:MPolyElem}
    for s in U
      ambient_ring(s) == R || error("multiplicative set does not live in the given ring")
    end
    return new{typeof(coefficient_ring(R)), elem_type(coefficient_ring(R)), typeof(R), elem_type(R)}(R, U)
  end
end

### required getter functions
ambient_ring(S::MPolyProductOfMultSets) = S.R

### additional functionality
get_index(S::MPolyProductOfMultSets, i::Integer) = S.U[i]
sets(S::MPolyProductOfMultSets) = copy(S.U)

### required functionality
function Base.in(
    f::RingElemType, 
    S::MPolyProductOfMultSets{BaseRingType, BaseRingElemType, RingType, RingElemType}
  ) where {BaseRingType, BaseRingElemType, RingType, RingElemType}
  R = ambient_ring(S)
  divides(one(R), f)[1] && return true
  U = sets(S)
  for s in U
    f in s && return true
  end
  # From here onwards, computations might not be cheap anymore
  a = factor(f)
  for fac in a
    # check for each factor whether it belongs to one of the admissible sets
    tmp_result = false
    for s in U
      if fac[1] in s 
	tmp_result = true
	break
      end
    end
    tmp_result || return false
  end
  return true
end

### printing
function Base.show(io::IO, S::MPolyProductOfMultSets)
  print(io, "product of the multiplicative sets [")
  for s in sets(S)
    print(io, s)
    s != last(sets(S)) && print(io, ", ")
  end
  print(io, "]")
end

### generation of random elements 
function rand(S::MPolyProductOfMultSets, v1::UnitRange{Int}, v2::UnitRange{Int}, v3::UnitRange{Int})
  return prod([rand(s, v1, v2, v3) for s in sets(S)])::elem_type(ambient_ring(S))
end

########################################################################
# Arithmetic of multiplicative sets                                    #
########################################################################

### containment ########################################################
⊂(T::AbsMPolyMultSet, U::AbsMPolyMultSet) = issubset(T, U)

function issubset(T::AbsMPolyMultSet, U::AbsMPolyMultSet) 
  ambient_ring(T) == ambient_ring(U) || return false
  error("comparison of multiplicative sets of type $(typeof(T)) and $(typeof(U)) is not implemented")
end

function ==(T::AbsMPolyMultSet, U::AbsMPolyMultSet) 
  return (issubset(T, U) && issubset(U, T))
end

function issubset(
    T::MPolyComplementOfPrimeIdeal{BRT, BRET, RT, RET},
    U::MPolyComplementOfPrimeIdeal{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  return issubset(prime_ideal(U), prime_ideal(T))
end

function issubset(
    T::MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET},
    U::MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  a = point_coordinates(U)
  b = point_coordinates(T)
  for i in 1:length(a)
    a[i] == b[i] || return false
  end
  return true
end

function issubset(
    T::MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET},
    U::MPolyComplementOfPrimeIdeal{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  a = point_coordinates(T)
  for i in 1:length(a)
    (gens(R)[i]- R(a[i])) in prime_ideal(U) || return false
  end
  return true
end

function issubset(
    T::MPolyComplementOfPrimeIdeal{BRT, BRET, RT, RET},
    U::MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  a = point_coordinates(U)
  for f in gens(prime_ideal(T))
    iszero(evaluate(f, a)) || return false
  end
  return true
end

function issubset(
    T::MPolyPowersOfElement{BRT, BRET, RT, RET},
    U::AbsMPolyMultSet{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  for a in denominators(T)
    a in U || return false
  end
  return true
end

function issubset(
    T::MPolyComplementOfPrimeIdeal{BRT, BRET, RT, RET},
    U::MPolyPowersOfElement{BRT, BRET, RT, RET},
  ) where {BRT, BRET, RT, RET}
  return false
end

function issubset(
    T::MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET},
    U::MPolyPowersOfElement{BRT, BRET, RT, RET},
  ) where {BRT, BRET, RT, RET}
  return false
end

### intersections ######################################################
function intersection(T::AbsMPolyMultSet, U::AbsMPolyMultSet) 
  error("intersection of multiplicative sets of type $(typeof(T)) and $(typeof(U)) is not implemented")
end

# TODO: Implement this if necessary!

### functionality for taking products
#
# Definition.
# Let T and U be multiplicative sets in a commutative ring R. The product 
# of T and U is defined as 
#
#   T⋅U = { f⋅g : f ∈ T and g ∈ U }.
#
# A product of multiplicative sets U = U₁⋅…⋅Uₙ is called interreduced 
# if neither one of the factors Uᵢ is contained in one of the others Uⱼ, j≠i.
#
# Lemma. 
# Any product of multiplicative sets U = U₁⋅…⋅Uₙ may be replaced by 
# an interreduced one. 
#
# Remark. 
# An interreduced factorization of a product of multiplicative sets may 
# not be unique: Consider the ring ℤ[x] and the multiplicative sets 
#   T  = {powers of 5x}
#   T' = {powers of x}
#   S  = {constant polynomials outside 7ℤ }.
# Then 
#   T⋅S = { a⋅xᵏ : a ∉ 7ℤ, k ∈ ℕ₀ } = T'⋅S.
#
# Upshot: Whenever a product is taken, some interreduced form of the 
# entire product is returned. Besides the obvious simplification in 
# case all factors are contained in a single one, it is difficult to 
# determine which interreduction is the best one. 

*(T::AbsMPolyMultSet, U::AbsMPolyMultSet) = product(T, U)

function product(T::AbsMPolyMultSet, U::AbsMPolyMultSet)
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  try 
    issubset(T, U) && return U
  catch
    @warn "comparison of multiplicative sets of types $(typeof(T)) and $(typeof(U)) is not implemented."
  end
  try
    issubset(U, T) && return T
  catch
    @warn "comparison of multiplicative sets of types $(typeof(U)) and $(typeof(T)) is not implemented."
  end
  return MPolyProductOfMultSets(R, [T, U])
end

function product(T::MST, U::MST) where {MST<:MPolyProductOfMultSets} 
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  new_sets = Vector{<:AbsMPolyMultSet}()
  for S in sets(T)
    push!(new_sets, S)
    for V in sets(U)
      if issubset(S, V) 
	pop!(new_sets)
	break
      end
    end
  end
  n = length(new_sets)
  for V in sets(U)
    push!(new_sets, V)
    for U in new_sets[1:n]
      if issubset(V, U) 
	pop!(new_sets)
	break
      end
    end
  end
  return MPolyProductOfMultSets(R, new_sets)
end

function product(T::MPolyProductOfMultSets{BRT, BRET, RT, RET}, U::MST) where {BRT, BRET, RT, RET, MST<:AbsMPolyMultSet{BRT, BRET, RT, RET}}
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  for V in sets(T)
    issubset(U, T) && return T
  end
  new_sets = U
  for V in sets(T)
    issubset(V, U) || push!(new_sets, V)
  end
  return MPolyProductOfMultSets(R, new_sets)
end

product(U::MST, T::MPolyProductOfMultSets{BRT, BRET, RT, RET}) where {BRT, BRET, RT, RET, MST<:AbsMPolyMultSet{BRT, BRET, RT, RET}} = product(T, U)

function product(T::MPolyComplementOfPrimeIdeal{BRT, BRET, RT, RET}, U::MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}) where {BRT, BRET, RT, RET}
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  P = prime_ideal(T)
  for f in gens(P)
    if iszero(evaluate(f, point_coordinates(U)))
      return MPolyProductOfMultSets(R, [U, T])
    end
  end
  return U
end

function product(
    U::MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET},
    T::MPolyComplementOfPrimeIdeal{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  return product(T, U)
end

function product(T::MST, U::MST) where {MST<:MPolyComplementOfKPointIdeal}
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  a = point_coordinates(U)
  b = point_coordinates(T)
  for i in 1:length(a)
    a[i] == b[i] || return MPolyProductOfMultSets(R, [U, T])
  end
  return T
end

function product(T::MST, U::MST) where {MST<:MPolyComplementOfPrimeIdeal}
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  if issubset(prime_ideal(T), prime_ideal(U))
    return T
  end
  if issubset(prime_ideal(U), prime_ideal(T))
    return U
  end
  return MPolyProductOfMultSets(R, [U, T])
end

function product(T::MST, U::MST) where {MST<:MPolyPowersOfElement}
  R = ambient_ring(T) 
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  new_denoms = Vector{elem_type(R)}()
  for f in denominators(T)
    for g in denominators(U)
      (_, f) = ppio(f, g)
    end
    if !(divides(one(parent(f)), f)[1])
      push!(new_denoms, f)
    end
  end
  n = length(new_denoms)
  for g in denominators(U)
    for f in new_denoms[1:n]
      (_, g) = ppio(g, f)
    end
    if !(divides(one(parent(g)), g)[1])
      push!(new_denoms, g)
    end
  end
  return (length(new_denoms) == 0 ? units_of(R) : MPolyPowersOfElement(R, new_denoms))
end

function product(
    T::MPolyPowersOfElement{BRT, BRET, RT, RET},
    U::AbsMPolyMultSet{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  for a in denominators(T)
    a in U || return MPolyProductOfMultSets(R, [U, T])
  end
  return U
end

### Preimages of multiplicative sets.
# In general for a ring homomorphism f : R → S and a multiplicative 
# set U ⊂ S the preimage V = f⁻¹(U) is a multiplicative set in R. 
# Membership in V can easily be tested, but introducing a new type 
# for preimages makes it necessary to extend all dispatch routines. 
# It is not clear what is the best strategy for all this. 

function preimage(f::Oscar.AlgHom, U::MST) where {MST<:AbsMPolyMultSet}
  error("not implemented")
end

########################################################################
# Localizations of polynomial rings over admissible fields             #
########################################################################

@Markdown.doc """
MPolyLocalizedRing{
    BaseRingType,
    BaseRingElemType,
    RingType,
    RingElemType,
    MultSetType
  } <: AbsLocalizedRing{
    RingType,
    RingType,
    MultSetType
  }

The localization of a multivariate polynomial ring ``R = 𝕜[x₁,…,xₙ]`` over a 
base field ``𝕜`` of type `BaseRingType` and with elements of type `RingElemType` 
at a multiplicative set ``S ⊂ R`` of type `MultSetType`.
"""
mutable struct MPolyLocalizedRing{
    BaseRingType,
    BaseRingElemType,
    RingType,
    RingElemType,
    MultSetType <: AbsMPolyMultSet{BaseRingType, BaseRingElemType, RingType, RingElemType}
  } <: AbsLocalizedRing{
    RingType,
    RingType,
    MultSetType
  }
  R::RingType # The parent ring which is being localized
  S::MultSetType # The multiplicatively closed set that has been inverted 

  function MPolyLocalizedRing(
      R::RingType, 
      S::MultSetType
    ) where {RingType<:MPolyRing, MultSetType<:AbsMPolyMultSet}
    # TODO: Add some sanity checks here?
    ambient_ring(S) == R || error("the multiplicative set is not contained in the given ring")
    k = coefficient_ring(R)
    R_loc = new{typeof(k), elem_type(k), RingType, elem_type(R), MultSetType}(R, S)
    return R_loc
  end
end

### required getter functions 
base_ring(W::MPolyLocalizedRing) = W.R
inverted_set(W::MPolyLocalizedRing) = W.S

### additional getter functions
gens(W::MPolyLocalizedRing) = W.(gens(base_ring(W)))

### required extension of the localization function
Localization(S::MPolyComplementOfPrimeIdeal) = MPolyLocalizedRing(ambient_ring(S), S)

Localization(S::MPolyComplementOfKPointIdeal) = MPolyLocalizedRing(ambient_ring(S), S)

Localization(S::MPolyPowersOfElement) = MPolyLocalizedRing(ambient_ring(S), S)

Localization(S::MPolyProductOfMultSets) = MPolyLocalizedRing(ambient_ring(S), S)

### Successive localizations are handled by the dispatch for products
function Localization(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    S::AbsMPolyMultSet{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET, MST}
  issubset(S, inverted_set(W)) && return W
  return Localization(S*inverted_set(W))
end

### additional constructors
MPolyLocalizedRing(R::RingType, P::MPolyIdeal{RingElemType}) where {RingType, RingElemType} = MPolyLocalizedRing(R, MPolyComplementOfPrimeIdeal(P))

Localization(R::MPolyRing, f::MPolyElem) = Localization(MPolyPowersOfElement(R, [f]))
Localization(R::MPolyRing, v::Vector{T}) where {T<:MPolyElem} = Localization(MPolyPowersOfElement(R, v))

function Localization(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MPolyPowersOfElement{BRT, BRET, RT, RET}}, 
    f::RET
  ) where {BRT, BRET, RT, RET<:RingElement}
  R = base_ring(W)
  parent(f) == R || error("the given element does not belong to the correct ring")
  S = inverted_set(W)
  if f in S
    return W
  end
  g = denominators(S)
  h = gcd(prod(g), f)
  return MPolyLocalizedRing(R, MPolyPowersOfElement(R, vcat(g, divexact(f, h))))
end

function Localization(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MPolyPowersOfElement{BRT, BRET, RT, RET}}, 
    v::Vector{RET}
  ) where {BRT, BRET, RT, RET}
  V = W
  for f in v
    V = Localization(V, f)
  end
  return V
end

### generation of random elements 
function rand(W::MPolyLocalizedRing, v1::UnitRange{Int}, v2::UnitRange{Int}, v3::UnitRange{Int})
  return W(rand(base_ring(W), v1, v2, v3), rand(inverted_set(W), v1, v2, v3))
end


########################################################################
# Elements of localized polynomial rings                               #
########################################################################

@Markdown.doc """
MPolyLocalizedRingElem{
    BaseRingType, 
    BaseRingElemType,
    RingType,
    RingElemType, 
    MultSetType
  } <: AbsLocalizedRingElem{
    RingType,
    RingElemType, 
    MultSetType
  } 

Elements of localizations of polynomial rings.
"""
mutable struct MPolyLocalizedRingElem{
    BaseRingType, 
    BaseRingElemType,
    RingType,
    RingElemType, 
    MultSetType
  } <: AbsLocalizedRingElem{
    RingType,
    RingElemType, 
    MultSetType
  } 

  W::MPolyLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}
  frac::AbstractAlgebra.Generic.Frac{RingElemType}

  function MPolyLocalizedRingElem(
      W::MPolyLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType},
      f::AbstractAlgebra.Generic.Frac{RingElemType};
      check::Bool=true
    ) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}
    base_ring(parent(f)) == base_ring(W) || error(
	"the numerator and denominator of the given fraction do not belong to the original ring before localization"
      )
    if check
      denominator(f) in inverted_set(W) || error("the given denominator is not admissible for this localization")
    end
    return new{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}(W, f)
  end
end

### required getter functions 
numerator(a::MPolyLocalizedRingElem) = numerator(a.frac)

denominator(a::MPolyLocalizedRingElem) = denominator(a.frac)

parent(a::MPolyLocalizedRingElem) = a.W

### additional getter functions
fraction(a::MPolyLocalizedRingElem) = a.frac

### required conversions
(W::MPolyLocalizedRing{
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    MultSetType
  })(f::RingElemType; check::Bool=true) where {
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    MultSetType
  } = MPolyLocalizedRingElem(W, FractionField(base_ring(W))(f), check=check)

function (W::MPolyLocalizedRing{
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    MultSetType
  })(a::RingElemType, b::RingElemType; check::Bool=true) where {
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    MultSetType
  } 
  return MPolyLocalizedRingElem(W, a//b, check=check)
end

### additional conversions
(W::MPolyLocalizedRing{
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    MultSetType
  })(f::AbstractAlgebra.Generic.Frac{RingElemType}; check::Bool=true) where {
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    MultSetType
  } = MPolyLocalizedRingElem(W, f, check=check)

### additional promotions 
AbstractAlgebra.promote_rule(::Type{RET}, ::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}) where {BRT, BRET, RT<:Ring, RET<:RingElement, MST} = MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}

AbstractAlgebra.promote_rule(::Type{BRET}, ::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}) where {BRT<:Ring, BRET<:RingElement, RT<:Ring, RET<:RingElement, MST} = MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}

AbstractAlgebra.promote_rule(::Type{Integer}, ::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}) where {BRT<:Ring, BRET<:RingElement, RT<:Ring, RET<:RingElement, MST} = MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}

AbstractAlgebra.promote_rule(::Type{fmpz}, ::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}) where {BRT<:Ring, BRET<:RingElement, RT<:Ring, RET<:RingElement, MST} = MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}

### overwriting the arithmetic using the fractions from AbstractAlgebra
function +(a::T, b::T) where {T<:MPolyLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return (parent(a))(fraction(a) + fraction(b), check=false)
end

function -(a::T, b::T) where {T<:MPolyLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return (parent(a))(fraction(a) - fraction(b), check=false)
end

function -(a::T) where {T<:MPolyLocalizedRingElem}
  return (parent(a))((-1)*fraction(a), check=false)
end

function *(a::T, b::T) where {T<:MPolyLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return (parent(a))(fraction(a) * fraction(b), check=false)
end

function *(a::RET, b::MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}) where {BRT, BRET, RT, RET <: RingElem, MST}
  return (parent(b))(a*fraction(b), check=false)
end

function *(a::MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}, b::RET) where {BRT, BRET, RT, RET <: RingElem, MST}
  return b*a
end

function *(a::BRET, b::MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}) where {BRT, BRET <: RingElem, RT, RET, MST}
  return (parent(b))(a*fraction(b), check=false)
end

function *(a::MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}, b::BRET) where {BRT, BRET <: RingElem, RT, RET, MST}
  return b*a
end

function Base.:(//)(a::Integer, b::T) where {T<:MPolyLocalizedRingElem}
  return (parent(b))(a//fraction(b))
end

function Base.:(//)(a::fmpz, b::T) where {T<:MPolyLocalizedRingElem}
  return (parent(b))(a//fraction(b))
end

function Base.:(//)(a::T, b::T) where {T<:MPolyLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  g = gcd(numerator(a), numerator(b))
  c = divexact(numerator(a), g)
  d = divexact(numerator(b), g)
  numerator(fraction(b)) in inverted_set(parent(b)) || error("the second argument is not a unit in this local ring")
  return (parent(a))(fraction(a) // fraction(b), check=false)
end

function ==(a::T, b::T) where {T<:MPolyLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return fraction(a) == fraction(b)
end

# We need to manually split this into three methods, because 
# otherwise it seems that Julia can not dispatch this function.
function ^(a::MPolyLocalizedRingElem, i::Int64)
  return parent(a)(fraction(a)^i, check=false)
end
function ^(a::MPolyLocalizedRingElem, i::Integer)
  return parent(a)(fraction(a)^i, check=false)
end
function ^(a::MPolyLocalizedRingElem, i::fmpz)
  return parent(a)(fraction(a)^i, check=false)
end

function divexact(p::T, q::T; check::Bool=false) where {T<:MPolyLocalizedRingElem} 
  W = parent(p)
  S = inverted_set(W)
  parent(q) == W || error("incompatible rings")
  a = numerator(p)
  b = denominator(p)
  c = numerator(q)
  d = denominator(q)
  ### a/b = (m/n)*(c/d) <=> a*d*n = c*b*m.
  # Using the factoriality of polynomial rings, 
  # we can cancel common factors of a*d and c*b 
  # and read off the minimal m and n from that.
  a = a*d
  c = c*b
  g = gcd(a, c)
  m = divexact(a, g)
  n = divexact(c, g)
  if !(n in S) 
    error("not an exact division")
  end
  return W(m, n, check=false)
end

isunit(f::MPolyLocalizedRingElem) = numerator(f) in inverted_set(parent(f))


########################################################################
# implementation of Oscar's general ring interface                     #
########################################################################

one(W::MPolyLocalizedRing) = W(one(base_ring(W)))
zero(W::MPolyLocalizedRing) = W(zero(base_ring(W)))

elem_type(W::MPolyLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyLocalizedRingElem{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}
elem_type(T::Type{MPolyLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}}) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyLocalizedRingElem{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}

parent_type(f::MPolyLocalizedRingElem{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}
parent_type(T::Type{MPolyLocalizedRingElem{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}}) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}

(W::MPolyLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType})(f::MPolyLocalizedRingElem{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}; check::Bool=true) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyLocalizedRingElem(W, fraction(f), check=check)

(W::MPolyLocalizedRing)() = zero(W)
(W::MPolyLocalizedRing)(a::Integer; check::Bool=true) = W(base_ring(W)(a), check=check)

isdomain_type(T::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}) where {BRT, BRET, RT, RET, MST} = true 
isexact_type(T::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}) where {BRT, BRET, RT, RET, MST} = true

### promotion rules
AbstractAlgebra.promote_rule(::Type{MPolyLocalizedRingElem{RT, RET, MST}}, ::Type{MPolyLocalizedRingElem{RT, RET, MST}}) where {RT<:Ring, RET<:RingElement, MST} = MPolyLocalizedRingElem{RT, RET, MST}

function AbstractAlgebra.promote_rule(::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}, ::Type{T}) where {BRT<:Ring, BRET<:RingElement, RT<:Ring, RET<:RingElement, MST, T<:RingElement} 
  AbstractAlgebra.promote_rule(RET, T) == RET && return MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}
  return AbstractAlgebra.promote_rule(BRET, T) == BRET ? MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST} : Union{}
end

########################################################################
# Singular functionality                                               #
########################################################################
@Markdown.doc """
LocalizedBiPolyArray{BRT, BRET, RT, RET, MST}

Main workhorse for binding of ideals in localizations ``R[S⁻¹]`` of 
multivariate polynomial rings ``R = 𝕜[x₁,…,xₙ]`` to Singular. 
"""
mutable struct LocalizedBiPolyArray{BRT, BRET, RT, RET, MST}
  # The generators on the Oscar side
  oscar_gens::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}
  # The numerators of the above fractions as elements in the singular version 
  # of the original ring before localization.
  singular_gens::Singular.sideal
  # The localized ring on the Oscar side.
  oscar_ring::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}
  # The polynomial ring on the singular side
  singular_ring::Singular.PolyRing
  # The ordering used for the above singular ring.
  ordering::Symbol
  # An optional shift vector applied to the polynomials in Oscar when 
  # translating them to the Singular ring. 
  # This is to make local orderings useful for localizations at 𝕜-points.
  shift::Vector{BRET}
  # Flag for caching
  is_groebner_basis::Bool

  function LocalizedBiPolyArray(
      oscar_ring::MPolyLocalizedRing{BRT, BRET, RT, RET, MST},
      oscar_gens::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}};
      ordering::Symbol=:degrevlex, 
      shift::Vector{BRET}=Vector{BRET}()
    ) where {BRT, BRET, RT, RET, MST}
    lbpa = new{BRT, BRET, RT, RET, MST}()
    # TODO: Add some sanity checks here
    lbpa.oscar_ring = oscar_ring
    lbpa.oscar_gens = oscar_gens
    lbpa.ordering = ordering
    # fill up the shift vector with zeroes if it is not provided in full length
    for i in (length(shift)+1:nvars(base_ring(oscar_ring)))
      push!(shift, zero(coefficient_ring(base_ring(oscar_ring))))
    end
    lbpa.shift = shift
    lbpa.is_groebner_basis=false
    return lbpa
  end
  
  function LocalizedBiPolyArray(
      oscar_ring::MPolyLocalizedRing{BRT, BRET, RT, RET, MST},
      singular_gens::Singular.sideal; 
      shift::Vector{BRET}=Vector{BRET}(), 
      is_groebner_basis::Bool=false,
      ordering::Symbol=:degrevlex
    ) where {BRT, BRET, RT, RET, MST}
    lbpa = new{BRT, BRET, RT, RET, MST}()
    # TODO: Add some sanity checks here
    lbpa.oscar_ring = oscar_ring
    lbpa.singular_gens = singular_gens
    lbpa.singular_ring = base_ring(singular_gens)
    R = base_ring(oscar_ring)
    lbpa.ordering = Singular.ordering_as_symbol(lbpa.singular_ring)
    k = coefficient_ring(R)
    # fill up the shift vector with zeroes if it is not provided in full length
    for i in (length(shift)+1:nvars(R))
      push!(shift, zero(k))
    end
    lbpa.shift = shift
    inv_shift_hom = AlgebraHomomorphism(R, R, [gen(R, i) - R(shift[i]) for i in (1:nvars(R))])
    lbpa.oscar_gens = [ oscar_ring(y) for y in (inv_shift_hom.(R.([x for x in gens(singular_gens)])))]
    lbpa.is_groebner_basis=is_groebner_basis
    return lbpa
  end
end

oscar_gens(lbpa::LocalizedBiPolyArray) = lbpa.oscar_gens
oscar_ring(lbpa::LocalizedBiPolyArray) = lbpa.oscar_ring
ordering(lbpa::LocalizedBiPolyArray) = lbpa.ordering
shift(lbpa::LocalizedBiPolyArray) = lbpa.shift

function singular_gens(lbpa::LocalizedBiPolyArray)
  singular_assure(lbpa)
  return lbpa.singular_gens
end

function singular_ring(lbpa::LocalizedBiPolyArray)
  singular_assure(lbpa)
  return lbpa.singular_ring
end

function singular_assure(lbpa::LocalizedBiPolyArray)
  if !isdefined(lbpa, :singular_ring)
    lbpa.singular_ring = Singular.PolynomialRing(
	Oscar.singular_ring(base_ring(base_ring(oscar_ring(lbpa)))), 
        [string(a) for a = Nemo.symbols(base_ring(oscar_ring(lbpa)))], 
        ordering = ordering(lbpa), 
        cached = false
      )[1]
  end
  if !isdefined(lbpa, :singular_gens)
    shift_hom = hom(base_ring(oscar_ring(lbpa)), base_ring(oscar_ring(lbpa)), 
        [gen(base_ring(oscar_ring(lbpa)), i) + lbpa.shift[i] for i in (1:nvars(base_ring(oscar_ring(lbpa))))])
    lbpa.singular_gens = Singular.Ideal(lbpa.singular_ring,
	[lbpa.singular_ring(shift_hom(numerator(x))) for x in oscar_gens(lbpa)])
  end
end

function std(lbpa::LocalizedBiPolyArray)
  i = Singular.std(singular_gens(lbpa))
  return LocalizedBiPolyArray(
             oscar_ring(lbpa), 
	     i, 
	     is_groebner_basis=true, 
	     shift=shift(lbpa),
	     ordering=ordering(lbpa)
	   )
end


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
# which I = I'⋅W. We call this the `saturated ideal` of the localization.

@Markdown.doc """
MPolyLocalizedIdeal{BRT, BRET, RT, RET, MST} <: AbsLocalizedIdeal{RT, RET, MST}

Ideals in localizations of polynomial rings.
"""
mutable struct MPolyLocalizedIdeal{BRT, BRET, RT, RET, MST} <: AbsLocalizedIdeal{RT, RET, MST}
  # the initial set of generators, not to be changed ever!
  gens::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}
  # the ambient ring for this ideal
  W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST} 
  
  # Fields for caching
  groebner_bases::Dict{Symbol, LocalizedBiPolyArray{BRT, BRET, RT, RET, MST}}
  dimension::Int
  saturated_ideal::MPolyIdeal{RET} 
 
  function MPolyLocalizedIdeal(
      W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
      gens::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}};
      check::Bool=false
    ) where {BRT, BRET, RT, RET, MST}
    R = base_ring(W)
    k = base_ring(R)
    S = inverted_set(W)
    for f in gens
      parent(f) == W || error("generator is not an element of the given ring")
      check && (denominator(f) in S || error("fraction is not an element of the localization"))
    end
    I = new{BRT, BRET, RT, RET, MST}()
    I.gens = gens
    I.W = W
    I.groebner_bases = Dict{Symbol, LocalizedBiPolyArray{BRT, BRET, RT, RET, MST}}()
    return I
  end
end
 
### required getter functions
gens(I::MPolyLocalizedIdeal) = copy(I.gens)
base_ring(I::MPolyLocalizedIdeal) = I.W

function saturated_ideal(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MST}
  ) where {BRT, BRET, RT, RET, MST}
  error("method `saturated_ideal` is not implemented for multiplicative sets of type $(typeof(inverted_set(base_ring(I))))")
end

function saturated_ideal(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyComplementOfPrimeIdeal{BRT, BRET, RT, RET}}
  ) where {BRT, BRET, RT, RET}
  ### saturation has to proceed via primary decomposition in this case. 
  # We rely on the primary decomposition on the singular side which is 
  # already implemented so that all non-relevant components are thrown 
  # away. The remaining components are then intersected to produce 
  # the ideal in question. 
  lbpa = BiPolyArray(I)
  V = base_ring(I)
  R = base_ring(V)
  sing_decomp = Singular.LibPrimdec.primdecGTZ(singular_ring(lbpa), singular_gens(lbpa))
  decomp = [BiPolyArray(V, K[1]) for K in Singular.LibPrimdec.primdecGTZ(singular_ring(lbpa), singular_gens(lbpa))]
  if length(decomp) == 0
    return ideal(R, zero(R))
  end
  relevant_comp = BiPolyArray(V, [one(V)])
  U = inverted_set(V)
  P = prime_ideal(U)
  for comp in decomp
    # Check whether the given component is contained in P.
    issubset(ideal(R, numerator.(oscar_gens(comp))), P) && (relevant_comp = BiPolyArray(V, Singular.intersection(singular_gens(relevant_comp), singular_gens(comp))))
  end
  return ideal(R, numerator.(oscar_gens(relevant_comp)))
end

function saturated_ideal(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}}
  ) where {BRT, BRET, RT, RET}
  ### saturation has to proceed via primary decomposition in this case. 
  # We rely on the primary decomposition on the singular side which is 
  # already implemented so that all non-relevant components are thrown 
  # away. The remaining components are then intersected to produce 
  # the ideal in question. 
  lbpa = BiPolyArray(I)
  V = base_ring(I)
  R = base_ring(V)
  sing_decomp = Singular.LibPrimdec.primdecGTZ(singular_ring(lbpa), singular_gens(lbpa))
  decomp = [BiPolyArray(V, K[1]) for K in Singular.LibPrimdec.primdecGTZ(singular_ring(lbpa), singular_gens(lbpa))]
  if length(decomp) == 0
    return ideal(R, zero(R))
  end
  relevant_comp = decomp[1]
  for i in (2:length(decomp))
    relevant_comp = BiPolyArray(V, Singular.intersection(singular_gens(relevant_comp), singular_gens(decomp[i])))
  end
  return ideal(R, numerator.(oscar_gens(relevant_comp)))
end

function saturated_ideal(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyPowersOfElement{BRT, BRET, RT, RET}}
  ) where {BRT, BRET, RT, RET}
  if !isdefined(I, :saturated_ideal)
    W = base_ring(I)
    R = base_ring(W)
    U = inverted_set(W)
    lbpa = BiPolyArray(I)
    sat_ideal = singular_gens(lbpa)
    for a in denominators(U)
      sat_ideal = Singular.saturation(sat_ideal, Singular.Ideal(singular_ring(lbpa), [singular_ring(lbpa)(a)]))[1]
    end
    I.saturated_ideal = ideal(R, R.(gens(sat_ideal)))
  end
  return I.saturated_ideal
end

function saturated_ideal(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyProductOfMultSets{BRT, BRET, RT, RET}}
  ) where {BRT, BRET, RT, RET}
  if !isdefined(I, :saturated_ideal)
    W = base_ring(I)
    R = base_ring(W)
    J = ideal(R, numerator.(gens(I)))
    for U in sets(inverted_set(W))
      L = Localization(U)
      J = saturated_ideal(L(J))
    end
    I.saturated_ideal = J
  end
  return I.saturated_ideal
end



# TODO: Extend the above functionality for other types of localizations.

### additional getter functions
groebner_bases(I::MPolyLocalizedIdeal) = I.groebner_bases

# the default ordering; probably mathematically useless
default_ordering(I::MPolyLocalizedIdeal) = :degrevlex

# specific default orderings for other cases
default_ordering(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyPowersOfElement{BRT, BRET, RT, RET}}
  ) where {BRT, BRET, RT, RET} = :degrevlex

default_ordering(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}}
  ) where {BRT, BRET, RT, RET} = :negdegrevlex

function dim(I::MPolyLocalizedIdeal)
  if isdefined(I,:dimension)
    return I.dimension
  end
  error("not implemented")
end

### Conversion of ideals in the original ring to localized ideals
function (W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST})(I::MPolyIdeal{RET}) where {BRT, BRET, RT, RET, MST}
  return MPolyLocalizedIdeal(W, W.(gens(I)))
end

### required constructors 
function ideal(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    f::MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}
  ) where {BRT, BRET, RT, RET, MST}
  return MPolyLocalizedIdeal(W, [f])
end

function ideal(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    gens::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}
  ) where {BRT, BRET, RT, RET, MST}
  return MPolyLocalizedIdeal(W, gens)
end

function ideal(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    f::RET
  ) where {BRT, BRET, RT, RET, MST}
  return MPolyLocalizedIdeal(W, [W(f)])
end

function ideal(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    gens::Vector{RET}
  ) where {BRT, BRET, RT, RET, MST}
  return MPolyLocalizedIdeal(W, W.(gens))
end

### required functionality
function Base.in(
    f::MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}, 
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MST} 
  ) where {BRT, BRET, RT, RET, MST}
  parent(f) == base_ring(I) || return false
  lbpa = groebner_basis(I)
  return iszero(reduce(f, lbpa))
end

function Base.in(
    f::RET, 
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MST} 
  ) where {BRT, BRET, RT, RET, MST}
  return base_ring(I)(f) in I
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
function intersection(I::IdealType, J::IdealType) where {IdealType<:MPolyLocalizedIdeal}
  return base_ring(I)(intersect(saturated_ideal(I), saturated_ideal(J)))
end

# TODO: The following method can probably be fine tuned for specific localizations.
function quotient(I::IdealType, J::IdealType) where {IdealType<:MPolyLocalizedIdeal}
  return base_ring(I)(quotient(saturated_ideal(I), saturated_ideal(J)))
end


### Default constructors 
# The ordering and the shifts are determined from the type of the multiplicative set
BiPolyArray(
    I::MPolyLocalizedIdeal;
    ordering=:negdegrevlex
  ) = LocalizedBiPolyArray(base_ring(I), gens(I), ordering=ordering) 

BiPolyArray(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    g::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}};
    ordering=:negdegrevlex
  ) where {BRT, BRET, RT, RET, MST} = LocalizedBiPolyArray(W, g, ordering=ordering) 

BiPolyArray(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    g::MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST};
    ordering=:negdegrevlex
  ) where {BRT, BRET, RT, RET, MST} = ByPolyArray(W, [g], ordering=ordering)

BiPolyArray(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    I::MPolyIdeal{RET};
    ordering=:negdegrevlex
  ) where {BRT, BRET, RT, RET, MST} = LocalizedBiPolyArray(W, W.(gens(I)), ordering=ordering) 

BiPolyArray(
    W::MPolyLocalizedRing, 
    I::Singular.sideal;
    is_groebner_basis::Bool=false
  ) = LocalizedBiPolyArray(W, I, ordering=Singular.ordering_as_symbol(base_ring(I)), is_groebner_basis=is_groebner_basis) 

BiPolyArray(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}};
    ordering=:negdegrevlex
  ) where {BRT, BRET, RT, RET} = LocalizedBiPolyArray(base_ring(I), gens(I), ordering=ordering, shift=point_coordinates(inverted_set(base_ring(I)))) 

BiPolyArray(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    g::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}};
    ordering=:negdegrevlex
  ) where {BRT, BRET, RT, RET, MST<:MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}} = LocalizedBiPolyArray(W, g, ordering=ordering, shift=point_coordinates(inverted_set(W))) 

BiPolyArray(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}}, 
    I::MPolyIdeal{RET};
    ordering=:negdegrevlex
  ) where {BRT, BRET, RT, RET} = LocalizedBiPolyArray(W, W.(gens(I)), ordering=ordering, shift=point_coordinates(inverted_set(W))) 

BiPolyArray(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}}, 
    I::Singular.sideal;
    is_groebner_basis::Bool=false
  ) where {BRT, BRET, RT, RET} = LocalizedBiPolyArray(W, I, ordering=Singular.ordering_as_symbol(base_ring(I)), shift=point_coordinates(inverted_set(W)), is_groebner_basis=is_groebner_basis) 

BiPolyArray(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MPolyPowersOfElement{BRT, BRET, RT, RET}},
    I::MPolyIdeal{RET};
    ordering=:degrevlex
  ) where {BRT, BRET, RT, RET} = LocalizedBiPolyArray(W, W.(gens(I)), ordering=ordering) 

BiPolyArray(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyPowersOfElement{BRT, BRET, RT, RET}};
    ordering=:degrevlex
  ) where {BRT, BRET, RT, RET} = LocalizedBiPolyArray(base_ring(I), gens(I), ordering=ordering) 

BiPolyArray(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MPolyPowersOfElement{BRT, BRET, RT, RET}},
    I::Singular.sideal;
    is_groebner_basis::Bool=false
  ) where {BRT, BRET, RT, RET} = LocalizedBiPolyArray(W, I, ordering=Singular.ordering_as_symbol(base_ring(I)), is_groebner_basis=is_groebner_basis)

function Base.show(io::IO, I::MPolyLocalizedIdeal) 
  print(io, "ideal in $(base_ring(I)) generated by the elements ") 
  n = length(gens(I))
  for i in (1:n-1)
    print(io, "$(gens(I)[i]), ")
  end
  print(io, last(gens(I)))
end

########################################################################
# Groebner and standard bases                                          #
########################################################################
#
# A "groebner basis" for an ideal I in a localized ring W = R[S⁻¹] in 
# is a LocalizedBiPolyArray G for which the following holds.
#
# G has attached to it an ordering and a singular ring. The reduction 
# of the numerator a of an element a//b of a localized ring W = R[S⁻¹] 
# by the elements of G with respect to that ordering has to be zero 
# if and only if a//b belongs to the ideal. 

### The catchall implementation. 
# This refers back to the saturated ideal procedures and ideal 
# membership of the numerator in the base_ring.
function groebner_basis(
    I::MPolyLocalizedIdeal,
    ordering::Symbol
  )
  D = groebner_bases(I)
  # check whether a standard basis has already been computed for this ordering
  if haskey(D, ordering)
    return D[ordering]
  end
  # if not, set up a LocalizedBiPolyArray
  W = base_ring(I)
  lbpa = BiPolyArray(W(saturated_ideal(I)), ordering=ordering)
  # compute the standard basis and cache the result
  D[ordering] = std(lbpa)
  return D[ordering]
end

function groebner_basis(I::MPolyLocalizedIdeal)
  return groebner_basis(I, default_ordering(I))
end

function groebner_assure(I::MPolyLocalizedIdeal)
  D = groebner_bases(I)
  if length(D) > 0 
    return
  end
  D[default_ordering(I)] = std(BiPolyArray(I))
  return
end

### special routines for localizations at 𝕜-points.
# This is using local orderings.
function groebner_basis(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}}; 
    ordering::Symbol=:negdegrevlex
  ) where {BRT, BRET, RT, RET}
  D = groebner_bases(I)
  # check whether a standard basis has already been computed for this ordering
  if haskey(D, ordering)
    return D[ordering]
  end
  # if not, set up a LocalizedBiPolyArray
  lbpa = BiPolyArray(I, ordering=ordering)
  # Check whether this ordering is admissible
  !Singular.has_local_ordering(singular_ring(lbpa)) && error("The ordering has to be a local ordering.")
  # compute the standard basis and cache the result.
  # No saturation is necessary in this case. 
  D[ordering] = std(lbpa)
  return D[ordering]
end

### special routine for localizations at complements of prime ideals.
# This uses the saturated ideal computed via primary decomposition.
function groebner_basis(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyComplementOfPrimeIdeal{BRT, BRET, RT, RET}}; 
    ordering::Symbol=:degrevlex
  ) where {BRT, BRET, RT, RET}
  D = groebner_bases(I)
  # check whether a standard basis has already been computed for this ordering
  if haskey(D, ordering)
    return D[ordering]
  end
  # if not, set up a LocalizedBiPolyArray
  # Note that saturation is essential here!
  lbpa = BiPolyArray(base_ring(I), saturated_ideal(I), ordering=ordering) 
  D[ordering] = std(lbpa)
  return D[ordering]
end
  
### special routines for localizations at powers of elements.
# This performs saturation.
function groebner_basis(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MPolyPowersOfElement{BRT, BRET, RT, RET}}; 
    ordering::Symbol=:degrevlex
  ) where {BRT, BRET, RT, RET}
  D = groebner_bases(I)
  # check whether a standard basis has already been computed for this ordering
  if haskey(D, ordering)
    return D[ordering]
  end
  # if not, set up a LocalizedBiPolyArray
  # Note that saturation is essential here!
  lbpa = BiPolyArray(base_ring(I), saturated_ideal(I), ordering=ordering) 
  D[ordering] = std(lbpa)
  return D[ordering]
end


### reduction to normal form with respect to a list of elements.
# Note that by convention, this reduces only the numerators.
function Base.reduce(
    f::MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}, 
    lbpa::LocalizedBiPolyArray{BRT, BRET, RT, RET, MST}
  ) where {BRT, BRET, RT, RET, MST}

  W = parent(f)
  W == oscar_ring(lbpa) || error("element does not belong to the Oscar ring of the biPolyArray")
  R = base_ring(W)
  shift_hom = hom(R, R, [gen(R, i) + lbpa.shift[i] for i in (1:nvars(R))])
  singular_n = singular_ring(lbpa)(shift_hom(numerator(f)))
  singular_n = Singular.reduce(singular_n, singular_gens(lbpa))
  if iszero(singular_n) 
    return zero(W)
  end
  inv_shift_hom = hom(R,R, [gen(R, i) - lbpa.shift[i] for i in (1:nvars(R))])
  return W(inv_shift_hom(R(singular_n)), denominator(f))
end


########################################################################
# Homomorphisms of localized polynomial rings                          #
########################################################################
#
# Let P = 𝕜[x₁,…,xₘ] and Q = 𝕜[y₁,…,yₙ] be polynomial rings 
# Any homomorphism ϕ : P[U⁻¹] → Q[V⁻¹] is completely determined 
# by the images of the variables 
#
#     ϕ(xᵢ) = aᵢ(y)/ bᵢ(y)
#
# where bᵢ(y) ∈ V for all i. Given such a list of images
# one can always define the associated homomorphism ϕ' : P → Q[V⁻¹]. 
# This extends to a well defined homomorphism ϕ as above iff
#
#     for all f ∈ U : ϕ'(f) is a unit in Q[V⁻¹]            (*)
#
# and this is easily seen to be the case iff there exists an 
# element c ∈ V such that c⋅ϕ'(f) ∈ V

mutable struct MPolyLocalizedRingHom{BaseRingType, BaseRingElemType, 
    RingType, RingElemType, DomainMultSetType, CodomainMultSetType
  } <: AbsLocalizedRingHom{
    RingType, RingElemType, DomainMultSetType, CodomainMultSetType
  }
  # the domain of definition
  V::MPolyLocalizedRing{BaseRingType, BaseRingElemType, 
			RingType, RingElemType, DomainMultSetType}
  # the codomain 
  W::MPolyLocalizedRing{BaseRingType, BaseRingElemType, 
			RingType, RingElemType, CodomainMultSetType}
  # the images of the variables
  images::Vector{MPolyLocalizedRingElem{
    BaseRingType, BaseRingElemType, RingType, RingElemType, 
    CodomainMultSetType}}

  function MPolyLocalizedRingHom(
      V::MPolyLocalizedRing{BRT, BRET, RT, RET, DMST}, 
      W::MPolyLocalizedRing{BRT, BRET, RT, RET, CMST}, 
      a::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, CMST}}
    ) where {BRT, BRET, RT, RET, CMST, DMST}
    R = base_ring(V)
    S = base_ring(W)
    k = coefficient_ring(R) 
    k == coefficient_ring(S) || error("the two polynomial rings are not defined over the same coefficient ring")
    ngens(R) == length(a) || error("the number of images does not coincide with the number of variables")
    parent_check = true
    for x in a
      parent_check = parent_check && parent(x) == W
      denominator(x) in inverted_set(W) || error("the homomorphism is not well defined")
    end
    parent_check || error("the images of the variables are not elements of the codomain")
    # Check whether this homomorphism is well defined
    # TODO: Implement that!
    return new{typeof(k), elem_type(k), typeof(R), elem_type(R), typeof(inverted_set(V)), typeof(inverted_set(W))}(V, W, a)
  end
end
  
### additional constructors
function MPolyLocalizedRingHom(
      R::RT,
      W::MPolyLocalizedRing{BRT, BRET, RT, RET, CMST}, 
      a::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, CMST}}
    ) where {BRT, BRET, RT, RET, CMST}
  return MPolyLocalizedRingHom(Localization(units_of(R)), W, a)
end

function MPolyLocalizedRingHom(
      V::MPolyLocalizedRing{BRT, BRET, RT, RET, DMST}, 
      S::RT,
      a::Vector{RET}
    ) where {BRT, BRET, RT, RET, DMST}
  W = Localization(units_of(S))
  return MPolyLocalizedRingHom(V, W, W.(a))
end

### required getter functions
domain(f::MPolyLocalizedRingHom) = f.V
codomain(f::MPolyLocalizedRingHom) = f.W
images(f::MPolyLocalizedRingHom) = f.images

### required functionality
function (f::MPolyLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(p::MPolyLocalizedRingElem{BRT, BRET, RT, RET, DMST}) where {BRT, BRET, RT, RET, DMST, CMST}
  parent(p) == domain(f) || error("the given element does not belong to the domain of the map")
  return evaluate(numerator(p), images(f))//evaluate(denominator(p), images(f))
end

### overwriting of the generic method
function (f::MPolyLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(p::RET) where {BRT, BRET, RT, RET, DMST, CMST}
  parent(p) == base_ring(domain(f)) || error("the given element does not belong to the domain of the map")
  return evaluate(p, images(f))
end

### provide an extra method for elements of the base ring
function (f::MPolyLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(p::BRET) where {BRT, BRET, RT, RET, DMST, CMST}
  parent(p) == coefficient_ring(base_ring(domain(f))) || error("the given element does not belong to the domain of the map")
  return codomain(f)(p)
end

### remove the ambiguity of methods in case the base ring is ℤ
function (f::MPolyLocalizedRingHom)(p::fmpz) 
  return codomain(f)(p)
end

### implementing the Oscar map interface
identity_map(W::T) where {T<:MPolyLocalizedRing} = MPolyLocalizedRingHom(W, W, W.(gens(base_ring(W))))
function compose(
    f::MPolyLocalizedRingHom{BRT, BRET, RT, RET, MST1, MST2}, 
    g::MPolyLocalizedRingHom{BRT, BRET, RT, RET, MST2, MST3}
  ) where {BRT, BRET, RT, RET, MST1, MST2, MST3}
  codomain(f) == domain(g) || error("maps are not compatible")
  return MPolyLocalizedRingHom(domain(f), codomain(g), g.(images(f)))
end

function preimage(f::MPolyLocalizedRingHom, I::MPolyLocalizedIdeal)
  base_ring(I) == codomain(f) || error("the ideal does not belong to the codomain of the map")
  R = base_ring(domain(f))
  error("not implemented")
end
