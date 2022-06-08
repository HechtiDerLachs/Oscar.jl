export MPolyComplementOfPrimeIdeal, MPolyComplementOfKPointIdeal, MPolyPowersOfElement, MPolyProductOfMultSets, MPolyLeadingMonOne
export rand, sets, issubset, units_of, simplify!, is_trivial
import Base: issubset

export MPolyLocalizedRing
export ambient_ring, point_coordinates, inverted_set, denominators, gens

export MPolyLocalizedRingElem
export numerator, denominator, fraction, parent, is_unit, divexact
export reduce_fraction

export MPolyLocalizedIdeal
export gens, base_ring, saturated_ideal, intersect, quotient

export Localization, ideal
export bring_to_common_denominator, write_as_linear_combination

export MPolyLocalizedRingHom
export domain, codomain, images

import AbstractAlgebra: Ring, RingElem

export complement_of_ideal, powers_of_element

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
  #return divides(one(R), o)[1]
  return is_unit(o)
end

### iteration 
Base.iterate(U::MPolyPowersOfElement) = (U.a[1], 1)
Base.iterate(U::MPolyPowersOfElement, a::Tuple{<:MPolyElem, Int}) = (a[2] < length(U.a) ? (U.a[a[2]+1], a[2]+1) : nothing)
Base.iterate(U::MPolyPowersOfElement, i::Int) = (i < length(U.a) ? (U.a[i+1], i+1) : nothing)

is_trivial(U::MPolyPowersOfElement) = (U == units_of(ambient_ring(U)))

### printing
function Base.show(io::IO, S::MPolyPowersOfElement)
  print(io, "powers of ")
  print(io, denominators(S))
end

### generation of random elements 
function rand(S::MPolyPowersOfElement, v1::UnitRange{Int}, v2::UnitRange{Int}, v3::UnitRange{Int})
  return prod([f^(abs(rand(Int))%10) for f in denominators(S)])::elem_type(ambient_ring(S))
end

### simplification. 
# Replaces each element d by its list of square free prime divisors.
function simplify!(S::MPolyPowersOfElement)
  R = ambient_ring(S)
  new_denom = Vector{elem_type(R)}()
  for d in denominators(S)
    for a in factor(d)
      push!(new_denom, a[1])
    end
  end
  S.a = new_denom
  return S
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

The complement of a prime ideal ``P ⊂ 𝕜[x₁,…,xₙ]`` in a multivariate polynomial ring 
with elements of type `RingElemType` over a base ring ``𝕜`` of type `BaseRingType`.
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
    check && (is_prime(P) || error("the ideal $P is not prime"))
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

@doc Markdown.doc"""  
    complement_of_ideal(R::MPolyRing, a::Vector)

Given a polynomial ring ``R``, say ``R = K[x_1,\dots, x_n]``, and given a vector 
``a = (a_1, \dots, a_n)`` of ``n`` elements of ``K``, return the multiplicatively 
closed subset ``R\setminus M``, where ``M`` is the maximal ideal 

$$M = \langle x_1-a_1,\dots, x_n-a_n\rangle \subset R.$$

    complement_of_ideal(P::MPolyIdeal; check::Bool=false)

Given a prime ideal ``P`` of a polynomial ring ``R``, say,
return the multiplicatively closed subset ``R\setminus P.``

!!! note
    If  `check` is set to `true`, the function checks whether ``P`` is indeed a prime ideal. 

    This may take some time.

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> U = complement_of_ideal(R, [0, 0 ,0])
complement of maximal ideal corresponding to point with coordinates fmpq[0, 0, 0]

julia> P = ideal(R, [x])
ideal(x)

julia> U = complement_of_ideal(P)
complement of ideal(x)
```
"""
complement_of_ideal(R::MPolyRing, a::Vector) = MPolyComplementOfKPointIdeal(R, a)
complement_of_ideal(P::MPolyIdeal; check::Bool=false) = MPolyComplementOfPrimeIdeal(P; check)

@doc Markdown.doc"""  
    powers_of_element(f::MPolyElem)

Given an element `f` of a polynomial ring, return the multiplicatively 
closed subset of the polynomial ring which is formed by the powers of `f`.

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> f = x
x

julia> U = powers_of_element(f)
powers of fmpq_mpoly[x]
```
"""
powers_of_element(f::MPolyElem) = MPolyPowersOfElement(f)

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
  print(io, "complement of maximal ideal corresponding to point with coordinates ")
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
getindex(S::MPolyProductOfMultSets, i::Integer) = S.U[i]
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
# Localization associated to a monomial ordering                       #
########################################################################

@Markdown.doc """
    MPolyLeadingMonOne{
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

The set `S = { a in R : leading_monomial(a, ord) = 1 }` for a fixed
monomial ordering `ord`.
"""
mutable struct MPolyLeadingMonOne{
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
  ord::MonomialOrdering

  function MPolyLeadingMonOne(R::RingType, ord::MonomialOrdering) where {RingType <: MPolyRing}
    @assert R === ord.R "Ordering does not belong to the given ring"
    k = coefficient_ring(R)
    return new{typeof(k), elem_type(k), RingType, elem_type(R)}(R, ord)
  end
end

### required getter functions
ambient_ring(S::MPolyLeadingMonOne) = S.R

### additional constructors
MPolyLeadingMonOne(ord::MonomialOrdering) = MPolyLeadingMonOne(ord.R, ord)

ordering(S::MPolyLeadingMonOne) = S.ord

### required functionality
function Base.in(
    f::RingElemType,
    S::MPolyLeadingMonOne{BaseRingType, BaseRingElemType, RingType, RingElemType}
  ) where {BaseRingType, BaseRingElemType, RingType, RingElemType}
  R = parent(f)
  R == ambient_ring(S) || return false
  if iszero(f)
    return false
  end
  return isone(leading_monomial(f, ordering(S)))
end

### printing
function Base.show(io::IO, S::MPolyLeadingMonOne)
  print(io, "elements of ")
  print(io, ambient_ring(S))
  print(io, " with leading monomial 1 w.r.t. ")
  print(io, ordering(S))
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

function issubset(
    T::MPolyProductOfMultSets{BRT, BRET, RT, RET},
    U::MPolyProductOfMultSets{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  for V in sets(T)
    issubset(V, U) || return false
  end
  return true
end

function issubset(
    T::MPolyProductOfMultSets{BRT, BRET, RT, RET},
    U::AbsMPolyMultSet{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  for V in sets(T)
    issubset(V, U) || return false
  end
  return true
end

function issubset(
    T::AbsMPolyMultSet{BRT, BRET, RT, RET},
    U::MPolyProductOfMultSets{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  for V in sets(U)
    issubset(T, V) && return true
  end
  error("containment can not be checked")
end

function issubset(
    T::MPolyPowersOfElement{BRT, BRET, RT, RET},
    U::MPolyProductOfMultSets{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  for d in denominators(T)
    d in U || return false
  end
  return true
end

### intersections ######################################################
function intersect(T::AbsMPolyMultSet, U::AbsMPolyMultSet) 
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

@Markdown.doc """
    product(T::AbsMPolyMultSet, U::AbsMPolyMultSet)

Return the product of the multiplicative subsets `T` and `U`. 

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> T = complement_of_ideal(R, [0, 0 ,0])
complement of maximal ideal corresponding to point with coordinates fmpq[0, 0, 0]

julia> f = x
x

julia> U = powers_of_element(f)
powers of fmpq_mpoly[x]

julia> S = product(T, U)
product of the multiplicative sets [complement of maximal ideal corresponding to point with coordinates fmpq[0, 0, 0], powers of fmpq_mpoly[x]]
```
"""
function product(T::AbsMPolyMultSet, U::AbsMPolyMultSet)
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  issubset(T, U) && return U
  issubset(U, T) && return T
  return MPolyProductOfMultSets(R, [T, U])
end

function product(T::MST, U::MST) where {MST<:MPolyProductOfMultSets} 
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  new_sets = Vector()
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
  return MPolyProductOfMultSets(R, [x for x in new_sets])
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

function product(
    T::MPolyPowersOfElement{BRT, BRET, RT, RET},
    U::MPolyProductOfMultSets{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET}
  R = ambient_ring(T)
  R == ambient_ring(U) || error("multiplicative sets do not belong to the same ring")
  keep_denom = Vector{RET}()
  for a in denominators(T)
    a in U || (push!(keep_denom, a))
  end
  length(keep_denom) == 0 && return U
  return MPolyProductOfMultSets(vcat(sets(U), MPolyPowersOfElement(keep_denom)))
end
function product(
    U::MPolyProductOfMultSets{BRT, BRET, RT, RET},
    T::MPolyPowersOfElement{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET} 
  return T*U
end

### Preimages of multiplicative sets.
# In general for a ring homomorphism f : R → S and a multiplicative 
# set U ⊂ S the preimage V = f⁻¹(U) is a multiplicative set in R. 
# Membership in V can easily be tested, but introducing a new type 
# for preimages makes it necessary to extend all dispatch routines. 
# It is not clear what is the best strategy for all this. 

function preimage(f::Oscar.AffAlgHom, U::MST) where {MST<:AbsMPolyMultSet}
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
@attributes mutable struct MPolyLocalizedRing{
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
@Markdown.doc """
    Localization(U::AbsMPolyMultSet)

Given a multiplicatively closed subset of a multivariate polynomial ring ``R``, say, 
return the localization of ``R`` at ``U`` together with the localization map 
from ``R`` to ``R[U^{-1}]``.

    Localization(R::MPolyRing, U::AbsMPolyMultSet)

Given a multiplicatively closed subset ``U`` of ``R``, proceed as above.

# Examples
```jldoctest
julia> R, (x, y, z) = PolynomialRing(QQ, ["x", "y", "z"])
(Multivariate Polynomial Ring in x, y, z over Rational Field, fmpq_mpoly[x, y, z])

julia> P = ideal(R, [x])
ideal(x)

julia> U = complement_of_ideal(P)
complement of ideal(x)

julia> Rloc, iota = Localization(R, U);

julia> Rloc
localization of Multivariate Polynomial Ring in x, y, z over Rational Field at the complement of ideal(x)

julia> iota
Map with following data
Domain:
=======
Multivariate Polynomial Ring in x, y, z over Rational Field
Codomain:
=========
localization of Multivariate Polynomial Ring in x, y, z over Rational Field at the complement of ideal(x)
```
"""
function Localization(S::AbsMPolyMultSet)
    R = ambient_ring(S)
    Rloc = MPolyLocalizedRing(R, S)
    #iota = MapFromFunc(x -> Rloc(x), R, Rloc)
    iota = hom(R, Rloc, Rloc.(gens(R)))
    return Rloc, iota
end

function Localization(R::MPolyRing, ord::MonomialOrdering)
  @assert R === ord.R
  return Localization(MPolyLeadingMonOne(ord))
end

### Successive localizations are handled by the dispatch for products
function Localization(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST}, 
    S::AbsMPolyMultSet{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET, MST}
  issubset(S, inverted_set(W)) && return W
  U = S*inverted_set(W)
  L, _ = Localization(U)
  #return L, MapFromFunc((x->(L(numerator(x), denominator(x), check=false))), W, L)
  return L, MPolyLocalizedRingHom(W, L, hom(base_ring(W), L, L.(gens(base_ring(W)))), check=false)
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
  L = MPolyLocalizedRing(R, MPolyPowersOfElement(R, vcat(g, divexact(f, h))))
  return L, MPolyLocalizedRingHom(W, L, hom(base_ring(W), L, L.(gens(base_ring(W)))), check=false)
  #return L, MapFromFunc((x->L(numerator(x), denominator(x), check=false)), W, L)
end

function Localization(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MPolyPowersOfElement{BRT, BRET, RT, RET}}, 
    v::Vector{RET}
  ) where {BRT, BRET, RT, RET}
  V = W
  for f in v
    V = Localization(V, f)
  end
  return V, MPolyLocalizedRingHom(W, V, hom(base_ring(W), V, V.(gens(base_ring(W)))), check=false)
  #return V, MapFromFunc((x->V(numerator(x), denominator(x), check=false)), W, V)
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
    if check && !iszero(f) && !is_unit(denominator(f))
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
function (W::MPolyLocalizedRing{
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    MultSetType
  })(f::RingElemType; check::Bool=true) where {
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType<:RingElem, 
    MultSetType
  } 
  return MPolyLocalizedRingElem(W, FractionField(base_ring(W))(f), check=false)
end

(W::MPolyLocalizedRing{
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    MultSetType
  })(f::BaseRingElemType) where {
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    MultSetType
  } = MPolyLocalizedRingElem(W, FractionField(base_ring(W))(base_ring(W)(f)), check=false)

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
  return (parent(b))(a*numerator(b), denominator(b), check=false)
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

is_unit(f::MPolyLocalizedRingElem) = numerator(f) in inverted_set(parent(f))


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
(W::MPolyLocalizedRing)(a::Integer) = W(base_ring(W)(a), check=false)
(W::MPolyLocalizedRing)(a::Int64) = W(base_ring(W)(a), check=false)
(W::MPolyLocalizedRing)(a::fmpz) = W(base_ring(W)(a), check=false)

is_domain_type(T::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}) where {BRT, BRET, RT, RET, MST} = true 
is_exact_type(T::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}) where {BRT, BRET, RT, RET, MST} = true

### promotion rules
AbstractAlgebra.promote_rule(::Type{MPolyLocalizedRingElem{RT, RET, MST}}, ::Type{MPolyLocalizedRingElem{RT, RET, MST}}) where {RT<:Ring, RET<:RingElement, MST} = MPolyLocalizedRingElem{RT, RET, MST}

function AbstractAlgebra.promote_rule(::Type{MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}}, ::Type{T}) where {BRT<:Ring, BRET<:RingElement, RT<:Ring, RET<:RingElement, MST, T<:RingElement} 
  AbstractAlgebra.promote_rule(RET, T) == RET && return MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}
  return AbstractAlgebra.promote_rule(BRET, T) == BRET ? MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST} : Union{}
end

@attr function base_ring_shifts(L::MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}) 
  a = point_coordinates(inverted_set(L))
  R = base_ring(L)
  shift = hom(R, R, gens(R)+R.(a))
  back_shift = hom(R, R, gens(R)-R.(a))
  return shift, back_shift
end

@Markdown.doc """
    bring_to_common_denominator(f::Vector{T}) where {T<:MPolyLocalizedRingElem}

Given a vector of fractions [a₁//b₁,…,aₙ//bₙ] return a pair 
(d, λ) consisting of a common denominator d and a vector 
λ = [λ₁,…,λₙ] such that aᵢ//bᵢ = λᵢ⋅aᵢ//d
"""
function bring_to_common_denominator(f::Vector{T}) where {T<:MPolyLocalizedRingElem}
  length(f) == 0 && error("need at least one argument to determine the return type")
  R = base_ring(parent(f[1]))
  for a in f
    R == base_ring(parent(a)) || error("elements do not belong to the same ring")
  end
  d = one(R)
  a = Vector{elem_type(R)}()
  for den in denominator.(f)
    b = gcd(d, den)
    c = divexact(den, b)
    e = divexact(d, b)
    d = d*c
    a = [c*k for k in a]
    push!(a, e)
  end
  return d, a
end

write_as_linear_combination(f::MPolyLocalizedRingElem, g::Vector) = write_as_linear_combination(f, parent(f).(g))

# return the localized ring as a quotient of a polynomial ring using Rabinowitsch's trick.
@Markdown.doc """
    as_affine_algebra(
      L::MPolyLocalizedRing{BRT, BRET, RT, RET, 
      MPolyPowersOfElement{BRT, BRET, RT, RET}}; 
      inverse_name::String="θ"
    ) where {BRT, BRET, RT, RET}

For a localized polynomial ring ``L = 𝕜[x₁,…,xₙ][f⁻¹]`` this returns a 
quintuple ``(A, I, d, ϕ, θ)`` consisting of 

  * an `AffineAlgebra` ``A = 𝕜[x₁,…,xₙ,θ]/⟨1 - θ⋅d⟩`` isomorphic to ``L``
  * the ideal ``⟨1 - θ⋅d⟩``
  * an element ``d ∈ 𝕜[x₁,…,xₙ]`` at which has been localized
  * the natural inclusion ``ϕ : 𝕜[x₁,…,xₙ] ↪ A``
  * the localization variable ``θ`` corresponding to ``d⁻¹``.
"""
function as_affine_algebra(
    L::MPolyLocalizedRing{BRT, BRET, RT, RET, 
			     MPolyPowersOfElement{BRT, BRET, RT, RET}}; 
    inverse_name::String="θ"
  ) where {BRT, BRET, RT, RET}
  R = base_ring(L)
  A, phi, t = _add_variables_first(R, [inverse_name])
  theta = t[1]
  f = prod(denominators(inverted_set(L)))
  I = ideal(A, [one(A)-theta*phi(f)])
  return A, I, f, phi, theta
end


########################################################################
# Homomorphisms of localized polynomial rings                          #
########################################################################

mutable struct MPolyLocalizedRingHom{
                                     DomainType<:MPolyLocalizedRing, 
                                     CodomainType<:Ring, 
                                     RestrictedMapType<:Map
                                    } <: AbsLocalizedRingHom{
                                                             DomainType, 
                                                             CodomainType, 
                                                             RestrictedMapType
                                                            }
  # the domain of definition
  W::DomainType

  ### the codomain
  # Why do we need to store the codomain explicitly and not extract it from 
  # the restricted map? 
  # Because the restricted map res probably takes values in a strictly 
  # smaller or even completely different ring than S. If C is the codomain 
  # of res, then we impliticly assume (and check) that coercion from elements 
  # of C to S is possible. This is strictly weaker than requiring res to implement 
  # the full map interface. In that case, one would -- for example -- need to 
  # implement a new type just for the inclusion map R → R[U⁻¹] of a ring into 
  # its localization.
  S::CodomainType

  # the restriction of the map to the base_ring of the domain
  res::RestrictedMapType

  function MPolyLocalizedRingHom(
      W::DomainType,
      S::CodomainType,
      res::RestrictedMapType;
      check::Bool=true
    ) where {DomainType<:MPolyLocalizedRing, CodomainType<:Ring, RestrictedMapType<:Map}
    R = base_ring(W)
    U = inverted_set(W)
    domain(res) === R || error("the domain of the restricted map does not coincide with the base ring of the localization")
    for f in U
      is_unit(S(res(f))) || error("image of $f is not a unit in the codomain")
    end
    return new{DomainType, CodomainType, RestrictedMapType}(W, S, res) 
  end
end
  
### additional constructors
function MPolyLocalizedRingHom(
      R::MPolyRing,
      S::Ring,
      a::Vector{RingElemType}
  ) where {RingElemType<:RingElem}
  res = hom(R, S, a)
  W, _ = Localization(units_of(R))
  return MPolyLocalizedRingHom(W, S, res)
end

function MPolyLocalizedRingHom(
      W::MPolyLocalizedRing,
      S::Ring,
      a::Vector{RingElemType}
  ) where {RingElemType<:RingElem}
  R = base_ring(W)
  res = hom(R, S, a)
  return MPolyLocalizedRingHom(W, S, res)
end

@doc Markdown.doc"""
    hom(Rloc::MPolyLocalizedRing, S::Ring, phi::Map)

Given a localized ring `Rloc`of type `MPolyLocalizedRing`, say `Rloc` is the localization 
of the multivariate polynomial ring `R` at the multiplicatively closed subset `U` of `R`, and 
given a homomorphism `phi` from `R` to `S` sending elements of `U` to units in `S`, return 
the homomorphism from `Rloc` to `S` whose composition with the localization map is `phi`.

    hom(Rloc::MPolyLocalizedRing, S::Ring, images::Vector)

Given a localized ring `Rloc` with notation as above, and given a vector `images` of `nvars` elements
of `S`, let `phi` be the homomorphism from `R` to `S` which is defined by the entries of 
`images`, and proceed as above.

!!! note
    The extra condition on `phi` is not checked by the function.

# Examples
```jldoctest
julia> R, (x,) = PolynomialRing(QQ, ["x"])
(Multivariate Polynomial Ring in x over Rational Field, fmpq_mpoly[x])

julia> U = powers_of_element(x)
powers of fmpq_mpoly[x]

julia> Rloc, iota = Localization(R, U);

julia> Sprime, (X, Y) = PolynomialRing(QQ, ["X", "Y"])
(Multivariate Polynomial Ring in X, Y over Rational Field, fmpq_mpoly[X, Y])

julia> S, p = quo(Sprime, ideal(Sprime, [X*Y-1]))
(Quotient of Multivariate Polynomial Ring in X, Y over Rational Field by ideal(X*Y - 1), Map from
Multivariate Polynomial Ring in X, Y over Rational Field to Quotient of Multivariate Polynomial Ring in X, Y over Rational Field by ideal(X*Y - 1) defined by a julia-function with inverse)

julia> PHI = hom(Rloc, S, [p(X)])
morphism from the localized ring localization of Multivariate Polynomial Ring in x over Rational Field at the powers of fmpq_mpoly[x] to Quotient of Multivariate Polynomial Ring in X, Y over Rational Field by ideal(X*Y - 1)

julia> PHI(iota(x))
X

julia> is_unit(PHI(iota(x)))
true
```
"""
hom(W::MPolyLocalizedRing, S::Ring, res::Map) = MPolyLocalizedRingHom(W, S, res)
hom(W::MPolyLocalizedRing, S::Ring, a::Vector{RET}) where {RET<:RingElem} = MPolyLocalizedRingHom(W, S, a)

### required getter functions
domain(PHI::MPolyLocalizedRingHom) = PHI.W
codomain(PHI::MPolyLocalizedRingHom) = PHI.S

@doc Markdown.doc"""
    restricted_map(PHI::MPolyLocalizedRingHom)

Given a ring homomorphism `PHI` from a localized multivariate polynomial ring, 
return the composition of `PHI` with the localization map.

# Examples
```jldoctest
julia> R, (x,) = PolynomialRing(QQ, ["x"])
(Multivariate Polynomial Ring in x over Rational Field, fmpq_mpoly[x])

julia> U = powers_of_element(x)
powers of fmpq_mpoly[x]

julia> Rloc, iota = Localization(R, U);

julia> Sprime, (X, Y) = PolynomialRing(QQ, ["X", "Y"])
(Multivariate Polynomial Ring in X, Y over Rational Field, fmpq_mpoly[X, Y])

julia> S, p = quo(Sprime, ideal(Sprime, [X*Y-1]))
(Quotient of Multivariate Polynomial Ring in X, Y over Rational Field by ideal(X*Y - 1), Map from
Multivariate Polynomial Ring in X, Y over Rational Field to Quotient of Multivariate Polynomial Ring in X, Y over Rational Field by ideal(X*Y - 1) defined by a julia-function with inverse)

julia> PHI = hom(Rloc, S, [p(X)])
morphism from the localized ring localization of Multivariate Polynomial Ring in x over Rational Field at the powers of fmpq_mpoly[x] to Quotient of Multivariate Polynomial Ring in X, Y over Rational Field by ideal(X*Y - 1)

julia> phi = restricted_map(PHI)
Map with following data
Domain:
=======
Multivariate Polynomial Ring in x over Rational Field
Codomain:
=========
Quotient of Multivariate Polynomial Ring in X, Y over Rational Field by ideal(X*Y - 1)
```
"""
restricted_map(PHI::MPolyLocalizedRingHom) = PHI.res

### implementing the Oscar map interface
function identity_map(W::T) where {T<:MPolyLocalizedRing} 
  MPolyLocalizedRingHom(W, W, identity_map(base_ring(W)))
end

function compose(
    f::MPolyLocalizedRingHom, 
    g::MPolyLocalizedRingHom
  )
  codomain(f) === domain(g) || error("maps are not compatible")
  return MPolyLocalizedRingHom(domain(f), codomain(g), compose(restricted_map(f), g))
end

(f::MPolyLocalizedRingHom)(I::Ideal) = ideal(codomain(f), domain(f).(gens(I)))

function ==(f::MPolyLocalizedRingHom, g::MPolyLocalizedRingHom) 
  domain(f) === domain(g) || return false
  codomain(f) === codomain(g) || return false
  for x in gens(base_ring(domain(f)))
    f(x) == g(x) || return false
  end
  return true
end

function divides(a::MPolyLocalizedRingElem, b::MPolyLocalizedRingElem)
  W = parent(a)
  W == parent(b) || error("elements do not belong to the same ring")
  F = FreeMod(W, 1)
  A = MatrixSpace(W, 1, 1)([b])
  M, _ = sub(F, A)
  represents_element(a*F[1], M) || return (false, zero(W))
  x = coordinates(a*F[1], M)
  return true, W(x[1])
end
