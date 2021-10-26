export AbsMultSet, AbsPowersOfElement, AbsComplementOfPrimeIdeal
export FmpzComplementOfPrimeIdeal, FmpzPowersOfElement, FmpzComplementOfZeroIdeal
export MPolyComplementOfPrimeIdeal, MPolyComplementOfMaxIdeal


export AbsLocalizedRing
export original_ring, inverted_set
export FmpzLocalizedRing, FmpzLocalizedRingElem
export reduce_fraction

export AbsLocalizedRingElem
export fraction, parent

export AbsLocalRing, AbsMaxLocalRing
export LocalRing, MaxLocalRing, MPolyLocalRing, MPolyMaxLocalRing

export AbsLocalRingIdeal, MPolyLocalizedIdeal, MPolyLocalRingIdeal, MPolyMaxLocalIdeal

export localize_at, ideal

import AbstractAlgebra.Ring

#################################################################################
# General framework for localizations of rings; to be used with affine algebras #
#################################################################################

#################################################################################
# Multiplicatively closed sets of (commutative) rings                           #
#################################################################################
@Markdown.doc """
    AbsMultSet{RingType, RingElemType}

Abstract type for a multiplicatively closed set in a commutative (Noetherian) ring 
R of type `RingType` with elements of type `RingElemType`.
"""
abstract type AbsMultSet{RingType, RingElemType} end

@Markdown.doc """
    in(f::RingElemType, S::AbsMultSet{RingType, RingElemType}) where {RingType, RingElemType}

Returns `true` if `f` belongs to `S`; `false` otherwise.

**Note:** If this routine is not implemented, the function call will default to the 
execution of an error message. 
"""
function Base.in(f::RingElemType, S::AbsMultSet{RingType, RingElemType}) where {RingType, RingElemType}
  error("method not implemented for multiplicatively closed sets of type $(typeof(S))")
end

@Markdown.doc """
    ambient_ring(S::AbsMultSet{RingType, RingElemType}) where {RingType, RingElemType}

Returns the ambient ring `R` for a multiplicatively closed set `S ⊂ R`.
"""
function ambient_ring(S::AbsMultSet{RingType, RingElemType}) where {RingType, RingElemType}
  error("method `ambient_ring` not implemented for multiplicatively closed sets of type $(typeof(S))")
end

@Markdown.doc """
    AbsPowersOfElement{RingType, RingElemType} <: AbsMultSet{RingType, RingElemType}

Abstract type for the multiplicatively closed set ``S = { fᵏ : f ∈ R, k ∈ ℕ₀ } ⊂ R`` 
for some element ``f`` of type `RingElemType` in a ring ``R`` of type `RingType`.
"""
abstract type AbsPowersOfElement{RingType, RingElemType} <: AbsMultSet{RingType, RingElemType} end

@Markdown.doc """
    denominators(P::AbsPowersOfElement{RingType, RingElemType}) where {RingType, RingElemType}

Returns a list of factors ``(a₁,…,aᵣ)`` of the element ``f = a₁⋅…⋅aᵣ`` defining ``P = { fᵏ : f ∈ R, k ∈ ℕ₀ }``.
"""
function denominators(P::AbsPowersOfElement{RingType, RingElemType}) where {RingType, RingElemType}
  error("method `generator(P::AbsPowersOfElement{RingType, RingElemType})` not implemented for `P` of type $(typeof(P))")
end

@Markdown.doc """
    FmpzPowersOfElement

A minimal implementation of `AbsPowersOfElement{RingType, RingElemType}` 
for integers of type `fmpz`.
"""
mutable struct FmpzPowersOfElement <: AbsPowersOfElement{FlintIntegerRing, fmpz}
  d::Vector{fmpz} # a vector of admissible denominators. 

  function FmpzPowersOfElement(denominators::Vector{fmpz})
    return new(denominators)
  end
end

FmpzPowersOfElement(d::fmpz) = FmpzPowersOfElement([d])
FmpzPowersOfElement(d::Int) = FmpzPowersOfElement(ZZ(d))

denominators(S::FmpzPowersOfElement) = S.d::Vector{fmpz}

function Base.in(a::fmpz, S::FmpzPowersOfElement) 
  # check whether ∃ c ∈ ℤ, k ∈ ℕ₀: c ⋅ a = (∏ᵢ dᵢ)ᵏ, where dᵢ are the admissible denominators in S.
  d = prod(denominators(S))
  g = gcd(a, d)
  while(!(g==one(ZZ)))
    a = divexact(a, g)
    g = gcd(a, d)
  end
  return a == one(ZZ)
end



@Markdown.doc """
    AbsComplementOfPrimeIdeal{RingType, IdealType, RingElemType}

Abstract type for the multiplicatively closed sets S = R \\ P for prime ideals P in a commutative ring R. 
This is comprises both the complement of maximal ideals, as well as arbitrary prime ideals. 
In general, one expects different algorithmic backends for each one of the two cases. This will lead to a 
distinction of the associated concrete types.
"""
abstract type AbsComplementOfPrimeIdeal{RingType, IdealType, RingElemType} <:AbsMultSet{RingType, RingElemType} end

function Base.in(f::RingElemType, S::AbsComplementOfPrimeIdeal{RingType,IdealType,  RingElemType}) where {RingType, IdealType, RingElemType}
  error("Method `Base.in` is not implemented for complements of prime ideals of type $(typeof(S))")
end


@Markdown.doc """
    FmpzComplementOfPrimeIdeal

The multiplicatively closed set `S = ℤ ∖ ⟨p⟩` of integers outside a prime ideal `⟨p⟩`.
"""
mutable struct FmpzComplementOfPrimeIdeal <: AbsComplementOfPrimeIdeal{FlintIntegerRing, Hecke.ZZIdl, fmpz}
  # essential fields
  p::fmpz

  function FmpzComplementOfPrimeIdeal(p::fmpz)
    isprime(p) || error("$(p) is not prime")
    return new(p)
  end
end

FmpzComplementOfPrimeIdeal(i::Int) = FmpzComplementOfPrimeIdeal(ZZ(i))

function Base.in(b::fmpz, S::FmpzComplementOfPrimeIdeal)
  return !(divides(b, S.p)[1])
end

@Markdown.doc """
    FmpzComplementOfZeroIdeal <: AbsComplementOfPrimeIdeal{FlintIntegerRing, Hecke.ZZIdl, fmpz}

The complement of the zero ideal in `ℤ`.
"""
mutable struct FmpzComplementOfZeroIdeal <: AbsComplementOfPrimeIdeal{FlintIntegerRing, Hecke.ZZIdl, fmpz}
  function FmpzComplementOfZeroIdeal() 
    return new{}()
  end
end

function Base.in(b::fmpz, S::FmpzComplementOfZeroIdeal) 
  return !(b == zero(ZZ))
end

@Markdown.doc """
    MPolyComplementOfPrimeIdeal{BaseRingType, RingElemType} <: AbsComplementOfPrimeIdeal{MPolyRing{BaseRingType}, MPolyIdeal{RingElemType}, RingElemType}

The complement of a prime ideal `P ⊂ 𝕜[x₁,…,xₙ]` in a multivariate polynomial ring 
with elements of type `RingElemType` over a base ring `𝕜` of type `BaseRingType`.
"""
mutable struct MPolyComplementOfPrimeIdeal{BaseRingType, RingElemType} <: AbsComplementOfPrimeIdeal{MPolyRing{BaseRingType}, MPolyIdeal{RingElemType}, RingElemType}
  # The parent polynomial ring 𝕜[x₁,…,xₙ]
  R::MPolyRing{BaseRingType}
  # The prime ideal whose complement this is
  P::MPolyIdeal{RingElemType}

  function MPolyComplementOfPrimeIdeal(
      P::MPolyIdeal{RingElemType}; 
      check::Bool=false
    ) where {RingElemType}
    R = base_ring(P)
    check && (isprime(P) || error("the ideal $P is not prime"))
    return new{typeof(coefficient_ring(R)), elem_type(R)}(R, P)
  end
end

ambient_ring(
    W::MPolyComplementOfPrimeIdeal{BaseRingType, RingElemType}
  ) where {BaseRingType, RingElemType} = S.R

prime_ideal(
    S::MPolyComplementOfPrimeIdeal{BaseRingType, RingElemType}
  ) where {BaseRingType, RingElemType} = S.P

function Base.in(f::RingElemType, S::MPolyComplementOfPrimeIdeal{BaseRingType, RingElemType}) where {BaseRingType, RingElemType}
  return !(f in prime_ideal(S))
end


@Markdown.doc """
    MPolyComplementOfMaxIdeal{BaseRingType, BaseRingElemType, RingElemType} <: AbsComplementOfPrimeIdeal{MPolyRing{BaseRingType}, MPolyIdeal{RingElemType}, RingElemType}

Complement of a maximal ideal ``𝔪 = ⟨x₁-a₁,…,xₙ-aₙ⟩⊂ 𝕜[x₁,…xₙ]`` with ``aᵢ∈ 𝕜``.
"""
mutable struct MPolyComplementOfMaxIdeal{BaseRingType, BaseRingElemType, RingElemType} <: AbsComplementOfPrimeIdeal{MPolyRing{BaseRingType}, MPolyIdeal{RingElemType}, RingElemType}
  # The parent polynomial ring 𝕜[x₁,…,xₙ]
  R::MPolyRing{BaseRingType}
  # The coordinates aᵢ of the point in 𝕜ⁿ corresponding to the maximal ideal
  a::Vector{BaseRingElemType}

  function MPolyComplementOfMaxIdeal(R::MPolyRing{BaseRingType}, a::Vector{BaseRingElemType}) where {BaseRingType, BaseRingElemType}
    length(a) == length(gens(R)) || error("the number of variables in the ring does not coincide with the number of coordinates")
    n = length(a)
    if n > 0 
      base_ring(R) == parent(a[1]) || error("the coordinates are not elements of the base ring")
    else
      elem_type(base_ring(R)) == BaseRingElemType || error("the type of the coordinates does not match the elem_type of the base ring")
    end
    S = new{BaseRingType, BaseRingElemType, elem_type(R)}(R, a)
    return S
  end
end

function Base.in(f::RingElemType, S::MPolyComplementOfMaxIdeal{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType}
  return !(evaluate(f, S.a) == zero(S.R))
end

function point_coordinates(S::MPolyComplementOfMaxIdeal{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType}
  return S.a
end

#################################################################################
# Localizations of (commutative) rings at multiplicatively closed sets          #
#################################################################################
@Markdown.doc """
    AbsLocalizedRing{RingType, RingElemType, MultSetType}

The localization R[S⁻¹] of a ring R of type `RingType` with elements of type `RingElemType` at a 
multiplicatively closed set S of type `MultSetType`. 

In general, the arithmetic of such a localized ring R[S⁻¹] should be implemented using fractions 
of elements in the original ring R. The methods provided for the multiplicatively closed set S 
can be used to check whether a given denominator is admissible for the specific localization. 

Depending on the actual type of R and S, further functionality can then be provided using 
different Groebner-basis driven backends. 
"""
abstract type AbsLocalizedRing{RingType, RingElemType, MultSetType} <: Ring end

@Markdown.doc """
    original_ring(W::AbsLocalizedRing{RingType, RingElemType, MultSetType}) where {RingType, RingElemType, MultSetType} 

Returns the original ring R for a localized ring of the form W = R[S⁻¹].
"""
function original_ring(W::AbsLocalizedRing{RingType, RingElemType, MultSetType}) where {RingType, RingElemType, MultSetType} 
  error("`original_ring` is not implemented for localized rings of type $(typeof(W))")
end

@Markdown.doc """
    inverted_set(W::AbsLocalizedRing{RingType, RingElemType, MultSetType}) where {RingType, RingElemType, MultSetType}

Returns the set S of at which has been localized for a localized ring W = R[S⁻¹].
"""
function inverted_set(W::AbsLocalizedRing{RingType, RingElemType, MultSetType}) where {RingType, RingElemType, MultSetType}
  error("`inverted_set` is not implemented for localized rings of type $(typeof(W))")
end

@Markdown.doc """
    localize_at(S::AbsMultSet{RingType, RingElemType}) where {RingType, RingElemType}

Returns the localization of the `ambient_ring` of `S` at `S` itself.
"""
function localize_at(S::AbsMultSet{RingType, RingElemType}) where {RingType, RingElemType}
  error("localizations at multiplicatively closed sets of type $(typeof(S)) are not implemented")
end

@Markdown.doc """
    (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(f::AbstractAlgebra.Generic.Frac{RingElemType}) where {RingType, RingElemType, MultSetType} 

Converts a fraction f = a//b to an element of the localized ring W.
"""
function (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(f::AbstractAlgebra.Generic.Frac{RingElemType}) where {RingType, RingElemType, MultSetType} 
  error("conversion for fractions to elements of type $(typeof(W)) is not implemented")
end

@Markdown.doc """
    (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(a::RingElemType) where {RingType, RingElemType, MultSetType} 

Converts an element `a` to an element of `W`.
"""
function (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(a::RingElemType) where {RingType, RingElemType, MultSetType} 
  error("conversion of elements of type $(RingElemType) to elements of $(typeof(W)) is not implemented")
end

@Markdown.doc """
    (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(a::RingElemType, b::RingElemType) where {RingType, RingElemType, MultSetType} 

Converts a pair `(a, b)` to a fraction `a/b` in `W`.
"""
function (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(a::RingElemType, b::RingElemType) where {RingType, RingElemType, MultSetType} 
  error("conversion of pairs `(a, b)` of elements of type $(RingElemType) to fractions `a/b` in a ring of type $(typeof(W)) is not implemented")
end


#################################################################################
# A minimal implementation of the above abstract interface for the ring ℤ       #
#################################################################################
@Markdown.doc """
    FmpzLocalizedRing{MultSetType} <: AbsLocalizedRing{FlintIntegerRing, fmpz, MultSetType} 

A minimal implementation for the localization `ℤ[S⁻¹]` of the ring of integers 
at a multiplicatively closed set `S` of type `MultSetType`.
"""
mutable struct FmpzLocalizedRing{MultSetType} <: AbsLocalizedRing{FlintIntegerRing, fmpz, MultSetType} 
  S::MultSetType # The multiplicatively closed set S ⊂ R whose inverses are added to R

  function FmpzLocalizedRing(S::MultSetType) where {MultSetType}
    # Sanity check whether the multiplicatively closed set S is compatible with the 
    # given rings
    MultSetType <: AbsMultSet{FlintIntegerRing, fmpz} || error(
	"The type of the multiplicatively closed set is not compatible with the type of the ring"
	)
    return new{MultSetType}(S)
  end
end

original_ring(W::FmpzLocalizedRing{MultSetType}) where {MultSetType} = ZZ::FlintIntegerRing

inverted_set(W::FmpzLocalizedRing{MultSetType}) where {MultSetType} = W.S::MultSetType

localize_at(S::FmpzComplementOfPrimeIdeal) = FmpzLocalizedRing(S)

localize_at(S::FmpzComplementOfZeroIdeal) = FmpzLocalizedRing(S)

localize_at(S::FmpzPowersOfElement) = FmpzLocalizedRing(S)


#################################################################################
# Elements of localized rings                                                   #
#################################################################################
@Markdown.doc """
    AbsLocalizedRingElem{RingType, RingElemType, MultSetType}

The abstract type of an element of the localization R[S⁻¹] of a commutative ring 
R of type `RingType` with elements of type `RingElemType` at a multiplicatively 
closed set S of type `MultSetType`.
"""
abstract type AbsLocalizedRingElem{RingType, RingElemType, MultSetType} end

@Markdown.doc """
    numerator(f::T) where {T<:AbsLocalizedRingElem}

Returns the numerator of `f`.
"""
function numerator(f::T) where {T<:AbsLocalizedRingElem}
  error("`numerator` is not implemented for elements of type $(typeof(f))")
end

@Markdown.doc """
    denominator(f::T) where {T<:AbsLocalizedRingElem}

Returns the denominator of `f`.
"""
function denominator(f::T) where {T<:AbsLocalizedRingElem}
  error("`denominator` is not implemented for elements of type $(typeof(f))")
end

@Markdown.doc """
    parent(f::T) where {T<:AbsLocalizedRingElem}

Returns the parent ring R[S⁻¹] of `f`.
"""
function parent(f::T) where {T<:AbsLocalizedRingElem}
  error("`parent` is not implemented for the type $(typeof(f))")
end

# printing
function Base.show(io::IO, f::T) where {T<:AbsLocalizedRingElem}
  print(io, "$(numerator(f))//$(denominator(f))")
end

########################################################################
# Arithmetic; a dumb catchall implmentation, NOT performant!           #
########################################################################

@Markdown.doc """
    function reduce_fraction(a::T) where {T<:AbsLocalizedRingElem}

Reduce the fraction a = p/q. **Warning**: The catchall-implementation does nothing!
"""
function reduce_fraction(a::T) where {T<:AbsLocalizedRingElem}
  return a
end

function +(a::T, b::T) where {T<:AbsLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  if denominator(a) == denominator(b) 
    return reduce_fraction((parent(a))(numerator(a) + numerator(b), denominator(a)))
  end
  return reduce_fraction((parent(a))(numerator(a)*denominator(b) + numerator(b)*denominator(a), denominator(a)*denominator(b)))
end

function -(a::T, b::T) where {T<:AbsLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  if denominator(a) == denominator(b) 
    return reduce_fraction((parent(a))(numerator(a) - numerator(b), denominator(a)))
  end
  return reduce_fraction((parent(a))(numerator(a)*denominator(b) - numerator(b)*denominator(a), denominator(a)*denominator(b)))
end

function *(a::T, b::T) where {T<:AbsLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return reduce_fraction((parent(a))(numerator(a)*numerator(b), denominator(a)*denominator(b)))
end

function Base.:(//)(a::T, b::T) where {T<:AbsLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  numerator(b) in inverted_set(parent(b)) || error("the second argument is not a unit in this local ring")
  return reduce_fraction((parent(a))(numerator(a)*denominator(b), numerator(b)*denominator(a)))
end

function ==(a::T, b::T) where {T<:AbsLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return numerator(a)*denominator(b) == numerator(b)*denominator(a)
end

function ^(a::T, i::Oscar.IntegerUnion) where {T<:AbsLocalizedRingElem}
  return parent(a)(numerator(a)^i, denominator(a)^i)
end

#######################################################################
# A minimal implementation of elements of localizations of ℤ          #
#######################################################################
@Markdown.doc """
    FmpzLocalizedRingElem{MultSetType}

Elements `a/b ∈ ℤ[S⁻¹]` of localizations of the ring of integers 
at a multiplicatively closed set `S` of type `MultSetType`.
"""
mutable struct FmpzLocalizedRingElem{MultSetType} <: AbsLocalizedRingElem{FlintIntegerRing, fmpz, MultSetType}
  numerator::fmpz
  denominator::fmpz
  R::FmpzLocalizedRing{MultSetType} # the parent ring

  function FmpzLocalizedRingElem(R::FmpzLocalizedRing{MultSetType}, a::fmpz, b::fmpz) where {MultSetType}
    # Perform some sanity checks
    b in inverted_set(R) || error("$b does not belong to the units of $R")
    return new{MultSetType}(a, b, R)
  end
end

# The required interface
function parent(f::FmpzLocalizedRingElem{MultSetType}) where {MultSetType} 
  return f.R::FmpzLocalizedRing{MultSetType}
end

function numerator(f::FmpzLocalizedRingElem{MultSetType}) where {MultSetType}
  return f.numerator::fmpz
end

function denominator(f::FmpzLocalizedRingElem{MultSetType}) where {MultSetType}
  return f.denominator::fmpz
end

# Enhancement of the arithmetic
function reduce_fraction(f::FmpzLocalizedRingElem{MultSetType}) where {MultSetType}
  g = gcd(numerator(f), denominator(f))
  return FmpzLocalizedRingElem(parent(f), divexact(numerator(f), g), divexact(denominator(f), g))
end

# Automatic conversion
@Markdown.doc """
    (W::LocalizedRing{RingType, RingElemType, MultSetType})(f::RingElemType) where {RingType, RingElemType, MultSetType}

Part of the minimal interface for localized rings. Suppose W = R[S⁻¹]; then this routine 
returns the conversion of an element f ∈ R to an element f//1 ∈ W.
"""
(W::FmpzLocalizedRing{MultSetType})(f::fmpz) where {MultSetType} = FmpzLocalizedRingElem(W, f, one(ZZ))
(W::FmpzLocalizedRing{MultSetType})(a::fmpz, b::fmpz) where {MultSetType} = FmpzLocalizedRingElem(W, a, b)
(W::FmpzLocalizedRing{MultSetType})(q::fmpq) where {MultSetType} = FmpzLocalizedRingElem(W, numerator(q), denominator(q))
(W::FmpzLocalizedRing{MultSetType})(q::Rational{Int}) where {MultSetType} = FmpzLocalizedRingElem(W, ZZ(numerator(q)), ZZ(denominator(q)))
@Markdown.doc """
    (W::FmpzLocalizedRing{MultSetType})(i::Oscar.IntegerUnion) where {MultSetType} = FmpzLocalizedRingElem(W, ZZ(i), one(ZZ))

Part of the minimal interface for localized rings. This routine returns the conversion of 
an integer i to an element i//1 ∈ W.
"""
(W::FmpzLocalizedRing{MultSetType})(i::Oscar.IntegerUnion) where {MultSetType} = FmpzLocalizedRingElem(W, ZZ(i), one(ZZ))
(W::FmpzLocalizedRing{MultSetType})(a::Oscar.IntegerUnion, b::Oscar.IntegerUnion) where {MultSetType} = FmpzLocalizedRingElem(W, ZZ(a), ZZ(b))

# extension of Oscar's ring interface
one(W::FmpzLocalizedRing{MultSetType}) where {MultSetType} = W(1)
zero(W::FmpzLocalizedRing{MultSetType}) where {MultSetType} = W(0)

elem_type(W::FmpzLocalizedRing{MultSetType}) where {MultSetType} = FmpzLocalizedRingElem{MultSetType}
elem_type(T::Type{FmpzLocalizedRing{MultSetType}}) where {MultSetType} = FmpzLocalizedRingElem{MultSetType}


#################################################################
# Localizations of polynomial rings                             #
#################################################################

@Markdown.doc """
    MPolyLocalizedRing{BaseRingType, RingElemType, MultSetType} <: AbsLocalizedRing{MPolyRing{BaseRingType}, MPolyElem{BaseRingType}}

Localizations ``R[S⁻¹]`` of free polynomial rings ``R = 𝕜[x₁,…,xₙ]`` with elements of type 
`RingElemType` over some base ring ``𝕜`` of type `BaseRingType` and with multiplicatively 
closed set ``S`` of type `MultSetType`.
"""
mutable struct MPolyLocalizedRing{BaseRingType, RingElemType, MultSetType} <: AbsLocalizedRing{MPolyRing{BaseRingType}, MPolyElem{BaseRingType}, MultSetType}
  R::MPolyRing{BaseRingType} # The parent ring which is being localized
  S::MultSetType

  function MPolyLocalizedRing(R::MPolyRing{BaseRingType}, 
      S::MultSetType) where {BaseRingType, MultSetType}
    # TODO: Add some sanity checks here?
    R_loc = new{BaseRingType, elem_type(R), MultSetType}(R,S)
    return R_loc
  end
end

#################################################################
# Honest local rings arising from localizations at prime ideals #
#################################################################

@Markdown.doc """
    AbsLocalRing{RingType, RingElemType, MultSetType}

Abstract type for local rings arising from localizations at prime ideals.
"""
abstract type AbsLocalRing{RingType, RingElemType} <: AbsLocalizedRing{RingType, RingElemType, AbsComplementOfPrimeIdeal{RingType, RingElemType}} end

function original_ring(W::AbsLocalRing{RingType, RingElemType}) where {RingType, RingElemType}
  error("`original_ring` not implemented for local rings of type $(typeof(W))")
end

function inverted_set(W::AbsLocalRing{RingType, RingElemType}) where {RingType, RingElemType}
  error("`inverted_set` not implemented for local rings of type $(typeof(W))")
end

@Markdown.doc """
    AbsLocalRingElem{RingType, RingElemType} <: AbsLocalizedRingElem{RingType, RingElemType, AbsComplementOfPrimeIdeal{RingType, RingElemType}

Abstract type for elements of local rings arising from localizations at prime ideals.
"""
abstract type AbsLocalRingElem{RingType, RingElemType} <: AbsLocalizedRingElem{RingType, RingElemType, AbsComplementOfPrimeIdeal{RingType, RingElemType}} end

############################################################################
# Localizations of polynomial rings over admissible fields at prime ideals #
############################################################################
@Markdown.doc """
    MPolyLocalRing{BaseRingType, RingElemType} <: AbsLocalRing{MPolyRing{BaseRingType}, MPolyElem{BaseRingType}}

The localization of a multivariate polynomial ring R = 𝕜[x₁,…,xₙ] of type `RingType` over a base field 𝕜 of type `BaseRingType` and with elements of type `RingElemType` at a prime ideal P ⊂ R.
"""
mutable struct MPolyLocalRing{BaseRingType, RingElemType} <: AbsLocalRing{MPolyRing{BaseRingType}, MPolyElem{BaseRingType}}
  R::MPolyRing{BaseRingType} # The parent ring which is being localized
  S::MPolyComplementOfPrimeIdeal{BaseRingType, RingElemType} 

  function MPolyLocalRing(R::MPolyRing{BaseRingType}, 
      S::MPolyComplementOfPrimeIdeal{BaseRingType, RingElemType}
    ) where {BaseRingType, RingElemType}
    # TODO: Add some sanity checks here?
    R_loc = new{BaseRingType, RingElemType}(R,S)
    return R_loc
  end
end

function localize_at(S::MPolyComplementOfPrimeIdeal{BaseRingType, RingElemType}) where {BaseRingType, RingElemType}
  return MPolyLocalRing(ambient_ring(S), S)
end

function MPolyLocalRing(R::MPolyRing{BaseRingType}, P::MPolyIdeal{RingElemType}) where {BaseRingType, RingElemType}
  return MPolyLocalRing(R, MPolyComplementOfPrimeIdeal(P))
end

function original_ring(W::MPolyLocalRing{BaseRingType, RingElemType}) where {BaseRingType, RingElemType}
  return W.R
end

function inverted_set(W::MPolyLocalRing{BaseRingType, RingElemType}) where {BaseRingType, RingElemType}
  return W.S
end


########################################################################
# Elements of local polynomial rings                                   #
########################################################################

mutable struct MPolyLocalRingElem{BaseRingType, RingElemType} <: AbsLocalRingElem{MPolyRing{BaseRingType}, MPolyElem{BaseRingType}} 
  frac::AbstractAlgebra.Generic.Frac{RingElemType}
  R_loc::MPolyLocalRing{BaseRingType, RingElemType}

  function MPolyLocalRingElem(f::AbstractAlgebra.Generic.Frac{RingElemType}, R_loc::MPolyLocalRing{BaseRingType, RingElemType}) where {BaseRingType, RingElemType}

    base_ring(parent(f)) == original_ring(R_loc) || error("the numerator and denominator of the given fraction do not belong to the original ring before localization")
    denominator(f) in inverted_set(R_loc) || error("the given denominator is not admissible for this localization")
    return new{BaseRingType, RingElemType}(f, R_loc)
  end
end

fraction(a::MPolyLocalRingElem{BaseRingType, RingElemType}) where {BaseRingType, RingElemType} = a.frac
numerator(a::MPolyLocalRingElem{BaseRingType, RingElemType}) where {BaseRingType, RingElemType} = numerator(a.frac)
denominator(a::MPolyLocalRingElem{BaseRingType, RingElemType}) where {BaseRingType, RingElemType} = denominator(a.frac)


function +(a::MPolyLocalRingElem{BaseRingType, RingElemType}, b::MPolyLocalRingElem{BaseRingType, RingElemType}) where {BaseRingType, RingElemType}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return (parent(a))(fraction(a) + fraction(b))
end

function -(a::MPolyLocalRingElem{BaseRingType, RingElemType}, b::MPolyLocalRingElem{BaseRingType, RingElemType}) where {BaseRingType, RingElemType}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return (parent(a))(fraction(a) - fraction(b))
end

function *(a::MPolyLocalRingElem{BaseRingType, RingElemType}, b::MPolyLocalRingElem{BaseRingType, RingElemType}) where {BaseRingType, RingElemType}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return (parent(a))(fraction(a) * fraction(b))
end

function Base.:(//)(a::MPolyLocalRingElem{BaseRingType, RingElemType}, b::MPolyLocalRingElem{BaseRingType, RingElemType}) where {BaseRingType, RingElemType}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  numerator(fraction(b)) in inverted_set(parent(b)) || error("the second argument is not a unit in this local ring")
  return (parent(a))(fraction(a) // fraction(b))
end

function ==(a::T, b::T) where {T<:MPolyLocalRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return fraction(a) == fraction(b)
end

function ^(a::T, i::Oscar.IntegerUnion) where {T<:MPolyLocalRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return parent(a)(fraction(a)^i)
end


parent(a::MPolyLocalRingElem{BaseRingType, RingElemType}) where {BaseRingType, RingElemType} = a.R_loc

(W::MPolyLocalRing{BaseRingType, RingElemType})(f::RingElemType) where {BaseRingType, RingElemType} = MPolyLocalRingElem((FractionField(original_ring(W)))(f), W)
(W::MPolyLocalRing{BaseRingType, RingElemType})(a::RingElemType, b::RingElemType) where {BaseRingType, RingElemType} = MPolyLocalRingElem(a//b, W)

(W::MPolyLocalRing{BaseRingType, RingElemType})(f::AbstractAlgebra.Generic.Frac{RingElemType}) where {BaseRingType, RingElemType} = MPolyLocalRingElem(f, W)


############################################################################
# Localizations of polynomial rings at certain maximal ideals              #
############################################################################

@Markdown.doc """
    MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType} <: AbsLocalRing{MPolyRing{BaseRingType}, MPolyElem{BaseRingType}}

The localization of a multivariate polynomial ring R = 𝕜[x₁,…,xₙ]
with elements of type `RingElemType` over a base field 𝕜 of type
`BaseRingType` and with elements of type `BaseRingElemType` at a
maximal ideal ``𝔪 = ⟨x₁-a₁,…,xₙ-aₙ⟩`` with coefficients
``aᵢ∈ 𝕜``.
"""
mutable struct MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType} <: AbsLocalRing{MPolyRing{BaseRingType}, MPolyElem{BaseRingType}}
  R::MPolyRing{BaseRingType} # The parent ring which is being localized
  S::MPolyComplementOfMaxIdeal{BaseRingType, BaseRingElemType, RingElemType} 

  function MPolyMaxLocalRing(
      R::MPolyRing{BaseRingType}, 
      S::MPolyComplementOfMaxIdeal{BaseRingType, BaseRingElemType, RingElemType}
    ) where {BaseRingType, BaseRingElemType, RingElemType}
    # TODO: Add some sanity checks here?
    R_loc = new{BaseRingType, BaseRingElemType, RingElemType}(R, S)
    return R_loc
  end
end

function localize_at(S::MPolyComplementOfMaxIdeal{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType}
  return MPolyMaxLocalRing(ambient_ring(S), S)
end

function MPolyMaxLocalRing( R::MPolyRing{BaseRingType}, P::Ideal{RingElemType} ) where {BaseRingType, RingElemType}
  return MPolyLocalRing(R, ComplementOfMaxIdeal(P))
end

function original_ring(W::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType}
  return W.R
end

function inverted_set(W::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType}
  return W.S
end


########################################################################
# Elements of localizations of polynomial rings at maximal ideals      #
########################################################################

mutable struct MPolyMaxLocalRingElem{BaseRingType, BaseRingElemType, RingElemType} <: AbsLocalRingElem{MPolyRing{BaseRingType}, MPolyElem{BaseRingType}} 
  frac::AbstractAlgebra.Generic.Frac{RingElemType}
  R_loc::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}

  function MPolyMaxLocalRingElem(f::AbstractAlgebra.Generic.Frac{RingElemType}, R_loc::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType}
    base_ring(parent(f)) == original_ring(R_loc) || error("the numerator and denominator of the given fraction do not belong to the original ring before localization")
    denominator(f) in inverted_set(R_loc) || error("the given denominator is not admissible for this localization")
    return new{BaseRingType, BaseRingElemType, RingElemType}(f, R_loc)
  end
end

fraction(a::MPolyMaxLocalRingElem{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} = a.frac
numerator(a::MPolyMaxLocalRingElem{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} = numerator(a.frac)
denominator(a::MPolyMaxLocalRingElem{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} = denominator(a.frac)

parent(a::MPolyMaxLocalRingElem{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} = a.R_loc

(W::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType})(f::RingElemType) where {BaseRingType, BaseRingElemType, RingElemType} = MPolyLocalRingElem((FractionField(original_ring(W)))(f), W)

(W::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType})(f::AbstractAlgebra.Generic.Frac{RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} = MPolyLocalRingElem(f, W)


############################################################################
# Ideals in localized rings                                                #
############################################################################

@Markdown.doc """
    AbsLocalizedIdeal{RingType, RingElemType, MultSetType} <: Ideal{RingElemType}

Abstract type for ideals ``IS⁻¹ ⊂ R[S⁻¹]`` in localized rings. In fact, every 
such ideal is of this form for some ideal ``I ⊂ R`` in the original ring. 
"""
abstract type AbsLocalizedRingIdeal{RingType, RingElemType, MultSetType} <: Ideal{RingElemType} end

abstract type AbsLocalRingIdeal{RingType, RingElemType} <: AbsLocalizedRingIdeal{RingType, RingElemType, AbsComplementOfPrimeIdeal{RingType, RingElemType}} end

mutable struct MPolyLocalizedIdeal{BaseRingType, RingElemType, MultSetType} <: AbsLocalizedRingIdeal{MPolyRing{BaseRingType}, RingElemType, MultSetType}
  # to be filled with content
end

mutable struct MPolyLocalIdeal{BaseRingType, RingElemType} <: AbsLocalRingIdeal{MPolyRing{BaseRingType}, RingElemType}
  # to be filled with content
end

@Markdown.doc """
    LocalizedBiPolyArray{LocRingType, RingElemType}

Main workhorse for binding of ideals in localizations ``R[S⁻¹]`` of type `LocRingType` 
of polynomial rings ``R`` with elements of type `RingElemType` to the singular backend. 

This is supposed to be used for all types of localizations, but with different 
orderings for the polynomial ring on the singular side, depending on the 
algorithmic implementation.
"""
mutable struct LocalizedBiPolyArray{LocRingType, RingElemType}
  # The generators on the Oscar side, given simply as fractions
  oscar_gens::Vector{AbstractAlgebra.Generic.Frac{RingElemType}}
  # The numerators of the above fractions as elements in the singular version 
  # of the original ring before localization.
  singular_gens::Singular.sideal
  # The localized ring on the Oscar side.
  oscar_ring::LocRingType
  # A polynomial ring on the singular side, mapping surjectively to the 
  # original ring before localization. 
  singular_ring::Singular.PolyRing
  # The ordering used for the above singular ring.
  ordering::Symbol
  # An optional shift vector applied to the polynomials in Oscar when 
  # translating them to the Singular ring. 
  shift::Vector{RingElemType}
  # Flag for caching
  is_groebner_basis::Bool

  function LocalizedBiPolyArray(oscar_ring::LocRingType, 
      oscar_gens::Vector{AbstractAlgebra.Generic.Frac{RingElemType}};
      ordering=:degrevlex, shift=Vector{RingElemType}()
    ) where {LocRingType <: AbsLocalizedRing, RingElemType}
    BPA = new{LocRingType, RingElemType}()
    # TODO: Add some sanity checks here
    BPA.oscar_ring = oscar_ring
    BPA.oscar_gens = oscar_gens
    BPA.ordering = ordering
    # fill up the shift vector with zeroes if it is not provided in full length
    for i in (length(shift)+1:length(gens(original_ring(oscar_ring))))
      append!(shift, zero(oscar_ring))
    end
    BPA.shift = shift
    BPA.is_groebner_basis=false
    return BPA
  end
  
  function LocalizedBiPolyArray(oscar_ring::LocRingType, 
      singular_gens::Singular.sideal, shift::Vector{RingElemType}
    ) where {LocRingType <: AbsLocalizedRing, RingElemType}
    BPA = new{LocRingType, RingElemType}()
    # TODO: Add some sanity checks here
    BPA.oscar_ring = oscar_ring
    BPA.singular_gens = singular_gens
    BPA.singular_ring = base_ring(singular_gens)
    R = original_ring(oscar_ring)
    @show BPA.singular_ring
    @show typeof(BPA.singular_ring)
    BPA.ordering = Singular.ordering_as_symbol(BPA.singular_ring)
    # fill up the shift vector with zeroes if it is not provided in full length
    for i in (length(shift)+1:length(gens(R)))
	      append!(shift, zero(R))
    end
    BPA.shift = shift
    nvars(R) == length(shift) || error("the number of variables does not coincide with the number of coordinates")
    inv_shift_hom = AlgebraHomomorphism(R, R, [gen(R, i) + shift[i] for i in (1:nvars(R))])
    BPA.oscar_gens = [ y//one(y) for y in (inv_shift_hom.(R.([x for x in gens(singular_gens)])))]
    BPA.is_groebner_basis=false
    return BPA
  end
end

oscar_gens(I::LocalizedBiPolyArray{LocRingType, RingElemType}) where {LocRingType, RingElemType} = I.oscar_gens
oscar_ring(I::LocalizedBiPolyArray{LocRingType, RingElemType}) where {LocRingType, RingElemType} = I.oscar_ring

function singular_gens(lbpa::LocalizedBiPolyArray{LocRingType, RingElemType}) where {LocRingType, RingElemType}
  singular_assure!(lbpa)
  return lbpa.singular_gens
end

function singular_ring(lbpa::LocalizedBiPolyArray{LocRingType, RingElemType}) where {LocRingType, RingElemType} 
  singular_assure!(lbpa)
  return lbpa.singular_ring
end
ordering(lbpa::LocalizedBiPolyArray{LocRingType, RingElemType}) where {LocRingType, RingElemType} = lbpa.ordering
shift(lbpa::LocalizedBiPolyArray{LocRingType, RingElemType}) where {LocRingType, RingElemType} = lbpa.shift


function _singular_ring(oscar_ring::MPolyMaxLocalRing{BaseRingType, RingElemType, MultSetType}; ord::Symbol = :degrevlex) where {BaseRingType, RingElemType, MultSetType}
  return Singular.PolynomialRing(Oscar.singular_ring(base_ring(original_ring(oscar_ring))), 
				 [string(a) for a = Nemo.symbols(original_ring(oscar_ring))], 
				 ordering = ord, 
				 cached = false)[1]
end

function singular_assure!(lbpa::LocalizedBiPolyArray{RingElemType, MultSetType}) where {RingElemType, MultSetType}
  if !isdefined(lbpa, :singular_ring)
    lbpa.singular_ring = _singular_ring(oscar_ring(lbpa), ord=ordering(lbpa))
  end
  if !isdefined(lbpa, :singular_gens)
    shift_hom = hom(original_ring(oscar_ring(lbpa)), original_ring(oscar_ring(lbpa)), 
        [gen(original_ring(oscar_ring(lbpa)), i) - lbpa.shift[i] for i in (1:nvars(original_ring(oscar_ring(lbpa))))])
    lbpa.singular_gens = Singular.Ideal(lbpa.singular_ring,
	[lbpa.singular_ring(shift_hom(numerator(x))) for x in oscar_gens(lbpa)])
  end
end


@Markdown.doc """
    MPolyMaxLocalIdeal{BaseRingType, BaseRingElemType, RingElemType} <: AbsMaxLocalRingIdeal{MPolyRing{BaseRingType}, MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}, RingElemType} 

Ideals in localizations of polynomial rings ``R = 𝕜[x₁,…,xₙ]`` at maximal ideals 
``𝔪 = ⟨x₁-a₁,…,xₙ-aₙ⟩`` with coefficients ``aᵢ∈ 𝕜``.
"""
mutable struct MPolyMaxLocalIdeal{
    BaseRingType, 
    BaseRingElemType, 
    RingElemType
  } <: AbsLocalizedRingIdeal{
    MPolyRing{BaseRingType}, 
    MPolyMaxLocalRingElem{BaseRingType, BaseRingElemType, MPolyElem{BaseRingType}}, 
    MPolyComplementOfMaxIdeal{BaseRingType, BaseRingElemType, RingElemType}
  }
  # the initial set of generators, not to be changed ever!
  gens::LocalizedBiPolyArray{MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}, RingElemType}
  # the ambient ring for this ideal
  R_loc::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}
  
  # Fields for caching
  groebner_basis::LocalizedBiPolyArray{MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}, RingElemType}
  dimension::Int
 

  function MPolyMaxLocalIdeal(R_loc::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}, f::Vector{AbstractAlgebra.Generic.Frac{RingElemType}}) where {BaseRingType, BaseRingElemType, RingElemType}
    R = original_ring(R_loc)
    k = base_ring(R)
    S = inverted_set(R_loc)
    a = point_coordinates(S)
    for x in f
      denominator(x) in S || error("fraction is not an element of the localization")
    end
    I = new{BaseRingType, BaseRingElemType, RingElemType}()
    I.gens = LocalizedBiPolyArray(R_loc, f, ordering=:negdegrevlex, shift=R.(a))
    I.R_loc = R_loc
    return I
  end
end

gens(I::MPolyMaxLocalIdeal{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} = I.gens
ambient_ring(I::MPolyMaxLocalIdeal{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} = I.R_loc

function shift(I::MPolyMaxLocalIdeal{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType}
  lbpa = I.gens
  return shift(lbpa)
end

function dimension(I::MPolyMaxLocalIdeal{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} 
  error("not implemented")
end

function MPolyMaxLocalIdeal(R_loc::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}, I::MPolyIdeal{RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} 
  if length(gens(I))==0 
    return MPolyMaxLocalIdeal(R_loc, Vector{AbstractAlgebra.Generic.Frac{RingElemType}}())
  end
  R = original_ring(R_loc)
  Q = AbstractAlgebra.Generic.FractionField(R)
  base_ring(I) == R || error("ideal does not belong to the original ring before localization")
  return MPolyMaxLocalIdeal(R_loc, Q.(gens(I)))
end

function ideal(R_loc::MPolyMaxLocalRing{BaseRingType, BaseRingElemType, RingElemType}, I::MPolyIdeal{RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType} 
  return MPolyMaxLocalIdeal(R_loc, I)
end


###############################################################################
# Groebner bases                                                              #
###############################################################################

function groebner_assure(I::MPolyMaxLocalIdeal{BaseRingType, BaseRingElemType, RingElemType}) where {BaseRingType, BaseRingElemType, RingElemType}
  if isdefined(I, :groebner_basis) 
    return I.groebner_basis
  end
  gb = Singular.std(singular_gens(gens(I)))
end

function groebner_basis(I::MPolyMaxLocalIdeal{BaseRingType, BaseRingElemType, RingElemType}; ord::Symbol = :negdegrevlex) where {BaseRingType, BaseRingElemType, RingElemType}
  if ord != ordering(gens(I))
    B = LocalizedBiPolyArray(ambient_ring(I), oscar_gens(gens(I)), ordering = ord)
    singular_assure!(B)
    R = singular_ring(B)
    !Oscar.Singular.has_local_ordering(R) && error("The ordering has to be a local ordering.")
    gb = Singular.std(singular_gens(B))
    return LocalizedBiPolyArray(ambient_ring(I), gb, shift(I))
  end
  if !isdefined(I, :groebner_basis)
    B = LocalizedBiPolyArray(ambient_ring(I), oscar_gens(gens(I)); ordering = ord, shift = shift(I))
    singular_assure!(B)
    R = singular_ring(B)
    !Oscar.Singular.has_local_ordering(R) && error("The ordering has to be a local ordering.")
    gb = Singular.std(singular_gens(B))
    I.groebner_basis = LocalizedBiPolyArray(ambient_ring(I), gb, shift(I))
  end
  return oscar_gens(I.groebner_basis)
end

