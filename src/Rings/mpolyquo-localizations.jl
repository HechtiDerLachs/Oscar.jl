import AbstractAlgebra: Ring, RingElem, Generic.Frac
import Base: issubset

export MPolyQuoLocalizedRing
export parent, inverted_set, base_ring, quotient_ring, localized_ring, modulus, localized_modulus, gens
export Localization

export MPolyQuoLocalizedRingElem
export numerator, denominator, parent, lift, isunit

export MPolyQuoLocalizedRingHom
export domain, codomain, images
export helper_ring, helper_images, minimal_denominators, helper_eta, helper_kappa, common_denominator, helper_ideal

export is_isomorphism, inverse

########################################################################
# Localizations of polynomial algebras                                 #
########################################################################
# 
# Let R = 𝕜[x₁,…,xₘ] be a polynomial ring, I ⊂ R some ideal 
# and P = R/I its quotient. Then P is naturally an R-module 
# and localization of P as a ring coincides with localization 
# as an R-module in the sense that for every multiplicative 
# set T ⊂ R there is a commutative diagram 
#
#         R    →  P = R/I
#         ↓       ↓
#   W = R[T⁻¹] → P[T⁻¹].
#
# Observe that, moreover, for every multiplicative set 
# T' ⊂ P the preimage T of T' in R is also a multiplicative set. 
#
# We may therefore treat localizations of polynomial algebras 
# as localizations of modules over free polynomial rings and 
# exclusively use the types of multiplicative sets which are 
# available for the latter.
#
# Note the following differences compared to the standard usage 
# of the localization interface:
#
#  * The `base_ring` returns neither P, nor W, but R.
#  * The `BaseRingType` is the type of R and similar for 
#    the other ring-based type parameters.
#
# This is to make the data structure most accessible for 
# the computational backends.
#
#  * The type returned by `numerator` and `denominator` 
#    on an element of type `MPolyQuoLocalizedRingElem` is 
#    not `RingElemType`, but the type of `P`. 
#
# This is to comply with the purely mathematical viewpoint
# where elements of localized rings are fractions of 
# residue classes rather than residue classes of fractions. 
#

mutable struct MPolyQuoLocalizedRing{
    BaseRingType,
    BaseRingElemType,
    RingType,
    RingElemType,
    MultSetType <: AbsMultSet{RingType, RingElemType}
  } <: AbsLocalizedRing{
    RingType,
    RingElemType,
    MultSetType
  }
  R::RingType
  I::MPolyIdeal{RingElemType}
  S::MultSetType
  Q::MPolyQuo{RingElemType}
  W::MPolyLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}

  # fields for caching
  J::MPolyLocalizedIdeal{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}

  function MPolyQuoLocalizedRing(
      R::RingType,
      I::MPolyIdeal{RingElemType},
      S::MultSetType,
      Q::MPolyQuo{RingElemType},
      W::MPolyLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}
    ) where {
      BaseRingType<:Ring, 
      BaseRingElemType<:RingElem, 
      RingType<:MPolyRing, 
      RingElemType<:MPolyElem, 
      MultSetType<:AbsMultSet{RingType, RingElemType}
    }
    base_ring(I) == R || error("Ideal does not belong to the ring")
    base_ring(Q) == R || error("The quotient ring does not come from the given ring")
    # The following line throws obscure error messages that might yield a bug for MPolyIdeals.
    # So it's commented out for now.
    #modulus(Q) == I || error("the modulus of the quotient ring does not coincide with the ideal")
    S == inverted_set(W) || error("the multiplicative set does not coincide with the inverted set of the localized ring")
    base_ring(W) == R || error("the localization does not come from the given ring")
    ambient_ring(S) == R || error("Multiplicative set does not belong to the ring")
    k = coefficient_ring(R)
    L = new{typeof(k), elem_type(k), typeof(R), RingElemType, MultSetType}(R, I, S, Q, W)
    L.J = W(I)
    return L
  end
end

### required getter functions 
base_ring(L::MPolyQuoLocalizedRing) = L.R
inverted_set(L::MPolyQuoLocalizedRing) = L.S

### additional getter functions
modulus(L::MPolyQuoLocalizedRing) = L.I
localized_modulus(L::MPolyQuoLocalizedRing) = L.J
quotient_ring(L::MPolyQuoLocalizedRing) = L.Q
localized_ring(L::MPolyQuoLocalizedRing) = L.W
gens(L::MPolyQuoLocalizedRing) = L.(gens(base_ring(L)))

### printing
function Base.show(io::IO, L::MPolyQuoLocalizedRing)
  print(io, "Localization of $(quotient_ring(L)) at the multiplicative set $(inverted_set(L))")
end

### additional constructors
function quo(
    W::MPolyLocalizedRing{BRT, BRET, RT, RET, MST},
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MST}
  ) where {BRT, BRET, RT, RET, MST}
  R = base_ring(W)
  S = inverted_set(W)
  lbpa = groebner_basis(I) # In particular, this saturates the ideal
  J = ideal(R, numerator.(oscar_gens(lbpa))) # the preimage of I in R
  return MPolyQuoLocalizedRing(R, J, S, quo(R, J)[1], W)
end

function quo(
    L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, MST},
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, MST}
  ) where {BRT, BRET, RT, RET, MST}
  R = base_ring(L)
  S = inverted_set(L)
  lbpa = groebner_basis(I) # In particular, this saturates the ideal
  J = ideal(R, numerator.(oscar_gens(lbpa))) # the preimage of I in R
  return MPolyQuoLocalizedRing(R, J, S, quo(R, J)[1], localized_ring(L))
end

function quo(
    L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, MST},
    J::MPolyIdeal{RET}
  ) where {BRT, BRET, RT, RET, MST}
  R = base_ring(L)
  S = inverted_set(L)
  W = localized_ring(L) 
  J = J + modulus(L)
  return MPolyQuoLocalizedRing(R, J, S, quo(R, J)[1], W)
end

function Localization(Q::MPolyQuo{RET}, S::MultSetType) where {RET <: RingElem, MultSetType <: AbsMultSet}
  return MPolyQuoLocalizedRing(base_ring(Q), modulus(Q), S, Q, Localization(S))
end

function Localization(
    L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, MST}, 
    S::AbsMPolyMultSet{BRT, BRET, RT, RET}
  ) where {BRT, BRET, RT, RET, MST}
  ambient_ring(S) == base_ring(L) || error("multiplicative set does not belong to the correct ring")
  issubset(S, inverted_set(L)) && return L
  U = inverted_set(L)*S
  return MPolyQuoLocalizedRing(base_ring(L), modulus(L), U, quotient_ring(L), Localization(U))
end

function MPolyQuoLocalizedRing(R::RT, I::Ideal{RET}, T::MultSetType) where {RT<:MPolyRing, RET<:MPolyElem, MultSetType<:AbsMultSet} 
  return MPolyQuoLocalizedRing(R, I, T, quo(R, I)[1], Localization(T))
end

function MPolyQuoLocalizedRing(R::RT) where {RT<:MPolyRing} 
  I = ideal(R, zero(R))
  Q, _ = quo(R, I)
  U = units_of(R)
  W = Localization(U)
  return MPolyQuoLocalizedRing(R, I, U, Q, W)
end

function MPolyQuoLocalizedRing(Q::RT) where {RT<:MPolyQuo}
  R = base_ring(Q)
  I = modulus(Q)
  U = units_of(R)
  W = Localization(U)
  return MPolyQuoLocalizedRing(R, I, U, Q, W)
end

function MPolyQuoLocalizedRing(W::MPolyLocalizedRing)
  R = base_ring(W)
  I = ideal(R, zero(R))
  Q, _ = quo(R, I)
  U = inverted_set(W)
  return MPolyQuoLocalizedRing(R, I, U, Q, W)
end


########################################################################
# Elements of localizations of polynomial algebras                     #
########################################################################

mutable struct MPolyQuoLocalizedRingElem{
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

  # the parent ring
  L::MPolyQuoLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}
  # representatives of numerator and denominator
  numerator::RingElemType
  denominator::RingElemType

  function MPolyQuoLocalizedRingElem(
      L::MPolyQuoLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}, 
      a::RingElemType,
      b::RingElemType
    ) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}

    S = inverted_set(L)
    parent(a) == parent(b) == base_ring(L) || error("elements do not belong to the correct ring")
    b in inverted_set(L) || error("the given denominator is not admissible for this localization")
    return new{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}(L, a, b)
  end
end

### required getter functions 
parent(a::MPolyQuoLocalizedRingElem) = a.L
numerator(a::MPolyQuoLocalizedRingElem) = quotient_ring(parent(a))(a.numerator) 
denominator(a::MPolyQuoLocalizedRingElem) = quotient_ring(parent(a))(a.denominator) 

### additional getter functions
quotient_ring(a::MPolyQuoLocalizedRingElem) = quotient_ring(parent(a))
localized_ring(a::MPolyQuoLocalizedRingElem) = localized_ring(parent(a))
lifted_numerator(a::MPolyQuoLocalizedRingElem) = a.numerator
lifted_denominator(a::MPolyQuoLocalizedRingElem) = a.denominator

### required conversions
(L::MPolyQuoLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType})(f::RingElemType) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyQuoLocalizedRingElem(L, f, one(f))
(L::MPolyQuoLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType})(a::RingElemType, b::RingElemType) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyQuoLocalizedRingElem(L, a, b)

### additional conversions
function (L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, MST})(f::Frac{RET}) where {BRT, BRET, RT, RET, MST}
  R = base_ring(L)
  return L(R(numerator(f)), R(denominator(f)))
end

function (L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, MST})(f::MPolyLocalizedRingElem{BRT, BRET, RT, RET, MST}) where {BRT, BRET, RT, RET, MST}
  parent(f) == localized_ring(L) || error("the given element does not belong to the correct localization")
  lbpa = groebner_basis(localized_modulus(L))
  f = reduce(f, lbpa)
  return MPolyQuoLocalizedRingElem(L, numerator(f), denominator(f))
end

function (L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, MST})(f::MPolyQuoElem{RET}) where {BRT, BRET, RT, RET, MST} 
  parent(f) == quotient_ring(L) || error("the given element does not belong to the correct ring") 
  return L(lift(f))
end

### additional functionality
lift(f::MPolyQuoLocalizedRingElem) = localized_ring(f)(lifted_numerator(f), lifted_denominator(f))

isunit(f::MPolyQuoLocalizedRingElem) = one(localized_ring(parent(f))) in localized_modulus(parent(f)) + ideal(localized_ring(parent(f)), lift(f))

function isunit(L::MPolyQuoLocalizedRing, f::MPolyLocalizedRingElem) 
  parent(f) == localized_ring(L) || error("element does not belong to the correct ring")
  one(localized_ring(L)) in localized_modulus(L) + ideal(localized_ring(L), f)
end

function isunit(L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, MST}, f::RET) where {BRT, BRET, RT, RET, MST}
  parent(f) == base_ring(L) || error("element does not belong to the correct ring")
  one(localized_ring(L)) in localized_modulus(L) + ideal(localized_ring(L), localized_ring(L)(f))
end

function isunit(L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, MST}, f::MPolyQuoElem{RET}) where {BRT, BRET, RT, RET, MST}
  parent(f) == quotient_ring(L) || error("element does not belong to the correct ring")
  one(localized_ring(L)) in localized_modulus(L) + ideal(localized_ring(L), localized_ring(L)(f))
end


### arithmetic #########################################################
function +(a::T, b::T) where {T<:MPolyQuoLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  if denominator(a) == denominator(b) 
    return reduce_fraction((parent(a))(numerator(a) + numerator(b), denominator(a)))
  end
  return reduce_fraction((parent(a))(numerator(a)*denominator(b) + numerator(b)*denominator(a), denominator(a)*denominator(b)))
end

# TODO: improve this method.
function addeq!(a::T, b::T) where {T<:MPolyQuoLocalizedRingElem}
  a = a+b
  return a
end

function -(a::T, b::T) where {T<:MPolyQuoLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  if denominator(a) == denominator(b) 
    return reduce_fraction((parent(a))(numerator(a) - numerator(b), denominator(a)))
  end
  return reduce_fraction((parent(a))(numerator(a)*denominator(b) - numerator(b)*denominator(a), denominator(a)*denominator(b)))
end

function *(a::T, b::T) where {T<:MPolyQuoLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return reduce_fraction((parent(a))(numerator(a)*numerator(b), denominator(a)*denominator(b)))
end

function *(a::RET, b::MPolyQuoLocalizedRingElem{BRT, BRET, RT, RET, MST}) where {BRT, BRET, RT, RET <: RingElem, MST}
  return reduce_fraction((parent(b))(a*numerator(b), denominator(b)))
end

function *(a::MPolyQuoLocalizedRingElem{BRT, BRET, RT, RET, MST}, b::RET) where {BRT, BRET, RT, RET <: RingElem, MST}
  return b*a
end

function *(a::BRET, b::MPolyQuoLocalizedRingElem{BRT, BRET, RT, RET, MST}) where {BRT, BRET, RT, RET <: RingElem, MST}
  return reduce_fraction((parent(b))(base_ring(b)(a)*numerator(b), denominator(b)))
end

function *(a::MPolyQuoLocalizedRingElem{BRT, BRET, RT, RET, MST}, b::BRET) where {BRT, BRET, RT, RET <: RingElem, MST}
  return b*a
end

### Why are the `//`-methods not implemented?
# Since a quotient ring Q = R/I of a polynomial ring R is not necessarily 
# factorial, it is difficult to decide, whether or not a and b have a 
# common factor g that can be cancelled so that b'= b/g ∈  Q belongs 
# to the multiplicative set. Moreover, this would be the case if any 
# lift of b' belonged to S + I where S ⊂ R is the original multiplicative 
# set. Such containment can not easily be checked based only on the 
# functionality provided for S: Depending on the concrete type of 
# S, this task is algorithmically difficult, if not impossible.
#
# To remedy for this, we pursue the following pattern: 
#
# * Creation of elements [a]/[b] ∈ Q[S⁻¹] is possible only from 
#   representatives a/b ∈ R[S⁻¹] with b ∈ S.
# * The ring arithmetic attempts to cancel fractions which includes 
#   reduction modulo I of both the numerator and the denominator. 
#   This leads to representatives which would not be admissible 
#   for creation of elements in Q[S⁻¹].
# * Division routines can be used for the ring R[S⁻¹] with subsequent
#   conversion. 

function Base.:(//)(a::Oscar.IntegerUnion, b::MPolyQuoLocalizedRingElem)
  error("function `//` not implemented for elements of type $(typeof(b))")
end

function Base.:(//)(a::T, b::T) where {T<:MPolyQuoLocalizedRingElem}
  error("function `//` not implemented for elements of type $(typeof(b))")
end

function ==(a::T, b::T) where {T<:MPolyQuoLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return numerator(a)*denominator(b) == numerator(b)*denominator(a)
end

function ^(a::MPolyQuoLocalizedRingElem, i::fmpz)
  return parent(a)(lifted_numerator(a)^i, lifted_denominator(a)^i)
end

function ^(a::MPolyQuoLocalizedRingElem, i::Integer)
  return parent(a)(lifted_numerator(a)^i, lifted_denominator(a)^i)
end

function isone(a::MPolyQuoLocalizedRingElem) 
  a = reduce_fraction(a)
  return (numerator(a) == denominator(a))
end

function iszero(a::MPolyQuoLocalizedRingElem)
  a = reduce_fraction(a)
  return iszero(numerator(a))
end

### enhancement of the arithmetic
function reduce_fraction(f::MPolyQuoLocalizedRingElem)
  h = lift(f)
  h = reduce(h, groebner_basis(localized_modulus(parent(f))))
  g = gcd(numerator(h), denominator(h))
  h = parent(h)(divexact(numerator(h), g), divexact(denominator(h), g))
  return parent(f)(h)
end


### implementation of Oscar's general ring interface
one(W::MPolyQuoLocalizedRing) = W(one(base_ring(W)))
zero(W::MPolyQuoLocalizedRing)= W(zero(base_ring(W)))

elem_type(W::MPolyQuoLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyQuoLocalizedRingElem{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}
elem_type(T::Type{MPolyQuoLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}}) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyQuoLocalizedRingElem{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}

parent_type(W::MPolyQuoLocalizedRingElem{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyQuoLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}
parent_type(T::Type{MPolyQuoLocalizedRingElem{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}}) where {BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType} = MPolyQuoLocalizedRing{BaseRingType, BaseRingElemType, RingType, RingElemType, MultSetType}


########################################################################
# Homomorphisms of quotients of localized polynomial algebras          #
########################################################################
# 
# Suppose we are given two localizations of polynomial algebras 
# by means of commutative diagrams 
#
#       R   →    P = R/I
#       ↓        ↓ 
# V = R[T⁻¹] →  P[T⁻¹]
#
# and 
#
#       S   →    Q = S/J
#       ↓        ↓ 
# W = S[U⁻¹] →  Q[U⁻¹].
#
# Lemma:
# For any homomorphism φ : P[T⁻¹] → Q[U⁻¹] the following holds. 
#
#             φ
#     P[T⁻¹]  →  Q[U⁻¹]
#       ↑          ↑
#     R[T⁻¹] --> S[U⁻¹]
#       ↑    ↗ ψ   ↑ ι
#       R     →  S[c⁻¹]
#             η    ↑ κ
#                  S
#
# a) The composition of maps R → Q[U⁻¹] completely determines φ by 
#    the images xᵢ ↦ [aᵢ]/[bᵢ] with aᵢ ∈ S, bᵢ ∈ U.
# b) Let ψ : R → S[U⁻¹] be the map determined by some choice of 
#    the images xᵢ↦ aᵢ/bᵢ as above. Then ψ extends to a map 
#    R[T⁻¹] → S[U⁻¹] if and only if 
#    
#       for all t ∈ T : ψ(t) ∈ U.
#
#    This is not necessarily the case as the lift of images 
#    φ(t) ∈ Q[U⁻¹] in S[U⁻¹] need only be elements of U + J.
# c) Choosing a common denominator c for all ψ(xᵢ), we obtain a 
#    ring homomorphism η : R → S[c⁻¹] such that ψ = ι ∘ η.
#
# Upshot: In order to describe φ, we may store some homomorphism 
#     
#       ψ : R → S[U⁻¹] 
#
# lifting it and keep in mind the ambiguity of choices for such ψ.
# The latter point c) will be useful for reducing to a homomorphism 
# of finitely generated algebras.

mutable struct MPolyQuoLocalizedRingHom{
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    DomainMultSetType, 
    CodomainMultSetType
  } <: AbsLocalizedRingHom{
    RingType, RingElemType, DomainMultSetType, CodomainMultSetType
  }
  domain::MPolyQuoLocalizedRing
  codomain::MPolyQuoLocalizedRing
  images::Vector{MPolyLocalizedRingElem}

  # variables for caching
  helper_ring::RingType
  helper_images::Vector{RingElemType}
  minimal_denominators::Vector{RingElemType}
  eta::AlgHom{BaseRingElemType}
  kappa::AlgHom{BaseRingElemType}
  
  inverse::MPolyQuoLocalizedRingHom{
    BaseRingType, 
    BaseRingElemType, 
    RingType, 
    RingElemType, 
    CodomainMultSetType,
    DomainMultSetType
  }

  function MPolyQuoLocalizedRingHom(
      L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, DMST}, 
      M::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, CMST}, 
      a::Vector{MPolyLocalizedRingElem{BRT, BRET, RT, RET, CMST}}
    ) where {BRT, BRET, RT, RET, CMST, DMST}
    R = base_ring(L)
    S = base_ring(M)
    k = coefficient_ring(R) 
    k == coefficient_ring(S) || error("the two polynomial rings are not defined over the same coefficient ring")
    ngens(R) == length(a) || error("the number of images does not coincide with the number of variables")
    parent_check = true
    for x in a
      parent_check = parent_check && parent(x) == localized_ring(M)
    end
    parent_check || error("the images of the variables are not elements of the codomain")
    # Check whether this homomorphism is well defined
    # TODO: Implement that!
    return new{typeof(k), elem_type(k), typeof(R), elem_type(R), typeof(inverted_set(L)), typeof(inverted_set(M))}(L, M, a)
  end
end

### required getter functions
domain(f::MPolyQuoLocalizedRingHom) = f.domain
codomain(f::MPolyQuoLocalizedRingHom) = f.codomain
images(f::MPolyQuoLocalizedRingHom) = f.images

### required functionality
function (f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(
    p::MPolyQuoLocalizedRingElem{BRT, BRET, RT, RET, DMST}
  ) where {BRT, BRET, RT, RET, DMST, CMST}
  parent(p) == domain(f) || error("the given element does not belong to the domain of the map")
  return codomain(f)(evaluate(lifted_numerator(p), images(f))//evaluate(lifted_denominator(p), images(f)))
end

### additional constructors
function MPolyQuoLocalizedRingHom(
    L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, DMST}, 
    M::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, CMST}, 
    a::Vector{MPolyQuoLocalizedRingElem{BRT, BRET, RT, RET, CMST}}
  ) where {BRT, BRET, RT, RET, CMST, DMST}
  return MPolyQuoLocalizedRingHom(L, M, lift.(a))
end

function MPolyQuoLocalizedRingHom(
    L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, DMST}, 
    M::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, CMST}, 
    a::Vector{T}
  ) where {BRT, BRET, RT, RET, CMST, DMST, T<:Any}
  return MPolyQuoLocalizedRingHom(L, M, localized_ring(M).(a))
end


### additional functionality 
function (f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(
    p::MPolyLocalizedRingElem{BRT, BRET, RT, RET, DMST}
  ) where {BRT, BRET, RT, RET, DMST, CMST}
  parent(p) == localized_ring(domain(f)) || error("the given element does not belong to the domain of the map")
  return codomain(f)(evaluate(numerator(p), images(f))//evaluate(denominator(p), images(f)))
end

function (f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(
    p::MPolyQuoElem{RET}
  ) where {BRT, BRET, RT, RET, DMST, CMST}
  parent(p) == quotient_ring(domain(f)) || error("the given element does not belong to the domain of the map")
  return codomain(f)(evaluate(lift(p), images(f)))
end

### overwriting of the generic method
function (f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(
    p::RET
  ) where {BRT, BRET, RT, RET, DMST, CMST}
  parent(p) == base_ring(domain(f)) || error("the given element does not belong to the domain of the map")
  return codomain(f)(evaluate(p, images(f)))
end

### provide an extra method for elements of the base ring
function (f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(p::BRET) where {BRT, BRET, RT, RET, DMST, CMST}
  parent(p) == coefficient_ring(base_ring(domain(f))) || error("the given element does not belong to the domain of the map")
  return codomain(f)(p)
end

### remove the ambiguity of methods in case the base ring is ZZ
function (f::MPolyQuoLocalizedRingHom)(p::fmpz) 
  return codomain(f)(p)
end

### implementing the Oscar map interface
identity_map(W::T) where {T<:MPolyQuoLocalizedRing} = MPolyQuoLocalizedRingHom(W, W, W.(gens(base_ring(W))))
function compose(
    f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, MST1, MST2}, 
    g::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, MST2, MST3}
  ) where {BRT, BRET, RT, RET, MST1, MST2, MST3}
  codomain(f) == domain(g) || error("maps are not compatible")
  return MPolyQuoLocalizedRingHom(domain(f), codomain(g), g.(images(f)))
end

function Base.show(io::IO, f::MPolyQuoLocalizedRingHom)
  print(io, "Ring homomorphism from $(domain(f)) to $(codomain(f)) mapping the generators to $(images(f))")
end

function ==(f::MPolyQuoLocalizedRingHom, g::MPolyQuoLocalizedRingHom) 
  domain(f) == domain(g) || return false
  codomain(f) == codomain(g) || return false
  a = images(f)
  b = images(g)
  n = length(a)
  for i in 1:n
    a[i] == b[i] || return false
  end
  return true
end

### helper_ring
# Sets up the ring S[c⁻¹] from the Lemma.
function helper_ring(f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST}) where {BRT, BRET, RT, RET, DMST, CMST}
  if isdefined(f, :helper_ring)
    return f.helper_ring
  end
  f.minimal_denominators = Vector{RET}()
  R = base_ring(domain(f))
  S = base_ring(codomain(f))
  p = one(S)

  for d in [denominator(y) for y in images(f)]
    g = gcd(d, p)
    d_min = divexact(d, g)
    push!(f.minimal_denominators, d)
    p = p*d_min
  end
 
  help_ring, help_kappa, theta = _add_variables(S, ["θ"])
  f.helper_ring = help_ring
  f.kappa = help_kappa
  c_inv = theta[1]
  f.helper_images = [f.kappa(numerator(y))*c_inv*f.kappa(divexact(p, denominator(y))) for y in images(f)]
  f.eta = AlgebraHomomorphism(R, help_ring, f.helper_images)
  return f.helper_ring
end

function helper_images(
    f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST}
  ) where {BRT, BRET, RT, RET, DMST, CMST} 
  if !isdefined(f, :helper_images) 
    helper_ring(f)
  end
  return f.helper_images
end

function minimal_denominators(
    f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST}
  ) where {BRT, BRET, RT, RET, DMST, CMST} 
  if !isdefined(f, :minimal_denominators) 
    helper_ring(f)
  end
  return f.minimal_denominators
end

function helper_eta(
    f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST}
  ) where {BRT, BRET, RT, RET, DMST, CMST} 
  if !isdefined(f, :eta) 
    helper_ring(f)
  end
  return f.eta
end

function helper_kappa(
    f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST}
  ) where {BRT, BRET, RT, RET, DMST, CMST} 
  if !isdefined(f, :kappa) 
    helper_ring(f)
  end
  return f.kappa
end

function common_denominator(
    f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST}
  ) where {BRT, BRET, RT, RET, DMST, CMST} 
  if !isdefined(f, :minimal_denominators) 
    helper_ring(f)
  end
  return (length(f.minimal_denominators) == 0 ? one(base_ring(codomain(f))) : prod(f.minimal_denominators))
end

function helper_ideal(
    f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST}
  ) where {BRT, BRET, RT, RET, DMST, CMST} 
  if !isdefined(f, :helper_ring) 
    helper_ring(f)
  end
  Sc = helper_ring(f)
  return ideal(Sc, one(Sc)-last(gens(Sc))*helper_kappa(f)(common_denominator(f)))
end

# return the localized ring as a quotient of a polynomial ring using Rabinowitsch's trick.
function as_affine_algebra(
    L::MPolyQuoLocalizedRing{BRT, BRET, RT, RET, 
			     MPolyPowersOfElement{BRT, BRET, RT, RET}}; 
    inverse_name::String="θ"
  ) where {BRT, BRET, RT, RET}
  R = base_ring(L)
  A, phi, t = _add_variables_first(R, [inverse_name])
  theta = t[1]
  f = prod(denominators(inverted_set(L)))
  I = ideal(A, [phi(g) for g in gens(modulus(L))]) + ideal(A, [one(A)-theta*phi(f)])
  return A, I, f, phi, theta
end


function is_isomorphism(
    phi::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, MST, MST}
  ) where {BRT, BRET, RT, RET, MST<:MPolyPowersOfElement{BRT, BRET, RT, RET}}
  if isdefined(phi, :inverse)
    return true
  end
  K = domain(phi)
  L = codomain(phi)
  A, I, d1, inc1, theta1 = as_affine_algebra(K, inverse_name="s")
  B, J, d2, inc2, theta2 = as_affine_algebra(L, inverse_name="t")

  # write the denominators of the images of the variables xᵢ of K as 
  # polynomials in the variables yⱼ of L and the localization variable t:
  #
  # TODO: This can most probably be fine tuned as follows. Make sure that 
  # the ideal J is of the form J' + ⟨1-t⋅g(y)⟩ where J' is generated by a 
  # Groebner basis for the saturated ideal of L in 𝕜[y]. Then choose an 
  # elimination ordering on t on 𝕜[t,y] which coincides on the y-variables 
  # with the ordering that had been used to compute the Groebner-basis of 
  # J'. Then the generators above for J are also already a Groebner basis 
  # since J' was already saturated. 
  #
  # Now a Groebner-basis computation for the ideal J_ext should proceed 
  # quickly by multiplying q with subsequently higher powers of t and reduction 
  # modulo J until a constant polynomial is attained. 
  #
  # With this strategy, the Groebner-basis computation should not even be 
  # expensive. 
  denoms = Vector{elem_type(B)}()
  for f in images(phi)
    J_ext = ideal(B, push!(gens(J), inc2(denominator(f))))
    G, M = groebner_basis_with_transformation_matrix(J_ext)
    G[1]==one(B) || error("the denominator is not a unit in the target ring")
    push!(denoms, last(M))
  end

  # write the images as polynomials in B 
  imagesB = [ inc2(numerator(images(phi)[i]))*denoms[i] for i in (1:length(denoms))]

  # expand the localization variable s in A as a polynomial in B
  denoms = Vector{elem_type(B)}()
  for h in denominators(inverted_set(K))
    phi_h = phi(h)
    p = lifted_numerator(phi_h)
    q = lifted_denominator(phi_h)
    J_ext = ideal(B, push!(gens(J), inc2(p)))
    G, M = groebner_basis_with_transformation_matrix(J_ext)
    G[1]==one(B) || error("the denominator is not a unit in the target ring")
    push!(denoms, inc2(q)*last(M))
  end
  pushfirst!(imagesB, prod(denoms))

  # perform a sanity check
  phiAB = AlgebraHomomorphism(A, B, imagesB)
  issubset(ideal(B, [phiAB(g) for g in gens(I)]), J) || error("the homomorphism is not well defined")

  # assemble a common ring in which the equations for the graph of phi can 
  # be realized.
  C, j1, B_vars = _add_variables_first(A, String.(symbols(B)))
  j2 = AlgebraHomomorphism(B, C, B_vars)
  G = ideal(C, [j1(gens(A)[i]) - j2(imagesB[i]) for i in (1:length(gens(A)))]) + ideal(C, j2.(gens(J)))
  singC, _ = Singular.PolynomialRing(Oscar.singular_ring(base_ring(C)), 
				  String.(symbols(C)),  
				  ordering=Singular.ordering_dp(1)
				  *Singular.ordering_dp(nvars(B)-1)
				  *Singular.ordering_dp(1)
				  *Singular.ordering_dp(nvars(A)-1))
  # TODO: adjust this to the orderings used for the previous groebner basis 
  # computations in A and B once such things are respected. 
  singG = Singular.Ideal(singC, singC.(gens(G)))
  stdG = Singular.std(singG) 
  
  # Compute the inverse images of the variables of L
  m = nvars(A)-1
  n = nvars(B)-1
  R = base_ring(K)
  V = localized_ring(K)
  pre_images = Vector{elem_type(V)}()
  #pre_imagesA = Vector{elem_type(A)}()
  # the first variable needs special treatment
  #singp = Singular.reduce(gens(singC)[1], stdG)
  #singp < gens(singC)[n+1] || return false
  #p = C(singp)
  #push!(pre_imagesA, evaluate(p, vcat([zero(A) for i in 0:n], gens(A))))
  for i in 1:n
    singp = Singular.reduce(gens(singC)[i+1], stdG)
    singp < gens(singC)[n+1] || return false
    p = C(singp)
    # Write p as an element in the very original ring
    #push!(pre_imagesA, evaluate(p, vcat([zero(A) for i in 0:n], gens(A))))
    push!(pre_images, evaluate(p, vcat([zero(V) for i in 0:n], [V(one(R), d1)], V.(gens(R)))))
  end

  invJ = ideal(A, [(p < gens(singC)[n+1] ? evaluate(C(p), vcat([zero(A) for i in 0:n], gens(A))) : zero(A)) for p in gens(stdG)])
  # TODO: invJ is already a Groebner basis, but only for the ordering used 
  # in the above elimination.
  # Make sure, this ordering is used again for the sanity check below!
  invJ == I || return false

  phi.inverse = MPolyQuoLocalizedRingHom(L, K, pre_images)
  phi.inverse.inverse = phi
  return true
end

function inverse(phi::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, MST, MST}
  ) where {BRT, BRET, RT, RET, MST<:MPolyPowersOfElement{BRT, BRET, RT, RET}}
  is_isomorphism(phi) || error("the given morphism is not an isomorphism")
  return phi.inverse
end



########################################################################
# Functionality for maps and ideals                                    #
########################################################################
# 
# The methods have to be adapted to the type of localization in the 
# target. It needs to be assured that all components which are invisible
# in the localization, are indeed discarded. 

function (f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, DMST}
  ) where {BRT<:Ring, BRET<:RingElement, RT<:MPolyRing, RET<:MPolyElem, 
    DMST<:AbsMultSet{RT, RET}, CMST<:MPolyPowersOfElement{BRT, BRET, RT, RET}
  }
  base_ring(I) == localized_ring(domain(f)) || error("ideal does not lay in the correct ring")
  imgs = f.(gens(I))
  return ideal(localized_ring(codomain(f)), lift.(imgs))
end

function (f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST})(
    I::MPolyIdeal{RET}
  ) where {BRT<:Ring, BRET<:RingElement, RT<:MPolyRing, RET<:MPolyElem, 
    DMST<:AbsMultSet{RT, RET}, CMST<:MPolyPowersOfElement{BRT, BRET, RT, RET}
  }
  base_ring(I) == base_ring(domain(f)) || error("ideal does not lay in the correct ring")
  return f(domain(f)(I))
end


### adds the variables with names specified in v to the polynomial 
# ring R and returns a triple consisting of the new ring, the embedding 
# of the original one, and a list of the new variables. 
function _add_variables(R::RingType, v::Vector{String}) where {RingType<:MPolyRing}
  ext_R, _ = PolynomialRing(coefficient_ring(R), vcat(symbols(R), Symbol.(v)))
  n = length(gens(R))
  phi = AlgebraHomomorphism(R, ext_R, gens(ext_R)[1:n])
  return ext_R, phi, gens(ext_R)[(length(gens(R))+1):length(gens(ext_R))]
end

function _add_variables_first(R::RingType, v::Vector{String}) where {RingType<:MPolyRing}
  ext_R, _ = PolynomialRing(coefficient_ring(R), vcat(Symbol.(v), symbols(R)))
  n = length(gens(R))
  phi = AlgebraHomomorphism(R, ext_R, gens(ext_R)[1+length(v):n+length(v)])
  return ext_R, phi, gens(ext_R)[(1:length(v))]
end



function preimage(
    f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST},
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, CMST}
  ) where {BRT<:Ring, BRET<:RingElement, RT<:MPolyRing, RET<:MPolyElem, 
    DMST<:AbsMultSet{RT, RET}, CMST<:MPolyPowersOfElement{BRT, BRET, RT, RET}
  }
  base_ring(I) == localized_ring(codomain(f)) || error("the ideal does not belong to the codomain of the map")
  R = base_ring(domain(f))
  S = base_ring(codomain(f))
  Sc = helper_ring(f)
  lbpa = groebner_basis(I) # saturation takes place in this computation
  J = ideal(Sc, [helper_kappa(f)(g) for g in numerator.(oscar_gens(lbpa))]) + helper_ideal(f)
  return localized_ring(domain(f))(preimage(helper_eta(f), J))
end

function preimage(
    f::MPolyQuoLocalizedRingHom{BRT, BRET, RT, RET, DMST, CMST},
    I::MPolyLocalizedIdeal{BRT, BRET, RT, RET, CMST}
  ) where {BRT<:Ring, BRET<:RingElement, RT<:MPolyRing, RET<:MPolyElem, 
    DMST<:AbsMultSet{RT, RET}, CMST<:MPolyComplementOfKPointIdeal{BRT, BRET, RT, RET}
  }
  base_ring(I) == localized_ring(codomain(f)) || error("the ideal does not belong to the codomain of the map")
  J = ideal(helper_ring(f), helper_kappa(f).(gens(saturated_ideal(I)))) + helper_ideal(f)
  return localized_ring(domain(f))(preimage(helper_eta(f), J))
end
