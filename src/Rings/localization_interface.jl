import AbstractAlgebra.Ring
import AbstractAlgebra: expressify, show_via_expressify

#################################################################################
# General framework for localizations of rings; to be used with affine algebras #
#################################################################################

#################################################################################
# Multiplicatively closed sets of (commutative) rings                           #
#################################################################################

@doc raw"""
    AbsMultSet{RingType, RingElemType}

The abstract type for a multiplicatively closed subset of a commutative ring 
of type `RingType` with elements of type `RingElemType`.
"""
abstract type AbsMultSet{RingType<:Ring, RingElemType<:RingElem} end

### required getter functions
@doc raw"""
    ambient_ring(S::AbsMultSet)

Return the ambient ring `R` for a multiplicatively closed set `S ⊂ R`.
"""
function ambient_ring(S::AbsMultSet)
  error("method `ambient_ring` not implemented for multiplicatively closed sets of type $(typeof(S))")
end

### required functionality
@doc raw"""
    in(f::RingElemType, U::AbsMultSet{RingType, RingElemType}) where {RingType, RingElemType}

Return `true` if `f` belongs to `U`, `false` otherwise.

# Examples
```jldoctest
julia> R, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"])
(Multivariate polynomial ring in 3 variables over QQ, QQMPolyRingElem[x, y, z])

julia> P = ideal(R, [x])
ideal(x)

julia> U = MPolyComplementOfPrimeIdeal(P)
Complement
  of prime ideal(x)
  in multivariate polynomial ring in 3 variables over QQ

julia> x+1 in U
true
```
"""
function Base.in(f::RingElemType, S::AbsMultSet{RingType, RingElemType}) where {RingType, RingElemType}
  error("method not implemented for multiplicatively closed sets of type $(typeof(S))")
end

### iterator over the multiplicative set
# This can (and should) be used to iterate over some set of generators 
# of the multiplicative set whenever possible. For instance, this is 
# used to check well-definedness of homomorphisms from localized rings. 
# By default, however, this iteration does nothing.
Base.iterate(U::T) where {T<:AbsMultSet} = (one(ambient_ring(U)), 1)
Base.iterate(U::T, a::Tuple{<:RingElem, Int}) where {T<:AbsMultSet} = nothing
Base.iterate(U::T, i::Int) where {T<:AbsMultSet} = nothing


#################################################################################
# Localizations of (commutative) rings at multiplicatively closed sets          #
#################################################################################
@doc raw"""
    AbsLocalizedRing{RingType, RingElemType, MultSetType}

The abstract type for modelling the localization R[U⁻¹] of a commutative ring R 
of type `RingType` with elements of type `RingElemType` at a multiplicatively closed 
subset S of type `MultSetType`. 

It is recommended to implement the arithmetic of a concrete instance of such a localized 
ring R[U⁻¹] using the concept of fractions of elements in the original ring R. To check
whether a given denominator is admissible for the specific localization, use the 
`ìn` function.

Depending on the actual type of R and U, further functionality can be provided using 
various Gröbner basis driven backends. 
"""
abstract type AbsLocalizedRing{RingType, RingElemType, MultSetType} <: Ring end

### required getter functions
@doc raw"""
    base_ring(Rloc::AbsLocalizedRing)

If, say, Rloc = R[U⁻¹], return R.

# Examples
```jldoctest
julia> R, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"])
(Multivariate polynomial ring in 3 variables over QQ, QQMPolyRingElem[x, y, z])

julia> P = ideal(R, [x])
ideal(x)

julia> U = MPolyComplementOfPrimeIdeal(P)
Complement
  of prime ideal(x)
  in multivariate polynomial ring in 3 variables over QQ

julia> Rloc, _ = localization(U);

julia> R === base_ring(Rloc)
true
```
"""
function base_ring(W::AbsLocalizedRing)
  error("`base_ring` is not implemented for localized rings of type $(typeof(W))")
end

@doc raw"""
    inverted_set(Rloc::AbsLocalizedRing)

If, say, Rloc = R[U⁻¹], return U.

# Examples
```jldoctest
julia> R, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"])
(Multivariate polynomial ring in 3 variables over QQ, QQMPolyRingElem[x, y, z])

julia> P = ideal(R, [x])
ideal(x)

julia> U = MPolyComplementOfPrimeIdeal(P)
Complement
  of prime ideal(x)
  in multivariate polynomial ring in 3 variables over QQ

julia> Rloc, _ = localization(U);

julia> U === inverted_set(Rloc)
true
```
"""
function inverted_set(W::AbsLocalizedRing)
  error("`inverted_set` is not implemented for localized rings of type $(typeof(W))")
end

### required functionality
@doc raw"""
    localization(U::AbsMultSet)

Given a multiplicatively closed subset of a multivariate polynomial ring ``R``, say, 
return the localization of ``R`` at ``U`` together with the localization map ``R`` ``\to`` ``R[U^{-1}]``.

    localization(R::Ring, U::AbsMultSet)

Given a multiplicatively closed subset ``U`` of ``R``, proceed as above.

# Examples
```jldoctest
julia> R, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"])
(Multivariate polynomial ring in 3 variables over QQ, QQMPolyRingElem[x, y, z])

julia> P = ideal(R, [x])
ideal(x)

julia> U = MPolyComplementOfPrimeIdeal(P)
Complement
  of prime ideal(x)
  in multivariate polynomial ring in 3 variables over QQ

julia> Rloc, iota = localization(R, U);

julia> Rloc
Localization
  of multivariate polynomial ring in 3 variables x, y, z
    over rational field
  at complement of prime ideal(x)

julia> iota
Ring homomorphism
  from multivariate polynomial ring in 3 variables over QQ
  to localization of multivariate polynomial ring in 3 variables over QQ at complement of prime ideal(x)
defined by
  x -> x
  y -> y
  z -> z
```
"""
function localization(S::AbsMultSet)
  error("localizations at multiplicatively closed sets of type $(typeof(S)) are not implemented")
end

function localization(R::Ring, U::AbsMultSet)
  R == ambient_ring(U) || error("ring and multiplicative set are incompatible")
  return localization(U)
end

@doc raw"""
    (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(f::AbstractAlgebra.Generic.Frac{RingElemType}) where {RingType, RingElemType, MultSetType} 

Converts a fraction f = a//b to an element of the localized ring W.
"""
function (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(f::AbstractAlgebra.Generic.Frac{RingElemType}) where {RingType, RingElemType, MultSetType} 
  error("conversion for fractions to elements of type $(typeof(W)) is not implemented")
end

### required conversions
@doc raw"""
    (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(a::RingElemType) where {RingType, RingElemType, MultSetType} 

Converts an element `a` to an element of `W`.
"""
function (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(a::RingElemType) where {RingType, RingElemType, MultSetType} 
  error("conversion of elements of type $(RingElemType) to elements of $(typeof(W)) is not implemented")
end

@doc raw"""
    (W::AbsLocalizedRing)(a::RingElem, b::RingElem; check::Bool=true)

Converts a pair `(a, b)` to an element `a//b` in `W`.

**Note:** When the flag `check=true` is set, then it will be checked 
whether the fraction `a//b` is admissible for `W`. Since those checks 
are usually expensive, it should be disabled for safe internal usage.
"""
function (W::AbsLocalizedRing{RingType, RingElemType, MultSetType})(a::RingElemType, b::RingElemType; check::Bool=true) where {RingType, RingElemType, MultSetType} 
  error("conversion of pairs `(a, b)` of elements of type $(RingElemType) to fractions `a/b` in a ring of type $(typeof(W)) is not implemented")
end

### Other conversions for the sake of convenience
(W::AbsLocalizedRing)(a::Int) = W(base_ring(W)(a))
(W::AbsLocalizedRing)(a::Integer) = W(base_ring(W)(a))
(W::AbsLocalizedRing)(a::ZZRingElem) = W(base_ring(W)(a))


#################################################################################
# Elements of localized rings                                                   #
#################################################################################
@doc raw"""
    AbsLocalizedRingElem{RingType, RingElemType, MultSetType}

The abstract type of an element of the localization R[S⁻¹] of a commutative ring 
R of type `RingType` with elements of type `RingElemType` at a multiplicatively 
closed set S of type `MultSetType`.
"""
abstract type AbsLocalizedRingElem{
    RingType <: AbstractAlgebra.Ring, 
    RingElemType <: AbstractAlgebra.RingElem, 
    MultSetType <: AbsMultSet
  } <: AbstractAlgebra.RingElem end

### required getter functions 
@doc raw"""
    numerator(f::AbsLocalizedRingElem)

Return the numerator of the internal representative of `f`.
"""
function numerator(f::AbsLocalizedRingElem)
  error("`numerator` is not implemented for elements of type $(typeof(f))")
end

@doc raw"""
    denominator(f::AbsLocalizedRingElem)

Return the denominator of the internal representative of `f`.
"""
function denominator(f::AbsLocalizedRingElem)
  error("`denominator` is not implemented for elements of type $(typeof(f))")
end

@doc raw"""
    parent(f::AbsLocalizedRingElem)

Return the parent ring R[S⁻¹] of `f`.
"""
function parent(f::AbsLocalizedRingElem)
  error("`parent` is not implemented for the type $(typeof(f))")
end

function expressify(f::AbsLocalizedRingElem; context=nothing) 
  isone(denominator(f)) && return expressify(numerator(f), context=context)
  return Expr(:call, :/, expressify(numerator(f), context=context), expressify(denominator(f), context=context))
end

@enable_all_show_via_expressify AbsLocalizedRingElem

# type getters
base_ring_elem_type(::Type{T}) where {BRT, BRET, T<:AbsLocalizedRingElem{BRT, BRET}} = BRET
base_ring_type(::Type{T}) where {BRT, BRET, T<:AbsLocalizedRingElem{BRT, BRET}} = BRT

base_ring_elem_type(L::AbsLocalizedRing) = base_ring_elem_type(typeof(L))
base_ring_type(L::AbsLocalizedRing) = base_ring_type(typeof(L))


########################################################################
# Arithmetic; a dumb catchall implementation, NOT performant!          #
########################################################################

@doc raw"""
    reduce_fraction(a::AbsLocalizedRingElem)

Reduce the fraction a = p/q. **Warning**: The catchall-implementation does nothing!
"""
function reduce_fraction(a::AbsLocalizedRingElem)
  return a
end

function +(a::T, b::T) where {T<:AbsLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  if denominator(a) == denominator(b) 
    return reduce_fraction((parent(a))(numerator(a) + numerator(b), denominator(a), check=false))
  end
  return reduce_fraction((parent(a))(numerator(a)*denominator(b) + numerator(b)*denominator(a), denominator(a)*denominator(b), check=false))
end

function -(a::T, b::T) where {T<:AbsLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  if denominator(a) == denominator(b) 
    return reduce_fraction((parent(a))(numerator(a) - numerator(b), denominator(a), check=false))
  end
  return reduce_fraction((parent(a))(numerator(a)*denominator(b) - numerator(b)*denominator(a), denominator(a)*denominator(b), check=false))
end

function -(a::T) where {T<:AbsLocalizedRingElem}
  return (parent(a))(-numerator(a), denominator(a), check=false)
end

function *(a::T, b::T) where {T<:AbsLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return reduce_fraction((parent(a))(numerator(a)*numerator(b), denominator(a)*denominator(b), check=false))
end

function *(a::RET, b::AbsLocalizedRingElem{RT, RET, MST}) where {RT, RET <: RingElem, MST}
  return reduce_fraction((parent(b))(a*numerator(b), denominator(b), check=false))
end

function *(a::AbsLocalizedRingElem{RT, RET, MST}, b::RET) where {RT, RET <: RingElem, MST}
  return b*a
end

function Base.:(/)(a::Oscar.IntegerUnion, b::AbsLocalizedRingElem)
  return divexact(parent(b)(a), b)
end

function Base.:(/)(a::T, b::T) where {T<:AbsLocalizedRingElem}
  return divexact(a, b)
end

function ==(a::T, b::T) where {T<:AbsLocalizedRingElem}
  parent(a) == parent(b) || error("the arguments do not have the same parent ring")
  return numerator(a)*denominator(b) == numerator(b)*denominator(a)
end

function ^(a::AbsLocalizedRingElem, i::ZZRingElem)
  return parent(a)(numerator(a)^i, denominator(a)^i, check=false)
end

function ^(a::AbsLocalizedRingElem, i::Integer)
  return parent(a)(numerator(a)^i, denominator(a)^i, check=false)
end

function divexact(a::T, b::T; check::Bool=false) where {T<:AbsLocalizedRingElem} 
  error("method `divexact` not implemented for arguments of type $(typeof(a))")
end

function inv(a::AbsLocalizedRingElem) 
  return divexact(parent(a)(denominator(a)), parent(a)(numerator(a)))
end

########################################################################
# generic functions to adhere to the Oscar ring interface              #
########################################################################

isone(a::AbsLocalizedRingElem) = (numerator(a) == denominator(a))

is_unit(f::AbsLocalizedRingElem) = numerator(f) in inverted_set(parent(f))

is_domain_type(T::Type{U}) where {U<:AbsLocalizedRingElem} = false # default set to false

is_exact_type(T::Type{U}) where {U<:AbsLocalizedRingElem} = false # default set to false

function Base.hash(f::T, h::UInt) where {T<:AbsLocalizedRingElem} 
  r = 0x78a97cd90
  r = xor(r, hash(numerator(f), h))
  return xor(r, hash(denominator(f), h))
end

Base.deepcopy_internal(f::T, dict::IdDict) where {T<:AbsLocalizedRingElem} = parent(f)(copy(numerator(f)), copy(denominator(f)), check=false)

one(W::AbsLocalizedRing) = W(one(base_ring(W)))

zero(W::AbsLocalizedRing) = W(zero(base_ring(W)))

(W::AbsLocalizedRing)() = zero(W)

canonical_unit(f::LocRingElemType) where {LocRingElemType<:AbsLocalizedRingElem} = one(parent(f))

characteristic(W::AbsLocalizedRing) = characteristic(base_ring(W))

function Base.show(io::IO, ::MIME"text/plain", W::AbsLocalizedRing)
  io = pretty(io)
  println(io, "Localization", Indent())
  print(io, "of ", Lowercase())
  show(io, MIME("text/plain"), base_ring(W))
  println(io)
  print(io, "at ")
  print(io, Lowercase(), inverted_set(W))
  print(io, Dedent())
end

function Base.show(io::IO, W::AbsLocalizedRing)
  io = pretty(io)
  if get(io, :supercompact, false)
    print(io, "Localized ring")
  else
    print(io, "Localization of ", Lowercase(), base_ring(W))
    print(io, " at ")
    print(io, Lowercase(), inverted_set(W))
  end
end

function zero!(a::AbsLocalizedRingElem) 
  a = zero(parent(a))
  return a
end

function mul!(c::T, a::T, b::T) where {T<:AbsLocalizedRingElem} 
  c = a*b
  return c
end

function add!(c::T, a::T, b::T) where {T<:AbsLocalizedRingElem} 
  c = a+b
  return c
end

function addeq!(a::T, b::T) where {T<:AbsLocalizedRingElem}
  a = a+b
  return a
end

### promotion rules
AbstractAlgebra.promote_rule(::Type{S}, ::Type{S}) where {S<:AbsLocalizedRingElem} = S

function AbstractAlgebra.promote_rule(::Type{S}, ::Type{T}) where {RT, RET, MST, S<:AbsLocalizedRingElem{RT, RET, MST}, T<:RingElement} 
  AbstractAlgebra.promote_rule(RET, T) == RET ? S : Union{}
end

### default conversion passing through the base ring
(L::AbsLocalizedRing)(f::RET) where {RET<:RingElem} = L(base_ring(L)(f))
(L::AbsLocalizedRing)(f::AbsLocalizedRingElem; check::Bool=true) = L(numerator(f), denominator(f), check=check)


### Needs to be overwritten in case of zero divisors!
iszero(a::AbsLocalizedRingElem) = iszero(numerator(a))


############################################################################
# Finitely generated ideals in localized rings                             #
############################################################################

@doc raw"""
    AbsLocalizedIdeal{LocRingElemType}

Abstract type for finitely generated ideals ``I ⊂ R[S⁻¹]`` in localized rings. 
"""
abstract type AbsLocalizedIdeal{LocRingElemType} <: Ideal{LocRingElemType} end

### required getter functions
#Return a Vector of generators of `I`.
function gens(I::AbsLocalizedIdeal)
  error("`gens(I)` has not been implemented for `I` of type $(typeof(I))")
end

# Return the localized ring over which `I` is defined.
function base_ring(I::AbsLocalizedIdeal)
  error("`base_ring(I)` has not been implemented for `I` of type $(typeof(I))")
end

### required constructors
function ideal(W::AbsLocalizedRing, f)
  error("`ideal(W, f)` has not been implemented for `W` of type $(typeof(W)) and `f` of type $(typeof(f))")
end

function ideal(W::AbsLocalizedRing, v::Vector)
  error("`ideal(W, v)` has not been implemented for `W` of type $(typeof(W)) and `v` of type $(typeof(v))")
end

function (W::AbsLocalizedRing)(I::Ideal)
  return ideal(W, W.(gens(I)))
end

### required functionality
# Checks for ideal membership of `f` in `I`.
function Base.in(
    f::RingElem,
    I::AbsLocalizedIdeal
  )
  return ideal_membership(f, I)
end

function ideal_membership(
    f::RingElem,
    I::AbsLocalizedIdeal
  )
  error("`ideal_membership(f, I)` has not been implemented for `f` of type $(typeof(f)) and `I` of type $(typeof(I))")
end

function issubset(I::IdealType, J::IdealType) where {IdealType<:AbsLocalizedIdeal}
  return all(x->(x in J), gens(I))
end

function ==(I::IdealType, J::IdealType) where {IdealType<:AbsLocalizedIdeal}
  return issubset(I, J) && issubset(J, I)
end

### A catchall implementation for the ideal arithmetic 
# Return the product of the ideals `I` and `J`.
function Base.:*(I::T, J::T) where {T<:AbsLocalizedIdeal}
  W = base_ring(I) 
  W == base_ring(J) || error("the given ideals do not belong to the same ring")
  new_gens = [ f*g for f in gens(I) for g in gens(J)]
  return ideal(W, new_gens)
end

# Return the sum of the ideals `I` and `J`.
function Base.:+(I::T, J::T) where {T<:AbsLocalizedIdeal}
  W = base_ring(I) 
  W == base_ring(J) || error("the given ideals do not belong to the same ring")
  return ideal(W, vcat(gens(I), gens(J)))
end

function Base.:^(I::T, k::IntegerUnion) where {T<:AbsLocalizedIdeal}
  k >= 0 || error("exponent must be non-negative")
  R = base_ring(I)
  if k == 2
    return ideal(R, [a*b for a in gens(I) for b in gens(I)])
  elseif k == 1
    return I
  elseif k == 0
    return ideal(R, one(R))
  else
    q, r = divrem(k, 2)
    return ideal(R, [a*b for a in gens(I^q) for b in gens(I^(q+r))])
  end
end

########################################################################
# Homomorphisms of localized rings                                     #
########################################################################

@doc raw"""
    AbsLocalizedRingHom{
        DomainType<:AbsLocalizedRing,
        CodomainType<:Ring,
        RestrictedMapType
      } <: Map{
        DomainType,
        CodomainType,
        SetMap,
        AbsLocalizedRingHom
      }

Homomorphism ``ϕ : R[U⁻¹] → S`` from the localization ``R[U⁻¹]`` of type 
``DomainType`` to an arbitrary ring `S` of type `CodomainType`. Such a 
homomorphism is completely determined by its 'restriction' 
``ϕ' : R → R[U⁻¹] → S`` to the `base_ring` ``R`` before localization and 
the type parameter `RestrictedMapType` is reserved for that map. 
"""
abstract type AbsLocalizedRingHom{
                                  DomainType<:AbsLocalizedRing,
                                  CodomainType<:Ring,
                                  RestrictedMapType
                                 } <: Map{
                                          DomainType,
                                          CodomainType,
                                          SetMap,
                                          AbsLocalizedRingHom
                                         }
end


### required getter functions
@doc raw"""
    domain(f::AbsLocalizedRingHom) 

Return the domain of definition of `f`.
"""
function domain(f::AbsLocalizedRingHom) 
  error("`domain(f)` not implemented for `f` of type $(typeof(f))")
end

@doc raw"""
    codomain(f::AbsLocalizedRingHom) 

Return the codomain of `f`.
"""
function codomain(f::AbsLocalizedRingHom) 
  error("`codomain(f)` not implemented for `f` of type $(typeof(f))")
end

@doc raw"""
    restricted_map(f::AbsLocalizedRingHom) 

For a ring homomorphism ``ϕ : R[U⁻¹] → S`` return the underlying 
restriction ``ϕ' : R → S``.
"""
function restricted_map(f::AbsLocalizedRingHom) 
  error("`restricted_map(f)` not implemented for `f` of type $(typeof(f))")
end

### required functionality
@doc raw"""
    (f::AbsLocalizedRingHom)(a::T) where {T<:RingElement}

Applies the map `f` to the element `a` in the domain of `f`.
"""
function (f::AbsLocalizedRingHom)(a::AbsLocalizedRingElem)
  parent(a) === domain(f) || return f(domain(f)(a))
  return codomain(f)(restricted_map(f)(numerator(a)))*inv(codomain(f)(restricted_map(f)(denominator(a))))
end

### generic functions
(f::AbsLocalizedRingHom)(a::RingElem; check::Bool=true) = f(domain(f)(a, check=check))
(f::AbsLocalizedRingHom)(a::Integer) = f(domain(f)(a))
(f::AbsLocalizedRingHom)(a::ZZRingElem) = f(domain(f)(a))

@doc raw"""
    (f::AbsLocalizedRingHom)(I::Ideal)

Return the ideal generated by the images `f(hᵢ)` of the generators `hᵢ` of `I`.
"""
(f::AbsLocalizedRingHom)(I::Ideal) = ideal(codomain(f), f.(domain(f).(gens(I))))

### implementing the Oscar map interface
check_composable(
                 f::AbsLocalizedRingHom{D, C},
                 g::AbsLocalizedRingHom{C, E}
                ) where {C, D, E}  = (codomain(f) == domain(g))

function Base.show(io::IO, f::AbsLocalizedRingHom)
  print(io, "morphism from the localized ring $(domain(f)) to $(codomain(f))")
end

function ==(f::T, g::T) where {T<:AbsLocalizedRingHom}
  domain(f) === domain(g) || return false
  codomain(f) === codomain(g) || return false
  return restricted_map(f) == restricted_map(g)
end

function kernel(f::AbsLocalizedRingHom)
  L = domain(f)
  return ideal(L, [L(g) for g in gens(kernel(restricted_map(f)))])
end

function preimage(f::AbsLocalizedRingHom, I::Ideal)
  base_ring(I) === codomain(f) || error("ideal must be in the codomain of f")
  Q, proj = quo(codomain(f), I)
  return kernel(compose(f, proj))
end

# For the generic code we route everything through the kernel computation.
# This is different to what happens within the affine algebras where the 
# computation of kernels is rerouted to a preimage, but that shouldn't matter.
function preimage(f::MPolyAnyMap{<:Any, <:AbsLocalizedRing}, I::Ideal)
  base_ring(I) === codomain(f) || error("ideal must be in the codomain of f")
  Q, proj = quo(codomain(f), I)
  return kernel(compose(f, proj))
end

