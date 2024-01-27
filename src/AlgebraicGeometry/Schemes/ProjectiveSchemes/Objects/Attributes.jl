export homogeneous_coordinate_ring

########################################################################
# Interface for abstract projective schemes                            #
########################################################################

@doc raw"""
    base_ring(X::AbsProjectiveScheme)

On ``X ⊂ ℙʳ_A`` this returns ``A``.
"""
base_ring(P::AbsProjectiveScheme) = base_ring(underlying_scheme(P))


@doc raw"""
    base_scheme(X::AbsProjectiveScheme)

Return the base scheme ``Y`` for ``X ⊂ ℙʳ×ₖ Y → Y`` with ``Y`` defined over a field ``𝕜``.
"""
base_scheme(P::AbsProjectiveScheme) =base_scheme(underlying_scheme(P))


@doc raw"""
    homogeneous_coordinate_ring(P::AbsProjectiveScheme)

On a projective scheme ``P = Proj(S)`` for a standard
graded finitely generated algebra ``S`` this returns ``S``.

# Example
```jldoctest
julia> S, _ = grade(QQ["x", "y", "z"][1]);

julia> I = ideal(S, S[1] + S[2]);

julia> X = ProjectiveScheme(S, I)
Projective scheme
  over rational field
defined by ideal(x + y)

julia> homogeneous_coordinate_ring(X)
Quotient
  of multivariate polynomial ring in 3 variables over QQ graded by
    x -> [1]
    y -> [1]
    z -> [1]
  by ideal(x + y)
```
"""
homogeneous_coordinate_ring(P::AbsProjectiveScheme) = homogeneous_coordinate_ring(underlying_scheme(P))


@doc raw"""
    relative_ambient_dimension(X::AbsProjectiveScheme)

On ``X ⊂ ℙʳ_A`` this returns ``r``.

# Example
```jldoctest
julia> S, _ = grade(QQ["x", "y", "z"][1]);

julia> I = ideal(S, S[1] + S[2])
ideal(x + y)

julia> X = ProjectiveScheme(S, I)
Projective scheme
  over rational field
defined by ideal(x + y)

julia> relative_ambient_dimension(X)
2

julia> dim(X)
1
```
"""
relative_ambient_dimension(P::AbsProjectiveScheme) = relative_ambient_dimension(underlying_scheme(P))

_dehomogenization_cache(X::AbsProjectiveScheme) = _dehomogenization_cache(underlying_scheme(X))
_homogenization_cache(X::AbsProjectiveScheme) = _homogenization_cache(underlying_scheme(X))

########################################################################
# Coordinates and coordinate rings
########################################################################


@doc raw"""
    ambient_coordinate_ring(P::AbsProjectiveScheme)

On a projective scheme ``P = Proj(S)`` with ``S = P/I``
for a standard graded polynomial ring ``P`` and a
homogeneous ideal ``I`` this returns ``P``.

# Example
```jldoctest
julia> S, _ = grade(QQ["x", "y", "z"][1])
(Graded multivariate polynomial ring in 3 variables over QQ, MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}[x, y, z])

julia> I = ideal(S, S[1] + S[2])
ideal(x + y)

julia> X = ProjectiveScheme(S, I)
Projective scheme
  over rational field
defined by ideal(x + y)

julia> homogeneous_coordinate_ring(X)
Quotient
  of multivariate polynomial ring in 3 variables over QQ graded by
    x -> [1]
    y -> [1]
    z -> [1]
  by ideal(x + y)

julia> ambient_coordinate_ring(X) === S
true

julia> ambient_coordinate_ring(X) === homogeneous_coordinate_ring(X)
false
```
"""
ambient_coordinate_ring(P::AbsProjectiveScheme)

ambient_coordinate_ring(P::AbsProjectiveScheme{<:Any, <:MPolyQuoRing}) = base_ring(homogeneous_coordinate_ring(P))
ambient_coordinate_ring(P::AbsProjectiveScheme{<:Any, <:MPolyDecRing}) = homogeneous_coordinate_ring(P)


function ambient_space(P::AbsProjectiveScheme{<:Any, <:MPolyDecRing})
  return P
end

@doc raw"""
    ambient_space(X::AbsProjectiveScheme)

On ``X ⊂ ℙʳ_A`` this returns ``ℙʳ_A``.

# Example
```jldoctest
julia> S, _ = grade(QQ["x", "y", "z"][1]);

julia> I = ideal(S, S[1] + S[2]);

julia> X = ProjectiveScheme(S, I)
Projective scheme
  over rational field
defined by ideal(x + y)

julia> P = ambient_space(X)
Projective space of dimension 2
  over rational field
with homogeneous coordinates [x, y, z]
```
"""
@attr function ambient_space(X::AbsProjectiveScheme)
  return projective_scheme(ambient_coordinate_ring(X))
end


@doc raw"""
    homogeneous_coordinates(X::AbsProjectiveScheme)

Return the generators of the homogeneous coordinate ring of ``X``.
"""
function homogeneous_coordinates(X::AbsProjectiveScheme)
  return gens(homogeneous_coordinate_ring(X))
end


function weights(X::AbsProjectiveScheme)
  S = homogeneous_coordinate_ring(ambient_space(X))
  A = grading_group(S)
  elementary_divisors(A)==[0] || error("not ZZ graded")
  return [degree(i)[1] for i in gens(S)]
end


##############################################################################
# Converter to covered scheme
##############################################################################

@doc raw"""
    covered_scheme(P::AbsProjectiveScheme)

Return a `CoveredScheme` ``X`` isomorphic to `P` with standard affine charts given by dehomogenization.

Use `dehomogenization_map` with `U` one of the `affine_charts` of ``X`` to
obtain the dehomogenization map from the `homogeneous_coordinate_ring` of `P`
to the `coordinate_ring` of `U`.

# Examples
```jldoctest
julia> P = projective_space(QQ, 2);

julia> Pcov = covered_scheme(P)
Scheme
  over rational field
with default covering
  described by patches
    1: affine 2-space
    2: affine 2-space
    3: affine 2-space
  in the coordinate(s)
    1: [(s1//s0), (s2//s0)]
    2: [(s0//s1), (s2//s1)]
    3: [(s0//s2), (s1//s2)]
```
"""
@attr AbsCoveredScheme function covered_scheme(P::AbsProjectiveScheme)
  #is_empty(P) && return empty_covered_scheme(base_ring(P))
  C = standard_covering(P)
  is_empty(C) && return empty_covered_scheme(base_ring(P))
  X = CoveredScheme(C)
  return X
end


@attr function covered_projection_to_base(X::AbsProjectiveScheme{<:Union{<:MPolyQuoLocRing, <:MPolyLocRing, <:MPolyQuoRing, <:MPolyRing}})
  if !has_attribute(X, :covering_projection_to_base)
    C = standard_covering(X)
  end
  covering_projection = get_attribute(X, :covering_projection_to_base)::CoveringMorphism
  projection = CoveredSchemeMorphism(covered_scheme(X), CoveredScheme(codomain(covering_projection)), covering_projection)
end



@doc raw"""
    defining_ideal(X::AbsProjectiveScheme)

On ``X ⊂ ℙʳ_A`` this returns the homogeneous
ideal ``I ⊂ A[s₀,…,sᵣ]`` defining ``X``.

# Example
```jldoctest
julia> R, (u, v) = QQ["u", "v"];

julia> Q, _ = quo(R, ideal(R, u^2 + v^2));

julia> S, _ = grade(Q["x", "y", "z"][1]);

julia> P = projective_scheme(S)
Projective space of dimension 2
  over quotient of multivariate polynomial ring by ideal(u^2 + v^2)
with homogeneous coordinates [x, y, z]

julia> defining_ideal(P)
ideal()
```
"""
defining_ideal(X::AbsProjectiveScheme)

defining_ideal(X::AbsProjectiveScheme{<:Any, <:MPolyDecRing}) = ideal(homogeneous_coordinate_ring(X), Vector{elem_type(homogeneous_coordinate_ring(X))}())
defining_ideal(X::AbsProjectiveScheme{<:Any, <:MPolyQuoRing}) = modulus(homogeneous_coordinate_ring(X))


#######################################################################
# Affine Cone
#######################################################################

@doc raw"""
    affine_cone(X::AbsProjectiveScheme)

On ``X = Proj(S) ⊂ ℙʳ_𝕜`` this returns a pair `(C, f)` where ``C = C(X) ⊂ 𝕜ʳ⁺¹``
is the affine cone of ``X`` and ``f : S → 𝒪(C)`` is the morphism of rings
from the `homogeneous_coordinate_ring` to the `coordinate_ring` of the affine cone.


Note that if the base scheme is not affine, then the affine cone is not affine.
# Example
```jldoctest
julia> R, (u, v) = QQ["u", "v"];

julia> Q, _ = quo(R, ideal(R, u^2 + v^2));

julia> S, _ = grade(Q["x", "y", "z"][1]);

julia> P = projective_scheme(S)
Projective space of dimension 2
  over quotient of multivariate polynomial ring by ideal(u^2 + v^2)
with homogeneous coordinates [x, y, z]

julia> affine_cone(P)
(V(u^2 + v^2), Map: graded multivariate polynomial ring -> quotient of multivariate polynomial ring)
```
"""
affine_cone(P::AbsProjectiveScheme)

@attr function affine_cone(
    P::AbsProjectiveScheme{RT}
  ) where {RT<:Union{MPolyRing, MPolyQuoRing, MPolyQuoLocRing, MPolyLocRing}}
  S = homogeneous_coordinate_ring(P)
  phi = RingFlattening(S)
  A = codomain(phi)
  C = Spec(A)
  B = base_scheme(P)
  P.projection_to_base = morphism(C, B, hom(OO(B), OO(C), gens(OO(C))[ngens(S)+1:end], check=false), check=false)
  return C, phi
end

@attr function affine_cone(
    P::AbsProjectiveScheme{RT, <:MPolyQuoRing}
  ) where {RT<:Union{Field, ZZRing}}
  S = homogeneous_coordinate_ring(P)
  PS = base_ring(S)
  PP = forget_grading(PS) # the ungraded polynomial ring
  I = modulus(S)
  II = forget_grading(I)
  SS, _ = quo(PP, II)
  phi = hom(S, SS, gens(SS), check=false)
  C = Spec(SS)
  return C, phi
end

@attr function affine_cone(
    P::AbsProjectiveScheme{RT, <:MPolyDecRing}
  ) where {RT<:Union{Field, ZZRing}}
  S = homogeneous_coordinate_ring(P)
  PP = forget_grading(S) # the ungraded polynomial ring
  phi = hom(S, PP, gens(PP), check=false)
  C = Spec(PP)
  return C, phi
end

@attr function affine_cone(
    X::AbsProjectiveScheme{CRT, RT}
  ) where {
           CRT<:SpecOpenRing,
           RT<:MPolyRing
          }
  S = ambient_coordinate_ring(X)
  B = coefficient_ring(S)
  Y = scheme(B)
  U = domain(B)
  R = base_ring(OO(Y))
  kk = base_ring(R)
  F = affine_space(kk, symbols(ambient_coordinate_ring(X)))
  C, pr_base, pr_fiber = product(U, F)
  X.homog_coord = [pullback(pr_fiber)(u)
                   for u in OO(codomain(pr_fiber)).(gens(OO(F)))]
  phi = hom(S, OO(C), pullback(pr_base), X.homog_coord, check=false)
  g = phi.(gens(defining_ideal(X)))
  CX = subscheme(C, g)
  X.C = CX

  psi = compose(phi, restriction_map(C, CX))
  set_attribute!(X, :base_scheme, U)
  X.projection_to_base = restrict(pr_base, CX, U, check=false)
  return X.C, psi
end

@attr function affine_cone(
    X::AbsProjectiveScheme{CRT, RT}
  ) where {
           CRT<:SpecOpenRing,
           RT<:MPolyQuoRing
          }
  P = ambient_coordinate_ring(X)
  S = homogeneous_coordinate_ring(X)
  B = coefficient_ring(P)
  Y = scheme(B)
  U = domain(B)
  R = base_ring(OO(Y))
  kk = base_ring(R)
  F = affine_space(kk, symbols(ambient_coordinate_ring(X)))
  C, pr_base, pr_fiber = product(U, F)
  homog_coord = [pullback(pr_fiber)(u)
                 for u in OO(codomain(pr_fiber)).(gens(OO(F)))]
  phi = hom(P, OO(C), pullback(pr_base), homog_coord, check=false)
  g = phi.(gens(modulus(S)))
  CX = subscheme(C, g)
  pr_base_res = restrict(pr_base, CX, codomain(pr_base), check=true)
  X.C = CX
  X.homog_coord = OO(CX).(homog_coord)

  #psi = hom(S, OO(CX), pullback(pr_base), OO(CX).(X.homog_coord), check=false)

  psi = compose(phi, restriction_map(C, CX))
  psi_res = hom(S, OO(CX), pullback(pr_base_res), X.homog_coord, check=false)
  set_attribute!(X, :base_scheme, U)
  X.projection_to_base = restrict(pr_base, CX, U, check=false)
  return X.C, psi_res
end

### TODO: Replace by the map of generators.
@doc raw"""
    homogeneous_coordinates_on_affine_cone(X::AbsProjectiveScheme)

On ``X ⊂ ℙʳ_A`` this returns a vector with the homogeneous
coordinates ``[s₀,…,sᵣ]`` as entries where each one of the
``sᵢ`` is a function on the `affine cone` of ``X``.

# Example
```jldoctest
julia> R, (u, v) = QQ["u", "v"];

julia> Q, _ = quo(R, ideal(R, u^2 + v^2));

julia> S, _ = grade(Q["x", "y", "z"][1]);

julia> P = projective_scheme(S)
Projective space of dimension 2
  over quotient of multivariate polynomial ring by ideal(u^2 + v^2)
with homogeneous coordinates [x, y, z]

julia> Oscar.homogeneous_coordinates_on_affine_cone(P)
3-element Vector{MPolyQuoRingElem{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}}:
 x
 y
 z

julia> gens(OO(affine_cone(P)[1])) # all coordinates on the affine cone
5-element Vector{MPolyQuoRingElem{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}}:
 x
 y
 z
 u
 v
```
"""
function homogeneous_coordinates_on_affine_cone(P::AbsProjectiveScheme)
  if !isdefined(P, :homog_coord)
    C, f = affine_cone(P)
    P.homog_coord = f.(gens(homogeneous_coordinate_ring(P)))
  end
  return P.homog_coord
end

homogeneous_coordinate_on_affine_cone(P::AbsProjectiveScheme, i::Int) = homogeneous_coordinates_on_affine_cone(P)[i]

########################################################################
# Methods for the concrete minimal instance                            #
########################################################################

# the documentation is for the abstract type
base_ring(P::ProjectiveScheme) = P.A

function base_scheme(X::ProjectiveScheme{CRT, RT}) where {CRT<:Ring, RT}
  if !isdefined(X, :Y)
    X.Y = Spec(base_ring(X))
  end
  return X.Y
end

function base_scheme(X::ProjectiveScheme{<:SpecOpenRing})
  return domain(base_ring(X))
end

function set_base_scheme!(
    P::ProjectiveScheme{CRT, RT},
    X::Union{<:AbsSpec, <:SpecOpen}
  ) where {CRT<:Ring, RT}
  OO(X) === base_ring(P) || error("schemes are not compatible")
  P.Y = X
  return P
end

function projection_to_base(X::ProjectiveScheme{CRT, RT}) where {CRT<:Union{<:MPolyRing, <:MPolyQuoRing, <:MPolyLocRing, <:MPolyQuoLocRing, <:SpecOpenRing}, RT}
  if !isdefined(X, :projection_to_base)
    affine_cone(X)
  end
  return X.projection_to_base
end

function _dehomogenization_cache(X::ProjectiveScheme)
  if !isdefined(X, :dehomogenization_cache)
    X.dehomogenization_cache = IdDict{AbsSpec, Map}()
  end
  return X.dehomogenization_cache
end

function _homogenization_cache(X::ProjectiveScheme)
  if !isdefined(X, :homogenization_cache)
    X.homogenization_cache = IdDict{AbsSpec, Function}()
  end
  return X.homogenization_cache
end


relative_ambient_dimension(P::ProjectiveScheme) = P.r

homogeneous_coordinate_ring(P::ProjectiveScheme) = P.S


### type getters
projective_scheme_type(A::T) where {T<:AbstractAlgebra.Ring} = projective_scheme_type(typeof(A))
projective_scheme_type(::Type{T}) where {T<:AbstractAlgebra.Ring} =
ProjectiveScheme{T, mpoly_dec_ring_type(mpoly_ring_type(T))}

base_ring_type(P::ProjectiveScheme) = base_ring_type(typeof(P))
base_ring_type(::Type{ProjectiveScheme{S, T}}) where {S, T} = S

ring_type(P::ProjectiveScheme) = ring_type(typeof(P))
ring_type(::Type{ProjectiveScheme{S, T}}) where {S, T} = T

### type constructors

# the type of a relative projective scheme over a given base scheme
projective_scheme_type(X::AbsSpec) = projective_scheme_type(typeof(X))
projective_scheme_type(::Type{T}) where {T<:AbsSpec} = projective_scheme_type(ring_type(T))


########################################################################
# Attributes for projective schemes over a field                       #
########################################################################

@attr Int function dim(P::AbsProjectiveScheme{<:Field})
  return dim(defining_ideal(P))-1
end

@attr Int function codim(P::AbsProjectiveScheme{<:Field})
  return dim(ambient_space(P)) - dim(defining_ideal(P)) + 1
end

@attr QQPolyRingElem function hilbert_polynomial(P::AbsProjectiveScheme{<:Field})
  return hilbert_polynomial(homogeneous_coordinate_ring(P))
end

@attr ZZRingElem function degree(P::AbsProjectiveScheme{<:Field})
  return degree(homogeneous_coordinate_ring(P))
end

@attr QQFieldElem function arithmetic_genus(P::AbsProjectiveScheme{<:Field})
  h = hilbert_polynomial(P)
  return (-1)^dim(P) * (first(coefficients(h)) - 1)
end

function relative_cotangent_module(X::AbsProjectiveScheme{<:Ring, <:MPolyRing})
  return relative_euler_sequence(X)[0]
end

function relative_euler_sequence(X::AbsProjectiveScheme{<:Ring, <:MPolyRing})
  S = homogeneous_coordinate_ring(X)::MPolyDecRing
  W1 = kaehler_differentials(S)
  W0 = kaehler_differentials(S, 0)
  theta = hom(W1, W0, [x*W0[1] for x in gens(S)])
  W, inc = kernel(theta)
  Z = graded_free_module(S, 0)
  inc_Z = hom(Z, W, elem_type(W)[])
  comp = ComplexOfMorphisms(ModuleFP, [inc_Z, inc, theta], typ=:cochain, seed = -1)
  return comp
end

function relative_cotangent_module(X::AbsProjectiveScheme{<:Ring, <:MPolyQuoRing})
  # We follow the common procedure. For X ↪ ℙ ⁿ we have
  #
  #                          θ
  #    0 → Ω¹ → ⊕ ⁿ⁺¹ 𝒪 (-1) → 𝒪 
  #
  # the Euler sequence. Restricting to X we get 
  #                               θ
  #    0 → Ω¹|_X → ⊕ ⁿ⁺¹ 𝒪 (-1)_X → 𝒪_X
  #
  # Then for the defining ideal I of X in ℙⁿ we obtain 
  # an exact sequence
  #
  #   I/I² → Ω¹|_X → Ω¹_X → 0.
  #
  # Note that for the associated graded modules we can 
  # not simply restrict the module for Ω¹|_X, but we have to 
  # recompute the kernel of the restricted θ.
  inc_X = ambient_embedding(X)
  phi = pullback(inc_X)
  P = codomain(inc_X)
  eu = relative_euler_sequence(P)
  W1P = eu[0]
  W1P_res, res_W1P = _change_base_ring_and_preserve_gradings(phi, W1P)
  Omega1_res, res_Omega1 = _change_base_ring_and_preserve_gradings(phi, eu[1])
  Omega0_res, res_Omega0 = _change_base_ring_and_preserve_gradings(phi, eu[2])

  theta = map(eu, 1)
  theta_res = _change_base_ring_and_preserve_gradings(phi, theta, domain_change = res_Omega1, codomain_change = res_Omega0)
  
  W1X, inc_W1X = kernel(theta_res)
  f = gens(defining_ideal(X))
  df = exterior_derivative.(f)
  @assert all(x->parent(x) === eu[1], df)

  SP = homogeneous_coordinate_ring(P)
  F = graded_free_module(SP, degree.(f))
  jac = hom(F, eu[1], df)
  jac_res = _change_base_ring_and_preserve_gradings(phi, jac, codomain_change = res_Omega1)
  img_gens = [preimage(inc_W1X, jac_res(x)) for x in gens(domain(jac_res))]
  psi = hom(domain(jac_res), W1X, img_gens)
  return cokernel(psi)
end

@doc raw"""
    genus(X::AbsProjectiveScheme{<:Field}; algorithm::Symbol=:normalization)

Given a projective curve `X` return the genus of `X`, i.e. the 
integer `p_g = p_a - delta` where `p_a` is the arithmetic genus 
and `delta` the delta-invariant of the curve.

The `algorithm` keyword can be specified to 
  - `:normalization` to go via the computation of a normalization
  - `:primary_decomposition` to proceed with a primary decomposition
Normalization is usually faster, but not always.
"""
function genus(X::AbsProjectiveScheme{<:Field}; algorithm::Symbol=:normalization)
  @req dim(X) == 1 "scheme must be one-dimensional"
  get_attribute!(X, :genus) do
    I = defining_ideal(X)
    I_sing = singular_generators(I)
    if algorithm == :normalization
      return Singular.LibNormal.genus(I_sing)
    elseif algorithm == :primary_decomposition
      return Singular.LibNormal.genus(I_sing, "prim")
    else 
      error("algorithm not recognized")
    end
  end
end

@doc raw"""
    arithmetic_genus(X::AbsProjectiveScheme{<:Field})

Given an equidimensional projective curve `X` return the arithmetic genus of `X`, i.e. the 
integer `(-1)^n (h_X(0) - 1)` where `h_X` is the Hilbert polynomial of `X` 
and `n` its dimension.
"""
@attr Int function arithmetic_genus(X::AbsProjectiveScheme{<:Field})
  A = homogeneous_coordinate_ring(X)
  h = hilbert_polynomial(A)
  n = dim(X)
  result = (-1)^n*(evaluate(h, 0) - 1)
  return Int(result) # Convert QQFieldElem to integer
end
