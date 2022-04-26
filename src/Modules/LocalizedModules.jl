export default_ordering, singular_assure, saturated_modulus, kernel, singular_gens, oscar_assure
export SubQuo

#promotion for scalar multiplication
AbstractAlgebra.promote_rule(::Type{RET}, ::Type{MET}) where {RET<:RingElem, MET<:ModuleElem} = MET

# for localizations of polynomial rings, the singular side 
# can not be filled out with fractions, but only with the 
# numerators of generators. Thus we need a specialized routine 
# for this.
function singular_assure(M::ModuleGens{T}) where {T<:MPolyLocalizedRingElem}
  isdefined(M, :SF) && isdefined(M, :S) && return
  L = base_ring(M)
  R = base_ring(L)
  F = ambient_free_module(M)
  # set up the singular side
  SR = singular_ring(R, singular(default_ordering(F))) # why does an Oscar module have a `default_ordering`?
  SF = Singular.FreeModule(SR, ngens(F))
  # applying a singular ring to a fraction clears denominators, see below.
  sgens_and_denoms = [SF(a) for a in oscar_generators(M)]
  M.SF = SF
  M.S = Singular.Module(SR, [a[1] for a in sgens_and_denoms]...)
end

function singular_gens(M::ModuleGens) 
  singular_assure(M)
  return M.S
end

function Base.iterate(L::Singular.smodule, i::Int)
  n = ngens(L)
  if i <= n 
    return L[i], i+1
  else
    return nothing
  end
end

Base.iterate(L::Singular.smodule) = iterate(L, 1)

Base.eltype(::Type{Singular.smodule}) = Singular.svector

Base.length(L::Singular.smodule) = ngens(L)

function oscar_assure(M::ModuleGens{T}) where {T<:MPolyLocalizedRingElem}
  isdefined(M, :O) && return
  L = base_ring(M)
  R = base_ring(L)
  F = ambient_free_module(M)
  M.O = [F(v) for v in singular_gens(M)]
  return 
end

function (F::FreeMod{T})(v::Singular.svector) where {T<:MPolyLocalizedRingElem}
  L = base_ring(M)
  R = base_ring(L)
  return sum([R(a)*e for (a, e) in zip(Array(v), gens(F))])
end



function (SF::Singular.FreeMod)(v::FreeModElem{T}) where {T<:MPolyLocalizedRingElem}
  F = parent(v)
  L = base_ring(F)
  R = base_ring(L)
  SR = base_ring(SF)
  # find a common denominator for the components of this generator
  d = lcm(denominator.(Vector(v)))
  new_numerators = [numerator(v[i])*divexact(d, denominator(v[i])) for i in 1:ngens(F)]
  # and return the linear combination of the new numerators together with its denominators
  return sum([SR(new_numerators[i])*gens(SF)[i] for i in 1:length(new_numerators)]), SR(d)
end

# this case is special, because it needs to also apply a shift
function (SF::Singular.FreeMod)(v::FreeModElem{T}) where {T<:MPolyLocalizedRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}
  F = parent(v)
  L = base_ring(F)
  R = base_ring(L)
  SR = base_ring(SF)
  a = point_coordinates(inverted_set(L))
  f = hom(R, R, [x-a for (x, a) in zip(gens(R), a)])

  # find a common denominator for the components of this generator
  d = lcm(denominator.(Vector(v)))
  new_numerators = [numerator(v[i])*divexact(d, denominator(v[i])) for i in 1:ngens(F)]
  # and return the linear combination of the new numerators
  return sum([SR(f(new_numerators[i]))*gens(SF)[i] for i in 1:length(new_numerators)]), SR(f(d))
end

# return the singular submodule generated by a list of elements together with its denominators
function (SF::Singular.FreeMod)(v::Vector{FreeModElem{T}}) where {T<:MPolyLocalizedRingElem}
  svd = [SF(a) for a in v]
  return Singular.Module(base_ring(SF), [a[1] for a in svd]...), [a[2] for a in svd]
end

function default_ordering(F::FreeModuleType) where {FreeModuleType<:FreeMod{<:MPolyLocalizedRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}}
  # We need to set up a free module over the polynomial ring 
  # so that the monomial ordering can be given.
  L = base_ring(F)
  R = base_ring(L)
  helperF = FreeMod(R, ngens(F))
  # TODO: Ask for a constructor of module orderings that works without setting up such a module 
  # explicitly!
  return negdegrevlex(gens(base_ring(base_ring(F))))*lex(gens(helperF))
end

# the default module ordering assumes that we're computing in a global ring
function default_ordering(F::FreeMod{T}) where {T<:MPolyLocalizedRingElem}
  # We need to set up a free module over the polynomial ring 
  # so that the monomial ordering can be given.
  L = base_ring(F)
  R = base_ring(L)
  helperF = FreeMod(R, ngens(F))
  return degrevlex(gens(base_ring(base_ring(F))))*lex(gens(helperF))
end

# given an m×n-matrix A with entries in a localization R[U⁻¹] we bring each 
# row to a common denominator 1//dᵢ ⋅ (bᵢ₁,…,bᵢₙ) and return the pair 
# (B, d) of the matrix B and the vector d.
function _clear_row_denominators(
    A::AbstractAlgebra.Generic.MatSpaceElem{RET}
  ) where {RET<:MPolyLocalizedRingElem}
  L = base_ring(A)
  R = base_ring(L)
  denom_A = denominator.(A)
  d = [lcm([denom_A[i, j] for j in 1:ncols(A)]) for i in 1:nrows(A)]
  cleared_A = MatrixSpace(R,nrows(A), ncols(A))(vcat([[numerator(A[i, j])*div(d[i], denominator(A[i,j])) for j in 1:ncols(A)] for i in 1:nrows(A)]...))
  return cleared_A, d
end

#function kernel(f::FreeModuleHom{FreeMod{BRET}, FreeMod{BRET}}) where {BRET<:MPolyLocalizedRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}
#  F = domain(f)
#  L = base_ring(F)
#  R = base_ring(L)
#  G = codomain(f)
#  point_coordinates(inverted_set(L))
#
#  A = matrix(f)
#  cleared_A, denom_A = _clear_row_denominators(A)
#  cAS = _to_singular_gens(cleared_A, shift=point_coordinates(inverted_set(L)))
#  KS = Singular.syz(cAS)
#  K = _to_oscar_gens(F, KS, denominators=denom_A)
#  return K, hom(K, F, ambient_representatives_generators(K))
#end

#function kernel(f::FreeModuleHom{FreeMod{BRET}, FreeMod{BRET}}) where {BRET<:MPolyLocalizedRingElem}
#  F = domain(f)
#  L = base_ring(F)
#  R = base_ring(L)
#  G = codomain(f)
#
#  A = matrix(f)
#  cleared_A, denom_A = _clear_row_denominators(A)
#  cAS = _to_singular_gens(cleared_A)
#  KS = Singular.syz(cAS)
#  K = _to_oscar_gens(F, KS, denominators=denom_A)
#  return K, hom(K, F, ambient_representatives_generators(K))
#end

#function kernel(f::FreeModuleHom{FreeMod{BRET}, SubQuo{BRET}}) where {BRET<:MPolyLocalizedRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}
#  F = domain(f)
#  L = base_ring(F)
#  R = base_ring(L)
#  G = codomain(f)
#
#  A = matrix(f)
#  cleared_A, denom_A = _clear_row_denominators(A)
#  A_smod = _to_singular_gens(cleared_A, shift=point_coordinates(inverted_set(L)))
#  smodulus = _to_singular_gens(ambient_free_module(G), relations(G))
#  sK = Singular.modulo(A_smod, smodulus)
#  K = _to_oscar_gens(F, sK, denominators=denom_A)
#  return K, hom(K, F, ambient_representatives_generators(K))
#end

#function kernel(f::FreeModuleHom{FreeMod{BRET}, SubQuo{BRET}}) where {BRET<:MPolyLocalizedRingElem}
#  F = domain(f)
#  L = base_ring(F)
#  R = base_ring(L)
#  G = codomain(f)
#
#  A = matrix(f)
#  cleared_A, denom_A = _clear_row_denominators(A)
#  A_smod = _to_singular_gens(cleared_A)
#  smodulus = _to_singular_gens(saturated_modulus(codomain(f)))
#  sK = Singular.modulo(A_smod, smodulus)
#  K = _to_oscar_gens(F, sK, denominators=denom_A)
#  return K, hom(K, F, ambient_representatives_generators(K))
#end

function saturated_modulus(M::SubQuo{BRET}) where {BRET<:MPolyLocalizedRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyPowersOfElement}}
  if !has_attribute(M, :saturated_modulus)
    L = base_ring(M)
    R = base_ring(L)
    A_clear, _ = ambient_representatives_generators(M)
    B_clear, _ = relations(M)
    SR = singular_poly_ring(R)
    A_mod = Singular.Module(Singular.Matrix(SR, SR.(transpose(cleared_A))))
    B_mod = Singular.Module(Singular.Matrix(SR, SR.(transpose(cleared_B))))
    AB_mod = A_mod + B_mod
    for d in denominators(inverted_set(L))
      AB_mod = Singular.saturation(AB_mod, Singular.Ideal(SR, [SR(d)]))
    end
    AB_vec = [R.(Array(AB_mod[i])) for i in 1:ngens(AB_mod)]
    F = ambient_module(M)
    B_sat = sub(F, [sum([v[i]*denom_A[i]*F[i] for i in 1:ngens(F)]) for v in AB_vec])
    set_attribute!(M, :saturated_modulus, B_sat)
  end
  return get_attribute(M, :saturated_modulus)::SubQuo{BRET}
end

function _to_singular_gens(
    A::AbstractAlgebra.Generic.MatSpaceElem{RET};
    shift=Vector{elem_type(coefficient_ring(base_ring(A)))}()
  ) where {RET<:MPolyElem}
  R = base_ring(A)
  SR = singular_poly_ring(R)
  if length(shift) > 0
    @assert length(shift) == ngens(R)
    sha = hom(R, R, [x-a for (x, a) in zip(gens(R), shift)])
    return Singular.Module(Singular.Matrix(SR, SR.(transpose(sha.(A)))))
  end
  return Singular.Module(Singular.Matrix(SR, SR.(transpose(A))))
end

function _to_singular_gens(
    F::FreeMod{T},
    v::Vector{FreeModElem{T}}
  ) where {T<:MPolyLocalizedRingElem}
  L = base_ring(F)
  R = base_ring(L)
  SR = singular_poly_ring(R)
  
  length(v) == 0 && return Singular.Module(Singular.Matrix(SR, [zero(SR) for i in 1:ngens(F)]))

  for a in v
    parent(a) === F || error("element does not belong to the correct parent")
  end

  SF = Singular.FreeModule(SR, ngens(F))
  return Singular.Module(SR, [SF(a)[1] for a in v]...)
end

function _to_oscar_gens(
    F::FreeMod{T},
    A::Singular.smodule;
    denominators=[one(base_ring(base_ring(F))) for i in 1:ngens(F)]
  ) where {T<:MPolyLocalizedRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}
  L = base_ring(F)
  R = base_ring(L)
  shainv = hom(R, R, [x+a for (x, a) in zip(gens(R), point_coordinates(inverted_set(L)))])
  A_vec = [shainv.(R.(Array(A[i]))) for i in 1:ngens(A)]
  AO = sub(F, [sum([v[i]*denominators[i]*F[i] for i in 1:ngens(F)]) for v in A_vec])
  return AO
end

# default without a shift
function _to_oscar_gens(
    F::FreeMod{T},
    A::Singular.smodule;
    denominators=[one(base_ring(base_ring(F))) for i in 1:ngens(F)]
  ) where {T<:MPolyLocalizedRingElem}
  R = base_ring(F)
  A_vec = [R.(Array(A[i])) for i in 1:ngens(A)]
  AO = sub(F, [sum([v[i]*denominators[i]*F[i] for i in 1:ngens(F)]) for v in A_vec])
  return AO
end

function Base.in(v::FreeModElem{T}, M::SubQuo{T}) where {T<:MPolyLocalizedRingElem}
  parent(v) === ambient_free_module(M) || return false
  L = base_ring(M)
  R = base_ring(L)
  SR = singular_poly_ring(R)
end

function groebner_bases(M::SubQuo{T}) where {T<:MPolyLocalizedRingElem}
  return M.groebner_basis
end

function groebner_basis(M::SubQuo{T}) where {T<:MPolyLocalizedRingElem}
  F = ambient_free_module(M)
  if !haskey(groebner_bases(M), default_ordering(F))
    L = base_ring(M)
    R = base_ring(L)
    SR = singular_poly_ring(R)
    SM = _to_singular_gens(F, ambient_representatives_generators(M))
    SMstd = Singular.std(SM)
    gbM = ModuleGens(F, SMstd)
    leadM = ModuleGens(F, Singular.lead(SMstd))
    gb = Oscar.ModuleGB(gbM, leadM, default_ordering(F))
    groebner_bases(M)[default_ordering(F)] = gb
  end
  return groebner_bases(M)[default_ordering(F)]
end


###################################################################
# 
# Maps from free modules to arbitrary modules over different rings
#
# Given any ring homomorphism φ : R → S, a free R-module F ≅ Rⁿ, 
# and a finitely presented S-module G, a morphism of R-modules 
#
#   f : F → G, v = ∑ᵢ vᵢ⋅eᵢ ↦ ∑ᵢ φ(vᵢ)⋅f(eᵢ)
#
# is completely determined by φ and the images of the generators 
# eᵢ of F. 
#
# In some cases, we really need the flexibility to allow different 
# base rings for the domain and codomain; for instance when working 
# with S a quotient ring, or a localization of R. However, we can 
# usually not assume that the coercion of elements in R to elements 
# of S is given by a map that implements any Oscar map interface. 
# Therefore, we allow maximal flexibility here and a fallback to 
# the case of modules defined over the same ring. 

############# Now covered by the FreeModuleHom ########################

########################################################################
# 
# kernel of a homomorphism f : F -> G for a free module F over a 
# localization R[U⁻¹] of a polynomial ring R.
#
# Let eᵢ be the generators of F, vᵢ ∈  G their images.
# Let F' be the free module over R such that F = F'[U⁻¹]. Similarly, 
# there exists an R-module G' such that G = G'[U⁻¹] (but usually, 
# there is no canonical choice!)
# We refer to F' and G' as the `base_ring_module`s of F and G, 
# respectively; see the documentation of the corresponding function 
# for details. 
#
# Then we can write 
#
#   vᵢ = 1//dᵢ ⋅ wᵢ  with wᵢ ∈ G' and dᵢ ∈ R
#
# which provides us with a map 
#
#   f' : F' → G',  eᵢ ↦ wᵢ.
#
# Note that f is *not* the localization of f'! Nevertheless, we have:
#
#
# Lemma: Let K ⊂ F be the kernel of f. Then K = K'[U⁻¹] where 
# K' ⊂ F' is the kernel of f'.
#
#
# proof: It is sufficient to show that for every element a ∈ K 
# without denominators we have a ∈ K'[U⁻¹]. 
# Suppose a = (a₁, a₂, …, aᵣ) ∈ K. Then 
#
#   a₁ ⋅ w₁//d₁ + a₂ ⋅ w₂//d₂ + … + aᵣ ⋅ wᵣ//dᵣ = 0 ∈ G.
#
# We may clear denominators and multiply by a further suitable 
# unit u ∈ U such that 
#
#   u ⋅ (a₁ ⋅ q₁ ⋅ w₁ + a₂ ⋅ q₂ ⋅ w₂ + … + aᵣ ⋅ qᵣ ⋅ wᵣ) = 0 ∈ G'
#
# where qᵢ = lcm(d₁,…,dᵣ)//dᵢ. Then the element 
#
#   a' := u ⋅ (a₁ ⋅ q₁, a₂ ⋅ q₂, …, aᵣ ⋅ qᵣ) ∈ K'
#
# and a = 1//(u ⋅lcm(d₁,…,dᵣ)) ⋅ a' ∈ K'[U⁻¹].                         
#                                                                      ⊡
#
# We may therefore compute K' and return its localization.

#function kernel(
#    f::FreeModuleHom{DomainType, CodomainType}
#  ) where {LRT<:MPolyLocalizedRing, DomainType<:FreeMod{LRT}, CodomainType<:ModuleFP}
#  Fl = domain(f)
#  L = base_ring(Fl)
#  Gl = codomain(f)
#  v = [f(Fl[i]) for i in 1:ngens(Fl)]
#  w, d = clear_denominators(v)
#  F = base_ring_module(Fl)
#  G = base_ring_module(Gl)
#  g = hom(F, G, w)
#  set_attribute!(f, :base_ring_map, g)
#  K, inc = kernel(g)
#  u = [sum([u[i]*d[i]*Fl[i] for i in 1:ngens(Fl)]) for u in ambient_representatives_generators(K)]
#  Kl = SubQuo(Fl, u)
#  set_attribute!(Kl, :base_ring_module, K)
#  set_attribute!(Kl, :denominators, d)
#  return Kl, hom(Kl, Fl, ambient_representatives_generators(Kl))
#end

@doc Markdown.doc"""
    base_ring_map(
        f::FreeModuleHom{DomainType, CodomainType}
      ) where {LRT<:MPolyLocalizedRing, DomainType<:FreeMod{LRT}, CodomainType<:ModuleFP}

Let ``f : F → G`` be a map from a free module ``F`` over a localization ``R[U⁻¹]`` 
of a polynomial ring ``R``. Let ``eᵢ`` be the generators of ``F``, ``vᵢ ∈  G`` their images.
Let ``F'`` be the free module over ``R`` such that ``F = F'[U⁻¹]``. Similarly, 
there exists an ``R``-module ``G'`` such that ``G = G'[U⁻¹]`` (but usually, 
there is no canonical choice!). We refer to ``F'`` and ``G'`` as the 
`base_ring_module`s of ``F`` and ``G``, respectively; see the documentation 
of the corresponding function for details. 

Then we can `clear_denominators` and write 

  ``vᵢ = 1//dᵢ ⋅ wᵢ``  with ``wᵢ ∈ G'`` and ``dᵢ ∈ R``

(for some minimal ``dᵢ``) which provides us with a map 

  ``f' : F' → G',  eᵢ ↦ wᵢ``.

This procedure returns the map ``f'``.

**Warning**: In general, the `base_ring_map` involves choices. When using it, make 
sure the final output does not depend on these!
"""
function base_ring_map(
    f::FreeModuleHom{DomainType, CodomainType}
  ) where {LRT<:MPolyLocalizedRing, DomainType<:FreeMod{LRT}, CodomainType<:ModuleFP}
  if !has_attribute(f, :base_ring_map)
    Fl = domain(f)
    L = base_ring(Fl)
    Gl = codomain(f)
    v = [f(Fl[i]) for i in 1:ngens(Fl)]
    w, d = clear_denominators(v)
    F = base_ring_module(Fl)
    G = base_ring_module(Gl)
    g = hom(F, G, w)
    set_attribute!(f, :base_ring_map, g)
  end
  return get_attribute(f, :base_ring_map)::morphism_type(base_ring_module_type(domain(f)), base_ring_module_type(codomain(f)))
end

# the associated module over the base ring is stored as an attribute; 
# no new fields required, but type stability provided by assertion via type getters.
function base_ring_module(F::FreeMod{T}) where {T<:MPolyLocalizedRingElem}
  if !has_attribute(F, :base_ring_module) 
    L = base_ring(F)
    R = base_ring(L)
    Fb = FreeMod(R, ngens(F))
    set_attribute!(F, :base_ring_module, Fb)
  end
  return get_attribute(F, :base_ring_module)::base_ring_module_type(F)
end

base_ring_type(::Type{FreeMod{T}}) where {T<:MPolyLocalizedRingElem} = parent_type(T)
base_ring_type(F::FreeMod{T}) where {T<:MPolyLocalizedRingElem} = base_ring_type(typeof(F))


function map_from_base_ring_module(F::FreeMod{<:MPolyLocalizedRingElem})
  if !has_attribute(F, :map_from_base_ring_module)
    L = base_ring(F)
    R = base_ring(L)
    Fb = base_ring_module(F)
    h = hom(Fb, F, gens(F), L)
    set_attribute!(F, :map_from_base_ring_module, h)
  end
  return get_attribute(F, :map_from_base_ring_module)::morphism_type(typeof(F), base_ring_module_type(F), typeof(L))
end

base_ring_module_type(::Type{FreeMod{T}}) where {T<:AbsLocalizedRingElem} = FreeMod{base_ring_type(parent_type(T))}
base_ring_module_type(F::FreeMod{T}) where {T<:AbsLocalizedRingElem} = base_ring_module_type(typeof(F))


### Translations for SubQuos

function SubQuo(F::FreeMod{T}, g::Vector{FreeModElem{T}}, q::Vector{FreeModElem{T}}) where {T<:RingElem} 
  return SubQuo(Oscar.SubModuleOfFreeModule(F, g), Oscar.SubModuleOfFreeModule(F, q))
end

function base_ring_module(M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  if !has_attribute(M, :base_ring_module) 
    L = base_ring(M)
    R = base_ring(L)
    g, d = clear_denominators(ambient_representatives_generators(M))
    q, _ = clear_denominators(relations(M))
    F = ambient_free_module(M)
    Fb = base_ring_module(F)
    Mb = SubQuo(Fb, g, q)
    set_attribute!(M, :base_ring_module, Mb)
    # TODO: Also build and cache the canonical map 
    # Mb → M for the given denominators d, once the 
    # required type exists.
    # For now, we do a manual storage of this data:
    set_attribute!(M, :generator_denominators, d)
  end
  return get_attribute(M, :base_ring_module)::base_ring_module_type(M)
end

base_ring_module_type(::Type{SubQuo{T}}) where {T<:AbsLocalizedRingElem} = SubQuo{base_ring_elem_type(T)}
base_ring_module_type(F::SubQuo{T}) where {T<:AbsLocalizedRingElem} = base_ring_module_type(typeof(F))


function generator_denominators(M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  if !has_attribute(M, :generator_denominators)
    base_ring_module(M)
  end
  return get_attribute(M, :generator_denominators)::Vector{elem_type(base_ring(base_ring(M)))}
end

@Markdown.doc """
    saturated_module(M::SubQuo{T}) where {T<:AbsLocalizedRingElem}

Suppose ``M = M₀[U⁻¹]`` is a localized `SubQuo` over ``L = R[U⁻¹]`` for 
some `base_ring_module` ``M₀`` over ``R``. Then ``M₀ = (G + Q) / Q`` 
for submodules ``G`` and ``Q`` of some free ``R``-module ``F``. 
Let ``Q' = {v ∈ F : ∃ u ∈ U : u⋅v ∈ Q}`` be the saturation of ``Q`` at ``U``
and let ``G'⊂ F`` be a submodule such that ``G' + Q'`` is the saturation 
of ``G + Q`` at ``U``. Then for fixed sets of generators ``fᵢ`` of ``G'`` 
and ``gⱼ`` of ``G`` there exist units ``uᵢ ∈ U`` and a matrix 
``A ∈ Rᵐˣⁿ`` such that ``uᵢ⋅fᵢ ≡ ∑ⱼaⱼᵢ⋅gⱼ mod Q'``.

This procedure returns the `SubQuo` ``(G' + Q')/Q'``. The transition 
information ``(u, A)`` can be asked for via `saturation_transitions(M)`.
"""
function saturated_module(M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  if !has_attribute(M, :saturated_module)
    L = base_ring(M)
    R = base_ring(L)
    Mb = base_ring_module(M)
    U = inverted_set(L)
    Mb_sat, u, A = saturation(Mb, U)
    set_attribute!(M, :saturated_module, Mb_sat)
    set_attribute!(M, :saturation_transitions, (u, A))
  end
  return get_attribute(M, :saturated_module)::SubQuo{base_ring_elem_type(T)}
end

base_ring_elem_type(::Type{T}) where {BRT, BRET, T<:AbsLocalizedRingElem{BRT, BRET}} = BRET
base_ring_type(::Type{T}) where {BRT, BRET, T<:AbsLocalizedRingElem{BRT, BRET}} = BRT

base_ring_elem_type(L::AbsLocalizedRing) = base_ring_elem_type(typeof(L))
base_ring_type(L::AbsLocalizedRing) = base_ring_type(typeof(L))

function saturation_transitions(M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  if !has_attribute(M, :saturation_transitions)
    saturated_module(M)
  end
  return get_attribute(M, :saturation_transitions)::Tuple{Vector{base_ring_elem_type(T)}, dense_matrix_type(base_ring_elem_type(T))}
end

@Markdown.doc """
    saturation(G::Oscar.SubModuleOfFreeModule{T}, U::AbsMultSet) where {T<:RingElem}

For a submodule ``G ⊂ F ≅ Rʳ`` with generators ``gⱼ``, ``j = 1,…,m`` and a 
multiplicative set ``U ⊂ R`` this computes a set of generators ``fᵢ``, ``i = 1,…,n``
for the submodule

    G' = { v ∈ F : ∃ u ∈ U : u ⋅ v ∈ G}

and returns the triple ``(G', u, A)`` where ``u = (u₁,…,uₙ) ∈ Uⁿ`` is a vector and 
``A = (aᵢⱼ) ∈ Rᵐˣⁿ`` is a matrix such that ``uᵢ⋅fᵢ = ∑ⱼ aᵢⱼ⋅ gⱼ``.
"""
function saturation(G::Oscar.SubModuleOfFreeModule{T}, U::AbsMultSet) where {T<:RingElem}
  error("not implemented; see the documentation for the required functionality")
end

function saturation(G::Oscar.SubModuleOfFreeModule{T}, Q::Oscar.SubModuleOfFreeModule{T}, U::AbsMultSet) where {T<:RingElem}
  error("not implemented; see the documentation for the required functionality")
end

### coercion of elements from the base_ring_module and its ambient free module
function (M::SubQuo{T})(a::SubQuoElem) where {T<:AbsLocalizedRingElem}
  L = base_ring(M)
  Mb = base_ring_module(M)
  parent(a) === Mb || return M(Mb(a))
  d = generator_denominators(M)
  v = [a[i] for i in 1:ngens(Mb)]
  return sum([v*d*e for (v,d,e) in zip(v, d, gens(M))])
end

function (M::SubQuo{T})(a::FreeModElem) where {T<:AbsLocalizedRingElem}
  L = base_ring(M)
  Mb = base_ring_module(M)
  parent(a) === ambient_free_module(Mb) || return M(ambient_free_module(Mb)(a))
  d = generator_denominators(M)
  v = coordinates(a, Mb)
  return sum([v*d*e for (v,d,e) in zip(v, d, gens(M))])
end

#function coordinates(a::FreeModElem{T}, M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
#  L = base_ring(M)
#  b, d = clear_denominators(a)
#  Mb = base_ring_module(M)
#  Mb_sat = saturated_module(M)
#  (u, A) = saturation_transitions(M)
#  denom_g = generator_denominators(M)
#  c = coordinates(b, Mb_sat)
#  res = [sum([L(c[i]*A[i,j]*denom_g[j], u[i], check=false) for i in 1:ngens(Mb_sat)]) for j in 1:ngens(M)]
#  return sparse_row(L, [(i, c) for (i, c) in zip(1:length(res), res) if !iszero(c)])
#end

# internal routine to get rid of denominators. 
# returns a pair of an element in the associated base_ring_module and the 
# denominator pulled out of the components
function clear_denominators(v::FreeModElem{<:MPolyLocalizedRingElem})
  F = parent(v)
  L = base_ring(F)
  R = base_ring(L)
  d = lcm(denominator.(Vector(v)))
  u = elem_type(R)[]
  for a in Vector(v)
    push!(u, numerator(a)*div(d, denominator(a)))
  end
  Fb = base_ring_module(F)
  return sum([a*e for (a, e) in zip(u, gens(Fb))]), d
end

function clear_denominators(v::Vector{FreeModElem{RET}}) where {RET<:MPolyLocalizedRingElem}
  u = clear_denominators.(v)
  return [a[1] for a in u], [a[2] for a in u]
end


### Special tensor product routines for localizations of modules.
# They return the associated module over the localized ring
function tensor_product(L::AbsLocalizedRing, G::FreeMod)
  R = base_ring(L)
  R == base_ring(G) || error("no canonical map provided from the base ring of the module to the new ring")
  F = FreeMod(L, ngens(G))
  set_attribute!(F, :base_ring_module, G)
  return F, hom(G, F, gens(F), L)
end
  
function tensor_product(L::AbsLocalizedRing, G::SubQuo)
  R = base_ring(L)
  R == base_ring(G) || error("no canonical map provided from the base ring of the module to the new ring")
  F = ambient_free_module(G)
  Fl = FreeMod(L, ngens(F))
  set_attribute!(Fl, :base_ring_module, F)
  inc_F = hom(F, Fl, gens(Fl), L)
  Gl = SubQuo(Fl, inc_F.(ambient_representatives_generators(G)))
  if length(relations(G)) > 0 
    error("conversion of SubQuos with nontrivial relations not implemented")
  end
  set_attribute!(Gl, :base_ring_module, G)
  return Gl #TODO: add the inclusion morphism once the required type exists.
end
  
function _minimal_power_such_that(f::RingElemType, P::PropertyType) where {RingElemType<:RingElem, PropertyType}
  P(one(parent(f))) && return (0, one(f))
  P(f) && return (1, f)
  f_powers = [(1,f)]

  while !P(last(f_powers)[2])
    push!(f_powers, (last(f_powers)[1]*2, last(f_powers)[2]^2))
  end
  upper = pop!(f_powers)
  lower = pop!(f_powers)
  while upper[1]!=lower[1]+1
    middle = pop!(f_powers)
    middle = (lower[1]+middle[1], lower[2]*middle[2])
    if P(middle[2])
      upper = middle
    else
      lower = middle
    end
  end
  return upper
end

### Some additional getters, so that I don't have to write G.(...) 
generating_submodule(G::SubQuo) = G.sub

function modulus(G::SubQuo) 
  if isdefined(G, :quo) 
    return G.quo
  end
  return nothing
end

Oscar.SubModuleOfFreeModule(F::FreeMod) = Oscar.SubModuleOfFreeModule(F, Vector{elem_type(F)}())
module_gens(M::Oscar.SubModuleOfFreeModule) = M.gens
ambient_free_module(M::Oscar.SubModuleOfFreeModule) = M.F

function Base.in(v::FreeModElem{T}, M::Oscar.SubModuleOfFreeModule{T}) where {T<:MPolyElem}
  v in ambient_free_module(M) || return false
  return iszero(Oscar.reduce(v, groebner_basis(M)))
end
  
#function coordinates(v::FreeModElem{T}, M::Oscar.SubModuleOfFreeModule{T}) where {T<:MPolyElem}
#  if iszero(v)
#    return sparse_row(base_ring(parent(v)))
#  end
#  F = ambient_free_module(M)
#  R = base_ring(M)
#  g = module_gens(M)
#  oscar_assure(g)
#  S = singular_generators(g)
#  b = Oscar.ModuleGens([v], F)
#  singular_assure(b)
#  s, r = Singular.lift(S, singular_generators(b))
#  if Singular.ngens(s) == 0 || iszero(s[1])
#    return nothing
#  end
#  return sparse_row(R, s[1], 1:ngens(M))
#end

function saturation(
    M::SubQuo{T},
    U::MPolyPowersOfElement{<:Any, <:Any, <:Any, T}
  ) where {T<:MPolyElem}
  R = base_ring(M)
  R === ambient_ring(U) || error("multiplicative set does not belong to the base_ring of the module")
  d = denominators(U)
  Qsat = modulus(M)
  for f in d
    Qsat = sat(Qsat, ideal(R, [f]))[1]
  end
  GQsat = sum(generating_submodule(M), modulus(M))
  for f in d
    GQsat = sat(GQsat, ideal(R, [f]))[1]
  end
  V = gens(GQsat)
  f = prod(d)
  U = [_minimal_power_such_that(f, (x->(represents_element(x*v, M))))[2] for v in V]
  g = ambient_representatives_generators(M)
  n = length(g)
  m = length(V)
  A = zero(MatrixSpace(R, m, n))
  for i in 1:m
    w = coordinates(U[i]*V[i], M)
    for j in 1:n
      A[i, j] = w[j]
    end
  end
  return SubQuo(GQsat, Qsat), U, A
end

function saturation(G::Oscar.SubModuleOfFreeModule{T}, U::MPolyPowersOfElement) where {T<:MPolyElem}
  R = base_ring(G)
  R === ambient_ring(U) || error("multiplicative set does not belong to the base_ring of the module")
  d = denominators(U)
  Gsat = G
  for f in d
    Gsat = sat(Gsat, ideal(R, [f]))[1]
  end
  V = gens(Gsat)
  f = prod(d)
  U = [_minimal_power_such_that(f, (x->(x*v in G)))[2] for v in V]
  g = gens(G)
  n = length(g)
  m = length(V)
  A = zero(MatrixSpace(R, m, n))
  for i in 1:m
    w = coordinates(U[i]*V[i], G)
    for j in 1:n
      A[i, j] = w[j]
    end
  end
  return Gsat, U, A
end

# A wrapper for the singular functionality
function sat(G::Oscar.SubModuleOfFreeModule{T}, J::MPolyIdeal{T}) where {T<:MPolyElem}
  R = base_ring(G)
  g = module_gens(G)
  singular_assure(g)
  gS = singular_gens(g)
  S = singular_poly_ring(R)
  JS = Singular.Ideal(S, S.(gens(J)))
  (gS_sat, k) = Singular.LibElim.sat(S, gS, JS)
  g_sat = Oscar.ModuleGens(ambient_free_module(G), gS_sat)
  G_sat = Oscar.SubModuleOfFreeModule(ambient_free_module(G), g_sat)
  return G_sat, k
end

