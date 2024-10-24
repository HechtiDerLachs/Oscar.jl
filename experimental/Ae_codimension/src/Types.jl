########################################################################
# MalgrangePreparator
#
# This is a data structure to be used for A-finite map germs 
#   f : ℂⁿ, 0 → ℂᵖ, 0,  x ↦ y = f(x)
# with p ≥ n. Let φ : R → S be the associated pullback of rings. 
# Then S ≅ M is a finite R-module. This data structure translates 
# an element in S into (a representative of) an element in M. 
#
# WARNING: The implemented algorithm makes various assumptions which 
# are not yet checked consintently! 
#
# We assume that f is surjective (i.e. m = p and no equations for the image).
# We create a polynomial ring 𝕜[x₁,…,xₙ,G₁,…,Gₘ,y₁,…,yₚ] where m is the 
# multiplicity of S over R. Then we let 
#   1 = g₁, g₂, …, gₘ ∈ S
# be elements which reduce to a 𝕜-basis of the fiber S/⟨y₁, …, yₚ⟩S
# and introduce the ideal
#
# I = ⟨yⱼ - fⱼ(x) : j = 1,…,p⟩ + ⟨Gⱼ- gⱼ : j = 1,…,m⟩
#
# and call it the "pusher ideal". Let `gb` be a Groebner basis of this 
# ideal with respect to a monomial ordering 
#
#   degrevlex(x)*degrevlex(G)*any_ordering(y)
#
# so that we have two elimination blocks: A first for the x-variables 
# and a second one for the G's.
#
# Claim: For an arbitrary element h(x) ∈ S, the reduction of h by `gb` 
# produces an element 
# 
#   v = ∑ᵢ aᵢ(y) ⋅ Gᵢ, aᵢ ∈ R
#
# where aᵢ are the coefficients of the representation of h as an element
# of the R-module M, the generators being the chosen gᵢs. 
#
# WARNING: This algorithm produces the correct result only under various 
# favorable assumptions which we still need so spell out concretely!
#
# MalgrangePreparator
#
# Input: - a map of polynomial rings f : R → S representing the pullback 
#          of the map germ 
#        - a set of generators gᵢ∈ S reducing to a 𝕜-base of the fiber 
#          S/⟨y⟩S.
#
# Output: An object `prep` which can be applied to elements h ∈ S so 
#         that `prep(h)` produces an element `v` in a free R-module `F` 
#         so that ∑ᵢf(vᵢ)⋅gᵢ = h in S.
#
########################################################################
mutable struct MalgrangePreparator{T<:MPolyRingElem}
  f::Map{<:MPolyRing, <:MPolyRing}
  g::Vector{T} # elements reducing to a base of the fiber
  SPR::Singular.PolyRing # the preparation ring
  PR::MPolyRing # the same ring on the OSCAR side
  I::Singular.sideal # the "pusher"-ideal
  x::Vector{<:Singular.spoly}
  y::Vector{<:Singular.spoly}
  G::Vector{<:Singular.spoly}
  M::FreeMod
  cod_to_PR::Map
  ext_dom::MPolyRing
  PR_to_ext_dom::Map

  function MalgrangePreparator(
      f::Map{<:MPolyRing, <:MPolyRing}, g::Vector{T}
    ) where {T<:MPolyRingElem}
    @assert is_one(first(g)) "first generator for the fiber module must be one"
    return new{T}(f, g)
  end
end

########################################################################
# MalgrangeModulePreparator
#
# Given a `MalgrangePreparator` `prep` for a map of rings f : R → S 
# as above and a free S-module `FS`, this produces an object 
# `Fprep` which realizes `FS` as a finite `R`-module `FR`. 
# The object `Fprep` can then be applied to elements of `FS` to 
# produce its corresponding element in `FR`. 
########################################################################
mutable struct MalgrangeModulePreparator{T<:MPolyRingElem}
  prep::MalgrangePreparator{T} # the internal one on the ring level
  cod_mod::FreeMod{T}
  dom_mod::FreeMod{T}
  dom_fac::FreeMod{T}
  mult_map::Map

  function MalgrangeModulePreparator(
      prep::MalgrangePreparator{T},
      F::FreeMod{T}
    ) where {T<:MPolyRingElem}
    @req base_ring(F) === codomain_ring(prep) "rings are incompatible"
    return new{T}(prep, F)
  end
end



