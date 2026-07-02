# This is a take at implementing https://stacks.math.columbia.edu/tag/07MB, 
# the cup product for (cohomology of) coherent sheaves.
struct CupProductMorphismFactory{MorphismType} <: HyperComplexMorphismFactory{MorphismType}
  F::AbsHyperComplex
  G::AbsHyperComplex
  cech_gens::Vector
  k::Int
  cech_complex::AbsHyperComplex
  cech_F::AbsHyperComplex
  cech_G::AbsHyperComplex
  tot_cech_F::AbsHyperComplex
  tot_cech_G::AbsHyperComplex


  function CupProductMorphismFactory(
      F::AbsHyperComplex{CT, MT},
      G::AbsHyperComplex{CT, MT},
      reduced_cech_gens::Vector{ET}, 
      k::Int
    ) where {CT, MT, ET}
    S = parent(first(reduced_cech_gens))
    K = shift(HomogKoszulComplex(S, elem_type(S)[x^k for x in reduced_cech_gens])[1:length(reduced_cech_gens)], 1)
    cech_F = hom(K, F)
    cech_G = hom(K, G)
    return new{MT}(F, G, reduced_cech_gens, k, K, cech_F, cech_G, total_complex(cech_F), total_complex(cech_G))
  end
end

function (fac::CupProductMorphismFactory)(self::AbsHyperComplexMorphism, i::Tuple)
  # Implement the production of the outgoing map
end

function can_compute(fac::CupProductMorphismFactory, self::AbsHyperComplexMorphism, i::Tuple)
  # Decide whether the outgoing map from index i can be computed
end


@attributes mutable struct CupProductMorphism{DomainType, CodomainType, MorphismType} <: AbsHyperComplexMorphism{DomainType, CodomainType, MorphismType, CupProductMorphism{DomainType, CodomainType, MorphismType}}
  internal_morphism::HyperComplexMorphism{DomainType, CodomainType, MorphismType}

  function CupProductMorphism(
      F::AbsHyperComplex{CT, MT},
      G::AbsHyperComplex{CT, MT},
      reduced_cech_gens::Vector{ET}, 
      k::Int
    ) where {CT<:FreeMod, MT<:FreeModuleHom, ET<:MPolyDecRingElem}
    @assert is_one(dim(F)) && is_one(dim(G))
    map_factory = CupProductMorphismFactory(F, G, reduced_cech_gens, k)

    dom = total_complex(tensor_product(map_factory.tot_cech_F, map_factory.tot_cech_G))
    # do we need to do bigger exponent here?
    cod = total_complex(hom(map_factory.cech_complex, tensor_product(F, G)))
    internal_morphism = HyperComplexMorphism(dom, cod, map_factory, cached=true, offset=[0])
    # Assuming that the types have been extracted from the input
    return new{typeof(dom), typeof(cod), MT}(internal_morphism)
  end
end

underlying_morphism(phi::CupProductMorphism) = phi.internal_morphism

