### Production of the chains
struct ContractionChainFactory{ChainType} <: HyperComplexChainFactory{ChainType}
  # Fields needed for production
    phi::ModuleFPHom
    max::Int64

  function ContractionChainFactory(phi::ModuleFPHom; truncation::Union{Int64,Nothing} = nothing)
    # Fill in the constructor
        truncation == nothing && (truncation = ngens(domain(phi)))
        new{ModuleFP}(phi,truncation)
  end
end

function (fac::ContractionChainFactory)(self::AbsHyperComplex, I::Tuple)
  # Production of the chains at index i
    i = I[1]
    i == 0 && return codomain(fac.phi)
    M = domain(fac.phi)
    i == 1 && return M
    return exterior_power(M,i)[1]
end

function can_compute(fac::ContractionChainFactory, self::AbsHyperComplex, I::Tuple)
  # Deciding whether the entry at index i can be produced
    i = I[1]
    return (fac.max >= i) && (i >= 0)
end

### Production of the morphisms 
struct ContractionMapFactory{MorphismType} <: HyperComplexMapFactory{MorphismType}
  # Fields needed for production

  function ContractionMapFactory()
    # Fill in the constructor
        new{ModuleFPHom}()
  end
end

function (fac::ContractionMapFactory)(self::AbsHyperComplex, p::Int, I::Tuple)
  # Production of the outgoing morphism at index i in the p-th direction
    fac = chain_factory(self)
    i = I[1]
    phi = fac.phi
    dom = self[i]
    codom = self[i-1]
    i == 1 && return phi
    decomp = Oscar.wedge_generator_decompose_function(dom)
    i == 2 && return hom(dom,codom,[sum(map(j -> (-1)^(j+1)*phi(decomp(w)[j])[1]*first(decomp(w)[filter(k -> !(k == j),1:i)]),1:i)) for w in gens(dom)])
    wedge = Oscar.wedge_pure_function(codom)
    return hom(dom,codom,[sum(map(j -> (-1)^(j+1)*phi(decomp(w)[j])[1]*wedge(decomp(w)[filter(k -> !(k == j),1:i)]),1:i)) for w in gens(dom)])
end

function can_compute(fac::ContractionMapFactory, self::AbsHyperComplex, p::Int, I::Tuple)
  # Deciding whether the outgoing map at index i in the p-th direction can be produced
    fac = chain_factory(self)
    i = I[1]
    return (fac.max >= i) && (i > 0)
end

### The concrete struct
@attributes mutable struct ContractionComplex{ChainType, MorphismType} <: AbsHyperComplex{ChainType, MorphismType} 
  internal_complex::HyperComplex{ChainType, MorphismType}

  function ContractionComplex(phi::ModuleFPHom; max::Union{Int64,Nothing} = nothing)
    max == nothing && (max = ngens(domain(phi)))
    chain_fac = ContractionChainFactory(phi; truncation = max)
    map_fac = ContractionMapFactory()
    
    # Assuming d is the dimension of the new complex
    internal_complex = HyperComplex(1, chain_fac, map_fac, [:chain];lower_bounds= [0], upper_bounds = [max])
    # Assuming that ChainType and MorphismType are provided by the input
    return new{ModuleFP, ModuleFPHom}(internal_complex)
  end
end

### Implementing the AbsHyperComplex interface via `underlying_complex`
underlying_complex(c::ContractionComplex) = c.internal_complex