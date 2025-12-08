#=
# Since some code coverage tool blocks the tests from passing if this file is 
# present with proper julia code inside, the code below is commented out. 
#
# If you want to implement your own hyper complex class, you may start with 
# the template below and replace every occurrence of `Wedge` with your favourite
# name for your new class. Then you have to fill in the gaps according to your 
# needs. We provide a sample implementation below.
=#

### Production of the chains
struct WedgeChainFactory{ChainType} <: HyperComplexChainFactory{ChainType}
  # Fields needed for production
    w::ModuleFPElem

  function WedgeChainFactory(w::ModuleFPElem)
    # Fill in the constructor
        new{ModuleFP}(w)
  end
end

function (fac::WedgeChainFactory)(self::AbsHyperComplex, I::Tuple)
  # Production of the chains at index i
    M = parent(fac.w)
    i = I[1]
    R = free_module(base_ring(M),1)
    n = ngens(M)
    i == n && return R
    i == n-1 && return M
    return exterior_power(M,n-i)[1]
end

function can_compute(fac::WedgeChainFactory, self::AbsHyperComplex, I::Tuple)
  # Deciding whether the entry at index i can be produced
    M = parent(fac.w)
    i = I[1]
    return (ngens(M) >= i) && (i >= 0)
end

### Production of the morphisms 
struct WedgeMapFactory{MorphismType} <: HyperComplexMapFactory{MorphismType}
  # Fields needed for production

  function WedgeMapFactory()
    # Fill in the constructor
        new{ModuleFPHom}()
  end
end

function (fac::WedgeMapFactory)(self::AbsHyperComplex, p::Int, I::Tuple)
  # Production of the outgoing morphism at index i in the p-th direction
    fac = chain_factory(self)
    w = fac.w
    i = I[1]
    dom = self[i]
    codom = self[i-1]
    M = self[1]
    n = ngens(M)
    i == n && return hom(dom,codom,[w])
    wedge = Oscar.wedge_pure_function(codom)
    i == n-1 && return hom(dom,codom, [wedge(Tuple([w,v])) for v in gens(dom)])
    decomp = Oscar.wedge_generator_decompose_function(dom)
    return hom(dom,codom,[wedge(Tuple(vcat([w],collect(decomp(phi))))) for phi in gens(dom)])
end

function can_compute(fac::WedgeMapFactory, self::AbsHyperComplex, p::Int, I::Tuple)
  # Deciding whether the outgoing map at index i in the p-th direction can be produced
    fac = chain_factory(self)
    M = parent(fac.w)
    i = I[1]
    return (ngens(M) >= i) && (i > 0)
end

### The concrete struct
@attributes mutable struct WedgeComplex{ChainType, MorphismType} <: AbsHyperComplex{ChainType, MorphismType} 
  internal_complex::HyperComplex{ChainType, MorphismType}

  function WedgeComplex(w::ModuleFPElem)
    chain_fac = WedgeChainFactory(w)
    map_fac = WedgeMapFactory()
    M = parent(w)

    # Assuming d is the dimension of the new complex
    internal_complex = HyperComplex(1, chain_fac, map_fac, [:cochain]; lower_bounds = [0], upper_bounds = [ngens(M)])
    # Assuming that ChainType and MorphismType are provided by the input
    return new{ModuleFP, ModuleFPHom}(internal_complex)
  end
end

### Implementing the AbsHyperComplex interface via `underlying_complex`
underlying_complex(c::WedgeComplex) = c.internal_complex