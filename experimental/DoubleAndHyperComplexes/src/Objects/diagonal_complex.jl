#helper function; wedges an element of the i-th exterior power of a module M by the element dw of M
function wedge_morphism(dw,i)
    M = parent(dw)
    n = ngens(M)
    i == 0 && return hom(free_module(base_ring(M),1),M,[dw])
    codom = exterior_power(M,i+1)[1]
    wedge = Oscar.wedge_pure_function(codom)
    i == 1 && return hom(M,codom, [wedge(Tuple([dw,v])) for v in gens(M)])
    dom = exterior_power(M,i)[1]
    decomp = Oscar.wedge_generator_decompose_function(dom)
    return hom(dom,codom,[wedge(Tuple(vcat([dw],collect(decomp(phi))))) for phi in gens(dom)])
end

### Production of the chains
struct DiagonalChainFactory{ChainType} <: HyperComplexChainFactory{ChainType}
  # Fields needed for production
    T::TotalComplex
    

  function DiagonalChainFactory(T::TotalComplex)
    # Fill in the constructor
        new{ModuleFP}(T)
  end
end

function (fac::DiagonalChainFactory)(self::AbsHyperComplex, i::Tuple)
  # Production of the chains at index i
    return fac.T[i[1] - i[2]]
end

function can_compute(fac::DiagonalChainFactory, self::AbsHyperComplex, i::Tuple)
  # Deciding whether the entry at index i can be produced
    return ((i[1] - i[2]) in range(fac.T)) && (i[2] >= 0)
end

### Production of the morphisms 
struct DiagonalMapFactory{MorphismType} <: HyperComplexMapFactory{MorphismType}
  # Fields needed for production

  function DiagonalMapFactory()
    # Fill in the constructor
        new{ModuleFPHom}()
  end
end

function (fac::DiagonalMapFactory)(self::AbsHyperComplex, p::Int, i::Tuple)
  # Production of the outgoing morphism at index i in the p-th direction
    fac = chain_factory(self)
    T = fac.T
    p == 1 && return map(T,i[1] - i[2])
    dom_inds = Oscar.indices_in_summand(T,i[1] - i[2])
    codom_inds = Oscar.indices_in_summand(T,i[1] - i[2] + 1)
    projs = map(t -> Oscar.projection(T,t),dom_inds)
    injs = map(t -> Oscar.injection(T,t),codom_inds)
    h = map(T,1)(gens(T[1])[end])[1]
    R = base_ring(T[1])
    PolyRing = base_ring(R)
    M_tensor_R = codomain(Oscar.projection(T,(1,0)))
    decomp = Oscar.tensor_generator_decompose_function(M_tensor_R)
    M = parent(decomp(M_tensor_R[1])[1])
    dh = sum(map(i -> derivative(PolyRing(h),PolyRing(gens(R)[i]))*gens(M)[i],1:ngens(M)))
    comps = []
    for j1 in 1:length(dom_inds)
        for j2 in 1:length(codom_inds)
            proj = projs[j1]
            dom = codomain(proj)
            inj = injs[j2]
            codom = domain(inj)
            disc = (collect(codom_inds[j2]) - collect(dom_inds[j1]))[2]
            if disc == 0
                wedg = wedge_morphism(dh,dom_inds[j1][1])
                comp = Oscar.tensor_pure_function(codom)
                decomp = Oscar.tensor_generator_decompose_function(dom)
                m = hom(dom,codom,map(comp,map(g -> (wedg(g[1]),g[2]),map(decomp,gens(dom)))))
                push!(comps,compose(proj,compose(m,inj)))
            else
                push!(comps, compose(proj,compose(hom(dom,codom,[zero(codom) for w in gens(dom)]),inj)))
            end
        end
    end
    dom = domain(projs[1])
    codom = codomain(injs[1])
    return hom(dom,codom,[sum(map(f -> f(w),comps)) for w in gens(dom)])
end

function can_compute(fac::DiagonalMapFactory, self::AbsHyperComplex, p::Int, i::Tuple)
  # Deciding whether the outgoing map at index i in the p-th direction can be produced
    fac = chain_factory(self)
    p == 1 && return (i[1] - i[2] > 0) && ((i[1] - i[2]) in range(fac.T)) && (i[2] >= 0)
    return (i[2] > 0) && ((i[1] - i[2]) in range(fac.T)) && (i[1] - i[2] < range(fac.T)[1])
end

### The concrete struct
@attributes mutable struct DiagonalComplex{ChainType, MorphismType} <: AbsHyperComplex{ChainType, MorphismType} 
  internal_complex::HyperComplex{ChainType, MorphismType}

  function DiagonalComplex(T::TotalComplex)
    chain_fac = DiagonalChainFactory(T)
    map_fac = DiagonalMapFactory()

    # Assuming d is the dimension of the new complex
    internal_complex = HyperComplex(2, chain_fac, map_fac, [:chain for i in 1:2]; lower_bounds = [0,0])
    # Assuming that ChainType and MorphismType are provided by the input
    return new{ModuleFP, ModuleFPHom}(internal_complex)
  end
end

### Implementing the AbsHyperComplex interface via `underlying_complex`
underlying_complex(c::DiagonalComplex) = c.internal_complex
