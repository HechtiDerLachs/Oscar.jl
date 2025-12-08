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
    M_tensor_R = codomain(Oscar.projection(T,(1,0)))
    M = get_attribute(M_tensor_R, :tensor_product)[1]
    dh = exterior_derivative(h; parent = M)
    comps = []
    for j1 in 1:length(dom_inds)
        for j2 in 1:length(codom_inds)
        	@show dom_inds[j1],codom_inds[j2]
            proj = projs[j1]
            dom = codomain(proj)
            inj = injs[j2]
            codom = domain(inj)
            disc = (collect(codom_inds[j2]) - collect(dom_inds[j1]))[2]
            if disc == 0
            	@show "there is wedging to do"
            	dom_power = dom_inds[j1][1]
            	comp = Oscar.tensor_pure_function(codom)
                dom_factors = get_attribute(dom, :tensor_product)
                @show dom_factors
                codom_factors = get_attribute(codom, :tensor_product)
                @show codom_factors
                if dom_power == 0
        	    	wdg = hom(dom_factors[1], codom_factors[1], [dh])
        	    else
        	    	wdg = Oscar.wedge_multiplication_map(dom_factors[1],codom_factors[1],dh)
        	    end
        	    id = hom(dom_factors[2],codom_factors[2],gens(codom_factors[2]))
                m = hom_tensor(dom,codom,[wdg,id])
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
