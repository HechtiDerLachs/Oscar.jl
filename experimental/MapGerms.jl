export AbsMapGerm, MapGerm
export domain_ring, codomain_ring, ground_field
export is_finite, is_A_finite
export pushforward

abstract type AbsMapGerm{FuncType<:RingElem, DomainRingType<:Ring, CodomainRingType<:Ring} end

@attributes mutable struct MapGerm{FuncType, DomainRingType, CodomainRingType} <: AbsMapGerm{FuncType, DomainRingType, CodomainRingType}
  f::Vector{FuncType}
  ground_field::Symbol # real or complex 
  domain_ring::DomainRingType
  codomain_ring::CodomainRingType
  graph_ring::Ring
  graph_ideal::Ideal
  dom_to_graph::Map
  cod_to_graph::Map
  pullback::Map

  ### Fields for caching
  A_tangent_space_complement_generators::Vector # Check with Juanjo what are the names! 
  is_finite::Bool


  function MapGerm(f::Vector{FuncType}; 
      domain_point::Vector=_domain_point(f),
      ground_field::Symbol=:complex, 
      domain_ring::Ring=_domain_ring(f, domain_point),
      codomain_ring::Ring=_codomain_ring(f, _codomain_point(f, domain_point))
    ) where {FuncType<:RingElem}
    ground_field == :complex || ground_field == :real || error("given symbol for the ground field is not supported")

    length(f) == 0 && error("no components of the map given")
    all(x->(parent(x)==parent(f[1])), f) || error("functions do not belong to the same ring")
    R = base_ring(domain_ring)
    kk = coefficient_ring(R)
    P, _ = PolynomialRing(kk, vcat(symbols(base_ring(domain_ring)), symbols(base_ring(codomain_ring))))
    graph_ring, _ = Localization(P, complement_of_ideal(P, vcat(domain_point, _codomain_point(f, domain_point))))
    dom_to_graph = hom(domain_ring, graph_ring, gens(base_ring(graph_ring))[1:ngens(base_ring(domain_ring))])
    cod_to_graph = hom(codomain_ring, graph_ring, gens(base_ring(graph_ring))[ngens(base_ring(domain_ring))+1:end])
    graph_ideal = ideal(graph_ring, [cod_to_graph(y) - dom_to_graph(g) for (y, g) in zip(gens(base_ring(codomain_ring)), f)])

    pullback = hom(codomain_ring, domain_ring, f)
    
    return new{typeof(f[1]), typeof(domain_ring), 
               typeof(codomain_ring)
              }(f, ground_field, domain_ring, 
                codomain_ring, graph_ring, 
                graph_ideal, dom_to_graph, 
                cod_to_graph, pullback
               )
  end
end 

### Essential getter methods

function domain_ring(F::MapGerm)
  return F.domain_ring
end

codomain_ring(F::MapGerm) = F.codomain_ring
ground_field(F::MapGerm) = F.ground_field
getindex(F::MapGerm, i::Int) = F.f[i]
components(F::MapGerm) = F.f

graph_ring(F) = F.graph_ring
graph_ideal(F) = F.graph_ideal
dom_to_graph(F) = F.dom_to_graph
cod_to_graph(F) = F.cod_to_graph
domain_point(F) = point_coordinates(inverted_set(domain_ring(F)))
codomain_point(F) = point_coordinates(inverted_set(codomain_ring(F)))

function _domain_point(f::Vector{FuncType}) where {FuncType<:MPolyElem}
  length(f) == 0 && error("map must have at least one component")
  R = parent(f[1])
  kk = coefficient_ring(R)
  return [zero(kk) for i in 1:ngens(R)]
end

function _domain_point(f::Vector{FuncType}) where {FuncType<:MPolyLocalizedRing}
  length(f) == 0 && error("map must have at least one component")
  L = parent(f[1])
  R = base_ring(L)
  kk = coefficient_ring(R)
  return [zero(kk) for i in 1:ngens(R)]
end

function _codomain_point(f::Vector{FuncType}, p::Vector{T}) where {FuncType<:MPolyElem, T}
  return [evaluate(g, p) for g in f]
end

function _codomain_point(f::Vector{FuncType}, p::Vector{T}) where {FuncType<:MPolyLocalizedRing, T}
  return [evaluate(numerator(g), p)//evaluate(denominator(g), p) for g in f]
end

function _codomain_ring(f::Vector{FuncType}, q::Vector{T}) where {FuncType<:MPolyElem, T}
  length(f) == 0 && error("function must have at least one component")
  R = parent(f[1])
  kk = coefficient_ring(R) # the coefficient ring
  P, y = PolynomialRing(kk, ["u$k" for k in 1:length(f)])
  U = complement_of_ideal(P, [kk(a) for a in q])
  L, _ = Localization(P, U)
  return L
end

function _codomain_ring(f::Vector{FuncType}, q::Vector{T}) where {FuncType<:MPolyLocalizedRingElem, T}
  length(f) == 0 || error("function must have at least one component")
  W = parent(f[1])
  R = base_ring(W)
  kk = coefficient_ring(R) # the coefficient ring
  P, y = PolynomialRing(kk, ["u$k" for k in 1:length(f)])
  U = complement_of_ideal(P, [kk(a) for a in q])
  L, _ = Localization(P, U)
  return L
end

function _domain_ring(f::Vector{FuncType}, p::Vector{T}) where {FuncType<:MPolyElem, T}
  length(f) == 0 && error("function must have at least one component")
  R = parent(f[1])
  kk = coefficient_ring(R)
  U = complement_of_ideal(R, [kk(a) for a in p])
  L, _ = Localization(R, U)
  return L
end

function _domain_ring(f::Vector{FuncType}) where {FuncType<:MPolyLocalizedRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}
  length(f) == 0 || error("function must have at least one component")
  return parent(f[1])
end

function Base.show(io::IO, F::MapGerm) 
  s = "($(ground_field(F) == :complex ? "ℂ" : "ℝ")^$(ngens(base_ring(domain_ring(F)))), "
  s = s * "[$(prod(vcat(vcat([[String(Symbol(x)), ", "] for x in point_coordinates(inverted_set(domain_ring(F)))[1:end-1]]...), String(Symbol(last(point_coordinates(inverted_set(domain_ring(F)))))))))])"
  s = s * " → ($(ground_field(F) == :complex ? "ℂ" : "ℝ")^$(ngens(base_ring(codomain_ring(F)))), "
  s = s * "[$(prod(vcat(vcat([[String(Symbol(x)), ", "] for x in point_coordinates(inverted_set(codomain_ring(F)))[1:end-1]]...), String(Symbol(last(point_coordinates(inverted_set(codomain_ring(F)))))))))]),  "
  s = s * "($(prod(vcat(vcat([[String(Symbol(x)), ", "] for x in gens(base_ring(domain_ring(F)))[1:end-1]]...), String(Symbol(last(gens(base_ring(domain_ring(F))))))))))"
  s = s * " ↦ ($(prod(vcat(vcat([[String(Symbol(x)), ", "] for x in components(F)[1:end-1]]...), String(Symbol(last(components(F))))))))"
  print(io, s)
end

is_finite(F::AbsMapGerm) = get_attribute!(F, :is_finite) do
  I = ideal(domain_ring(F), [g - a for (g, a) in zip(components(F), domain_point(F))])
  return dim(I) == 0
end

is_A_finite(F::AbsMapGerm) = get_attribute!(F, :is_A_finite) do
  return false
end

function has_finite_A_codimension(F::AbsMapGerm)
  # TODO: To be filled in
end

function extended_A_tangent_space(F::AbsMapGerm)
  # TODO: To be filled in
end

function pushforward(M::ModuleFP, phi::Map{DomType, CodType}) where {DomType<:Ring, CodType<:Ring}
  error("pushforward not implemented for modules of type $(typeof(M)) and maps of type $(typeof(phi))")
end

function pushforward(M::ModuleFP{PolyType}, phi::Map{DRT, CRT}) where {PolyType<:MPolyElem, DRT<:MPolyRing, CRT<:MPolyRing}
  # Here comes our algorithm for the pushforward in the polynomial case
end

function pushforward(S::DRT, phi::Map{DRT, CRT}) where {DRT<:MPolyRing, CRT<:MPolyRing}
  R = domain(phi)
  S == codomain(phi) || error("map not compatible with ring")
  # compose the common polynomial ring
  kk = coefficient_ring(S)
  P, _ = PolynomialRing(kk, vcat(symbols(S), symbols(R)))
  RtoP = hom(R, P, gens(P)[ngens(S)+1:end])
  StoP = hom(S, P, gens(P)[1:ngens(S)])
  # Choose an elimination ordering for the variables of S
  o = degrevlex(gens(P)[1:ngens(S)])*degrevlex(gens(P)[ngens(S)+1:end])
  I = ideal(P, [RtoP(y)- StoP(phi(y)) for y in gens(R)])
  gbI = groebner_basis(I, ordering=o)

  # gather the monomials which are generators of S over R
  leadI = leading_ideal(I, ordering=o)
  mons = [x for x in gens(leadI) if all(y->!(divides(x, y)[1]), RtoP.(gens(R)))]
  rel_lead = ideal(S, [preimage(StoP, x) for x in mons])
  dim(rel_lead) == 0 || error("map is not finite")

  base = elem_type(S)[]
  d = 0
  new_mons = [ x for x in Oscar.all_monomials(S, d) if !(x in rel_lead)]
  while length(new_mons) != 0 
    base = vcat(base, new_mons)
    d = d + 1
    new_mons = [ x for x in Oscar.all_monomials(S, d) if !(x in rel_lead)]
  end

  r = length(base)
  F = FreeMod(R, r) # the ambient free module for the representation of S over R
  
  # This function returns a representative of an element g in S 
  # in the free module F with generators identified with monomials in base
  function helper_func(g::MPolyElem)
    parent(g) == S || error("element does not belong to the correct ring")
    Pg = StoP(g)
    h = normal_form(Pg, I, o)
    result = zero(F)
    for (a, m) in zip(coefficients(h), monomials(h))
      for (e, x) in zip(gens(F), base)
        (yes, y) = divides(m, StoP(x))
        if yes && all(z->!(divides(y, z)[1]), StoP.(gens(S)))
          result = result + a*preimage(RtoP, y)*e
        end
      end
    end
    return result
  end

  function inv_help_func(v::FreeModElem)
    parent(v) == F || error("element does not belong to the correct module")
    return sum([phi(v[i])*base[i] for i in 1:rank(parent(v))])
  end

  StoF = MapFromFunc(helper_func, inv_help_func, S, F)

  # Compute the kernel of the inverse map to arrive at a presentation of S 
  # as an R-module

  FP = FreeMod(P, rank(F))
  P1 = FreeMod(P, 1)
  M, _ = quo(P1, (I*P1)[1])
  psi = hom(FP, M, [StoP(x)*M[1] for x in base])
  K, _ = kernel(psi)

  # intersection of this kernel with the submodule F over the subring R 
  # will provide us with the sought for presentation.
  O = o*lex(gens(FP))
  gbK = std_basis(K, O)

  valid_gens = [v for (v, a) in zip(gbK.O, ambient_representatives_generators(leading_module(K, O))) if all(x->!(a in (ideal(P, x)*FP)[1]), gens(P)[1:ngens(S)])]

  # Now we need to port them to the module F
  K_gens = [sum([preimage(RtoP, a)*F[i] for (a, i) in zip(Vector(v), 1:rank(F))]) for v in valid_gens]

  # form the quotient and the identification
  Smod, pr = quo(F, K_gens)
  StoSmod = compose(StoF, pr)

  # assemble the multiplication map on the module side
  # TODO: This can probably be optimized using multiplication 
  # tables for the generators over R?
  function mult_map(v::SubQuoElem, w::SubQuoElem)
    parent(v) == parent(w) == Smod || error("elements do not belong to the correct module")
    return StoSmod(preimage(StoSmod, v)*preimage(StoSmod, w))
  end

  return Smod, StoSmod, mult_map
end
