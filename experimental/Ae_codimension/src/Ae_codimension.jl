include("Types.jl")

# Assume ϕ : R → S is a ring homomorphism and F an S-module 
# which happens to be a finite R-module via Φ. Then give 
# F as an R-module and and identifying maps in both directions.
function _pushforward(phi::Map{<:MPolyRing, <:MPolyQuoRing}, F::FreeMod{<:MPolyQuoRing})
  R = domain(phi)
  S = codomain(phi)
  @req S === base_ring(F) "base rings incompatible"
  r = rank(F)
  error("not implemented")
end

function _codomain_as_module(
    phi::Map{<:MPolyLocRing{<:Field, <:FieldElem, <:MPolyRing, <:MPolyRingElem, <:MPolyComplementOfKPointIdeal},
             <:MPolyQuoLocRing{<:Field, <:FieldElem, <:MPolyRing, <:MPolyRingElem, <:MPolyComplementOfKPointIdeal}
            }
  )
  error("not implemented")
end

function _codomain_as_module(
    phi::Map{<:MPolyRing{<:FieldElem}, <:MPolyRing{<:FieldElem}}
  )
  R = domain(phi)
  S = codomain(phi)
  kk = coefficient_ring(R)
  @req kk === coefficient_ring(S) "coefficient rings of domain and codomain must coincide"
  q = ngens(R)
  p = ngens(S)
  y = gens(R)
  x = gens(S)
  f = _images_of_generators(phi)
  I = ideal(S, f)

  RS, z = polynomial_ring(kk, vcat(symbols(R), symbols(S)))
  inc_R = hom(R, RS, gens(RS)[1:q])
  inc_S = hom(S, RS, gens(RS)[q+1:end])
  Y = gens(RS)[1:q]
  X = gens(RS)[q+1:end]
  J = ideal(RS, [Y[i] - inc_S(f[i]) for i in 1:q])
  ord = degrevlex(X)*degrevlex(Y)
  gb_J = groebner_basis(J, ordering=ord)
  lead_J = leading_ideal(gb_J)
  @assert all(radical_membership(a, lead_J) for a in X) "map is not globally finite"

  pr_S = hom(RS, S, vcat([zero(S) for i in 1:q], gens(S)))
  lead_J_pr = pr_S(lead_J) # This will send every monomial to zero which does not have a constant R-part. 
  mon_dict, mon_list = _monomial_basis(lead_J_pr)
  # The monomials in the above list only give bounds for an ambient free module. 
  # We still have to divide by the remaining relations.
  r = length(mon_list)
  F = free_module(R, r)

  # relations coming from the equation for the image
  pr_R = hom(RS, R, vcat(gens(R), [zero(R) for i in 1:p]))
  img_eqns = [pr_R(f) for f in gens(gb_J) if all(all(iszero(e[q+i]) for i in 1:p) for e in AbstractAlgebra.exponent_vectors(f))]
  rels = elem_type(F)[a*g for a in img_eqns for g in gens(F)]

  # relations from elements of the groebner basis which are not monic w.r.t the x-variables
  S_over_R, _ = polynomial_ring(R, symbols(S))
  to_S_over_R = hom(RS, S_over_R, vcat([S_over_R(x) for x in gens(R)], gens(S_over_R)))

  gb_gens = [to_S_over_R(g) for g in gens(gb_J)]
  lead_exps = Vector{Int}[]
  lead_coeffs = elem_type(R)[]

  ord_S_over_R = degrevlex(gens(S_over_R))

  for g in gb_gens
    c, e = leading_coefficient_and_exponent(g; ordering=ord_S_over_R)
    push!(lead_exps, e)
    push!(lead_coeffs, c)
    is_constant(c) && continue
    @assert haskey(mon_dict, e) "leading exponent not found in monomial basis"
    v = sum(c*F[mon_dict[e]] for (c, e) in zip(AbstractAlgebra.coefficients(g), AbstractAlgebra.exponent_vectors(g)); init=zero(F))
    push!(rels, v)
  end
  
  #tails = [g - c*m for (g, c, m) in zip(gb_gens, lead_coeffs, lead_exps)]
  
  red_indices = [i for i in 1:length(gb_gens) if is_constant(lead_coeffs[i])]
  red_exps = lead_exps[red_indices]
  #red_tails = [inv(lead_coeffs[i])*tails[i] for i in red_indices]
  red_gens = [inv(lead_coeffs[i])*gb_gens[i] for i in red_indices]

  J, inc_J = sub(F, rels)
  M, pr_M = quo(F, J)

  F_one = F[mon_dict[[0 for i in 1:p]]]

  function _rec_div(g::MPolyRingElem)
    parent(g) === S_over_R || return _rec_div(evaluate(g, gens(S_over_R)))
    is_zero(g) && return decomp
    pre_result = zero(M)
    for (c, e) in zip(AbstractAlgebra.coefficients(g), AbstractAlgebra.exponent_vectors(g))
      if haskey(mon_dict, e)
        pre_result += c*M[mon_dict[e]]
        continue
      end
      k = findfirst(_divides(e, m) for m in red_exps)
      k === nothing && error("no element for reduction found")
      return pre_result + _rec_div(g - c*prod(x^j for (x, j) in zip(gens(S_over_R), e-red_exps[k]); init=one(S_over_R))*red_gens[k])
    end
    return pre_result
  end

  M_to_S = map_from_func(v->sum(phi(c)*mon_list[i] for (i, c) in coordinates(repres(v)); init=zero(S)), M, S)
  S_to_M = map_from_func(_rec_div, S, M)
  return M, S_to_M, M_to_S
end

function _monomial_basis(lead::MPolyIdeal)
  R = base_ring(lead)
  kk = coefficient_ring(R)
  result = Dict{Vector{Int}, Int}()
  list = Vector{elem_type(R)}()
  n = ngens(R)
  is_one(lead) && return result
  d = 0
  mon_counter = 0
  mons = filter!(m->!(m in lead), collect(monomials_of_degree(R, d)))
  while !isempty(mons)
    for m in mons
      e = first(AbstractAlgebra.exponent_vectors(m))
      mon_counter += 1
      result[e] = mon_counter
      push!(list, m)
    end
    d += 1
    mons = filter!(m->!(m in lead), collect(monomials_of_degree(R, d)))
  end
  return result, list
end


### Counterparts of functions in Nacho's code

# Probably the first argument is really a map?
function ae_normal_mod_k(f::MPolyIdeal, k::Int)
  error("not implemented")
end

function ae_normal(f::MPolyIdeal)
  error("not implemented")
end

function normal_OY_module(GOX::MatrixElem, GOY::MatrixElem)
end

function generate_OY_Module(GOX::MatrixElem, GOY::MatrixElem)
end

function malgr_ring(J::Ideal, n::Int, f::Ideal)
end

function malgr_form_poly(h::MPolyRingElem)
end

function malgr_form_vect(v::MatrixElem)
end

function _matrix_to_vector(M::MatrixElem)
end

function _vector_to_matrix(v::Vector, a::Int, b::Int)
end

function malgr_form_to_OX(M::MatrixElem)
end

function _split_map(f::Map{<:Ring, <:Ring})
end

function inv_malgr_poly(v::MatrixElem, g::Ideal, w::Ideal)
end

function preparation_ring(
    f::Map{<:MPolyRing, <:MPolyRing}, g::Vector{T}
  ) where {T<:MPolyRingElem}
  R = domain(f)
  S = codomain(f)
  @req all(parent(x) === S for x in g) "base rings are incompatible"
  kk = coefficient_ring(R)
  @req kk === coefficient_ring(S) "coefficient rings are incompatible"
  m = length(g)
  G_symbs = [Symbol("G($k)") for k in 1:m]
  x = gens(S)
  x_symbs = symbols(S)
  y = gens(R)
  y_symbs = symbols(R)
  
  P, all_coords = polynomial_ring(kk, vcat(x_symbs, G_symbs, y_symbs))
  X = all_coords[1:ngens(S)]
  Y = all_coords[ngens(S)+m+1:end]
  G = all_coords[ngens(S)+1:ngens(S)+m]
  R_to_P = hom(R, P, Y)
  S_to_P = hom(S, P, X)

  # Assemble the "Pusher" ideal
  push_gens = elem_type(P)[Y[i] - S_to_P(f(R[i])) for i in 1:ngens(R)]
  push_gens = vcat(push_gens, elem_type(P)[G[i] - S_to_P(g[i]) for i in 1:length(g)])

  ord = degrevlex(X)*degrevlex(G)*degrevlex(Y)
  SP = singular_poly_ring(P, ord)
  I = Singular.Ideal(SP, elem_type(SP)[SP(x) for x in push_gens])
  return P, Singular.std(I), SP.(X), SP.(Y), SP.(G)
end

morphism(prep::MalgrangePreparator) = prep.f
fiber_gens(prep::MalgrangePreparator) = prep.g

function preparation_ring(prep::MalgrangePreparator)
  if !isdefined(prep, :SPR)
    P, I, X, Y, G = preparation_ring(morphism(prep), fiber_gens(prep))
    prep.SPR = base_ring(I)
    prep.PR = P
    prep.I = I
    prep.x = X
    prep.y = Y
    prep.G = G
  end
  return prep.SPR
end

function oscar_preparation_ring(prep::MalgrangePreparator)
  if !isdefined(prep, :PR)
    preparation_ring(morphism(prep), fiber_gens(prep))
  end
  return prep.PR
end

domain_ring(prep::MalgrangePreparator) = domain(morphism(prep))
codomain_ring(prep::MalgrangePreparator) = codomain(morphism(prep))

function cod_var_imgs(prep::MalgrangePreparator)
  if !isdefined(prep, :x)
    preparation_ring(prep)
  end
  return prep.x
end

function dom_var_imgs(prep::MalgrangePreparator)
  if !isdefined(prep, :x)
    preparation_ring(prep)
  end
  return prep.x
end

function pusher_ideal(prep::MalgrangePreparator)
  if !isdefined(prep, :I)
    preparation_ring(prep)
  end
  return prep.I
end

function domain_module(prep::MalgrangePreparator{T}) where T
  if !isdefined(prep, :M)
    prep.M = FreeMod(domain_ring(prep), length(fiber_gens(prep)))
  end
  return prep.M::FreeMod{T}
end

function cod_to_PR(prep::MalgrangePreparator)
  if !isdefined(prep, :cod_to_PR)
    prep.cod_to_PR = hom(codomain_ring(prep), preparation_ring(prep), coefficient_ring(preparation_ring(prep)), cod_var_imgs(prep))
  end
  return prep.cod_to_PR
end

function extended_domain_ring(prep::MalgrangePreparator)
  if !isdefined(prep, :ext_dom)
    prep.ext_dom, _ = polynomial_ring(domain_ring(prep), length(fiber_gens(prep)))
  end
  return prep.ext_dom
end

function to_ext_dom(prep::MalgrangePreparator)
  if !isdefined(prep, :PR_to_ext_dom)
    ext_dom = extended_domain_ring(prep)
    img_gens = elem_type(ext_dom)[zero(ext_dom) for _ in 1:ngens(codomain_ring(prep))]
    img_gens = vcat(img_gens, gens(ext_dom))
    img_gens = vcat(img_gens, ext_dom.(gens(coefficient_ring(ext_dom))))
    coeff_map = coefficient_ring(domain_ring(prep))
    #coeff_map = x->domain_ring(prep)(coefficient_ring(domain_ring(prep))(x))
    prep.PR_to_ext_dom = hom(oscar_preparation_ring(prep), extended_domain_ring(prep), coeff_map, img_gens)
  end
  return prep.PR_to_ext_dom
end

function (prep::MalgrangePreparator{T})(f::T) where {T <: MPolyRingElem}
  @req parent(f) === codomain_ring(prep) "element not in the domain"
  Skk = coefficient_ring
  f_big = cod_to_PR(prep)(f)
  f_red = Singular.reduce(f_big, pusher_ideal(prep))
  f_ext = to_ext_dom(prep)(oscar_preparation_ring(prep)(f_red))
  @assert total_degree(f_ext) <= 1 "reduction was not successful"
  result = zero(domain_module(prep))
  for (c, e) in zip(AbstractAlgebra.coefficients(f_ext), AbstractAlgebra.exponent_vectors(f_ext))
    k = findfirst(isone, e)
    k = (k === nothing ? 1 : k)
    result = result + c*parent(result)[k]
  end

  return result
end

### MalgrangeModulePreparator

preparator(prep::MalgrangeModulePreparator) = prep.prep
codomain_module(prep::MalgrangeModulePreparator) = prep.cod_mod

function domain_module(prep::MalgrangeModulePreparator)
  if !isdefined(prep, :dom_mod)
    ring_prep = preparator(prep)
    m = length(fiber_gens(ring_prep))
    R = domain_ring(ring_prep)
    S = codomain_ring(ring_prep)
    F = codomain_module(prep)
    r = ngens(F)
    Rr= free_module(R, r)
    Rm = domain_module(ring_prep)
    result, mm = tensor_product(Rr, Rm; task=:map)
    prep.dom_mod = result
    prep.mult_map = mm
    prep.dom_fac = Rr
  end
  return prep.dom_mod
end

function (prep::MalgrangePreparator)(F::FreeMod)
  return MalgrangeModulePreparator(prep, F)
end

function multiplication_map(prep::MalgrangeModulePreparator)
  !isdefined(prep, :dom_mod) && domain_module(prep)
  return prep.mult_map
end

function domain_factor(prep::MalgrangeModulePreparator)
  !isdefined(prep, :dom_mod) && domain_module(prep)
  return prep.dom_fac
end

function (prep::MalgrangeModulePreparator)(v::FreeModElem)
  @req parent(v) === codomain_module(prep) "parent mismatch"
  result = zero(domain_module(prep))
  ring_prep = preparator(prep)
  mult_map = multiplication_map(prep)
  dom_fac = domain_factor(prep)
  for (i, c) in coordinates(v)
    result += mult_map((dom_fac[i], ring_prep(c)))
  end
  return result
end

### Experimental computation of the Ae-codimension

function ae_tangent(
    f::Map{<:MPolyRing, <:MPolyRing};
    split::Int=ngens(codomain(f))
  )
  R = domain(f)
  S = codomain(f)
  kk = coefficient_ring(R)
  @req kk === coefficient_ring(S) "incompatible rings"

  # find a set of generators for S as an R̃-module
  R_tilde, _ = polynomial_ring(kk, symbols(R)[1:split])
  ff = _images_of_generators(f)
  f_tilde = hom(R_tilde, S, ff[1:split])
  ff_tilde = _images_of_generators(f_tilde)
  I = ideal(S, ff_tilde)
  Q, pr = quo(S, I)
  kk = coefficient_ring(S)
  V, ident = vector_space(kk, Q)
  g = lift.(ident.(gens(V)))
  sort!(g, by=total_degree)

  prep = MalgrangePreparator(f_tilde, g)

  jac_f = jacobi_matrix(ff)
  n = ngens(S)
  F = FreeMod(S, ngens(R))
  jac_gens = [sum(jac_f[i, j]*F[j] for j in 1:ngens(R); init=zero(F)) for i in 1:nrows(jac_f)]
  jac_gens = [gg*v for gg in g for v in jac_gens]

  m = length(g)
  Y = gens(R)[split+1:end]
  pb_mons = elem_type(S)[]
  for e in Base.product([0:m for _ in 0:length(Y)]...)
    push!(pb_mons, f(prod(y^k for (y, k) in zip(Y, e); init=one(R))))
  end
  pb_gens = [hh*g for g in gens(F) for hh in pb_mons]
  pb_gens = vcat(pb_gens, [g*v for g in ff_tilde for v in gens(F)])

  Fprep = prep(F)
  sub_gens = [Fprep(g) for g in vcat(jac_gens, pb_gens)]
  ae_tangent, _ = sub(domain_module(Fprep), sub_gens)
  return ae_tangent
end


function ae_codimension(
    f::Map{<:MPolyRing, <:MPolyRing};
    split::Int=ngens(codomain(f))
  )
  aet = ae_tangent(f; split)
  return Singular.vdim(Singular.std(singular_generators(aet.sub.gens)))
end


