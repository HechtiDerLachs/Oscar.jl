export kbase, versal_deformation_perturbations
export singular_slocus, singular_vdim, singular_vdim_local, vdim
export milnor_number
export elimpart

function manualT1(I::Ideal)
  R = base_ring(I)
  F1 = FreeMod(R, 1)
  Imod, _ = sub(F1, [g*F1[1] for g in gens(I)])
  RmodI, _ = quo(F1, Imod)
  N, m = hom(Imod, RmodI, :with_map)
  f = gens(I)
  Df = jacobi_matrix(f)
  F = ambient_free_module(N)
  spanDf, _ = sub(F, Df)
  T, map_from_normal_module = quo(N, ambient_representatives_generators(spanDf))
  return T, map_from_normal_module, m
end

function is_quotient_of_free_module(M::SubquoModule)
  return all(x->represents_element(x, M), gens(ambient_free_module(M)))
end

function is_submodule_of_free_module(M::SubquoModule)
  return !isdefined(M, :quo) || all(x->iszero(x), M.quo)
end

function kbase(M::SubquoModule{T}) where {T<:MPolyRingElem}
  if !is_quotient_of_free_module(M)
    N, iso = present_as_cokernel(M, :with_map)
    b = kbase(N)
    return iso.(b)
  end

  F = ambient_free_module(M)
  N, _ = sub(F, relations(M))
  leadN = leading_module(N)
  R = base_ring(M)
  result = elem_type(F)[]
  for e in gens(F)
    d = 0
    deg_d_part = [x*e for x in Oscar.all_monomials(R, d) if !(represents_element(x*e, leadN))]
    while length(deg_d_part)>0
      result = vcat(result, deg_d_part)
      d = d+1
      deg_d_part = [x*e for x in Oscar.all_monomials(R, d) if !(represents_element(x*e, leadN))]
    end
  end
  return result
end

function versal_deformation_perturbations(I::MPolyIdeal)
  T, projection_from_normal_module, as_hom = manualT1(I)
  b = kbase(T)
  blift = [preimage(projection_from_normal_module, v) for v in b]
  bhoms = as_hom.(blift)
  [f.(gens(domain(f))) for f in bhoms]
end


### Functionality for elements and ideals in localized rings
function Generic.dim(I::MPolyLocalizedIdeal) 
    return dim(saturated_ideal(I))
end

function Hecke.radical(I::MPolyLocalizedIdeal)
    return base_ring(I)(radical(saturated_ideal(I)))
end

function Oscar.jacobi_matrix(f::MPolyLocRingElem)
  L = parent(f)
  n = nvars(base_ring(L))
  return matrix(L, n, 1, [derivative(f, i) for i=1:n])
end

function Oscar.jacobi_matrix(g::Vector{<:MPolyLocRingElem})
  length(g) == 0 && error("can not return the jacobi matrix of an empty vector")
  R = parent(g[1])
  n = nvars(base_ring(R))
  @assert all(x->parent(x) == R, g)
  return matrix(R, n, length(g), [derivative(x, i) for i=1:n for x = g])
end

function Oscar.derivative(f::MPolyLocRingElem, i::Int)
  isone(denominator(f)) && return parent(f)(derivative(numerator(f), i))
  num = derivative(numerator(f), i)*denominator(f) - derivative(denominator(f), i)*numerator(f)
  den = denominator(f)^2
  g = gcd(num, den)
  return parent(f)(divexact(num, g), divexact(den, g), check=false)
end

function Oscar.ngens(L::MPolyLocRing)
    return ngens(base_ring(L))
end

function singular_slocus(I::MPolyIdeal)
  R = base_ring(I)
  SR = singular_poly_ring(R)
  Sgens = SR.(gens(I))
  SI = Singular.Ideal(SR, Sgens)
  SJ = Singular.LibSing.slocus(SI)
  J = ideal(R, R.(gens(SJ)))
  return J
end

function singular_vdim(I::MPolyIdeal)
  R = base_ring(I)
  SR = singular_poly_ring(R)
  Sgens = SR.(gens(I))
  SI = Singular.Ideal(SR, Sgens)
  return Singular.vdim(Singular.std(SI))
end

function singular_vdim_local(I::MPolyIdeal)
  R = base_ring(I)
  SR = singular_poly_ring(R, negdegrevlex(gens(R)))
  Sgens = SR.(gens(I))
  SI = Singular.Ideal(SR, Sgens)
  std_SI = Singular.std(SI)
  return Singular.vdim(std_SI)
end

function vdim(I::T) where {T<:MPolyLocalizedIdeal{<:MPolyLocRing{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal}}}
  I_shift = Oscar.shifted_ideal(I)
  return singular_vdim_local(I_shift)
end

function milnor_number(f::MPolyLocRingElem{<:Any, <:Any, <:Any, <:Any, <:MPolyComplementOfKPointIdeal})
  R = parent(f)
  J = ideal(R, minors(jacobi_matrix(f), 1))
  Q, _ = quo(R, J)
  return vector_space_dimension(Q)
end

# another wrapper for elimpart
function elimpart(I::MPolyIdeal)
  println("eliminating superfluous variables from the ideal $I")
  R = base_ring(I)
  SR = singular_poly_ring(R)
  SI = Singular.Ideal(SR, SR.(gens(I)))
  out = Singular.LibPresolve.elimpart(SI)
  kept_var_symb = [symbols(R)[i] for i in 1:ngens(R) if !iszero(out[4][i])]
  substitutions = [x => R.(y) for (x, y) in zip(gens(R), gens(out[5]))]
  println("Keep the variables $([String(x) for x in kept_var_symb]);")
  println("Substitute as follows:")
  for i in 1:ngens(R)
    println("$(R[i]) -> $((R.(gens(out[5])))[i])")
  end

  # construct the ideal
  Rnew, new_vars = PolynomialRing(coefficient_ring(R), kept_var_symb)
  subst_map_R = hom(R, R, R.(gens(out[5])))
  imgs = Vector{elem_type(Rnew)}()
  j = 1
  for i in 1:ngens(R)
    if !iszero(out[4][i])
      push!(imgs, gens(Rnew)[j])
      j = j+1
    else
      push!(imgs, zero(Rnew))
    end
  end
  proj_map = hom(R, Rnew, imgs)

  # the full substitution map 
  f = compose(subst_map_R, proj_map)

  # the transformed ideal
  gensInew = gens(standard_basis(ideal(Rnew, f.(gens(I))), ordering=degrevlex(gens(Rnew))))
  println("After substitution, the ideal is generated by $gensInew")
  return Rnew, ideal(Rnew, gensInew), f
end

