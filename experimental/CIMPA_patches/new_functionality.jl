export kbase, versal_deformation_perturbations

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

function is_quotient_of_free_module(M::SubQuo)
  return all(x->represents_element(x, M), gens(ambient_free_module(M)))
end

function is_submodule_of_free_module(M::SubQuo)
  return !isdefined(M, :quo) || all(x->iszero(x), M.quo)
end

function kbase(M::SubQuo{T}) where {T<:MPolyElem}
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
