export is_equidimensional
export singular_locus_with_decomposition
export reduced_scheme

function singular_locus(X::Spec)
  comp = singular_locus_with_decomposition(X)
  if length(comp) == 0 
    return subscheme(X, one(OO(X)))
  end
  R = base_ring(OO(X))
  return Spec(R, prod([modulus(OO(Y)) for Y in comp]), inverted_set(OO(X)))
end

function singular_locus_with_decomposition(X::Spec)
  I = localized_modulus(OO(X))
  result = typeof(X)[]
  if is_equidimensional(X)
    d = dim(X)
    R = base_ring(OO(X))
    n = ngens(R)
    J = saturated_ideal(I)
    M = jacobi_matrix(gens(J))
    K = ideal(R, minors(M, n-d))
    one(OO(X)) in OO(X)(K) && return result
    return [subscheme(X, K)]
  else
    P = primary_decomposition(saturated_ideal(I))
    components = [subscheme(X, J[2]) for J in P]
    for Y in components
      for Z in components
        if !(Y == Z)
          W = intersect(Y, Z)
          if !isempty(W) 
            push!(result, W)
          end
        end
      end
    end
    for Y in components
      result = vcat(result, singular_locus(Y))
    end
  end
  return result
end

@attr Bool function is_equidimensional(X::Spec)
  I = localized_modulus(OO(X))
  P = primary_decomposition(saturated_ideal(I))
  length(P) == 0 && return true
  d = dim(P[1][1])
  all(x->dim(x[1])==d, P[2:end]) && return true
  return false
end

@attr function reduced_scheme(X::Spec)
  I = localized_modulus(OO(X))
  J = radical(saturated_ideal(I))
  return Spec(base_ring(J), J, inverted_set(OO(X)))
end


  

