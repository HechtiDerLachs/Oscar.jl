export versal_unfolding, delta_invariant, classify, T2

oscar_coeff_ring(::Singular.Rationals) = QQ
# TODO: make sure, more rings work!

oscar_poly_ring(S::Singular.PolyRing) = PolynomialRing(oscar_coeff_ring(base_ring(S)), symbols(S))[1]

function versal_unfolding(I::MPolyIdeal; degree_cutoff::Int=100)
  R = base_ring(I)
  SR = singular_poly_ring(R) # TODO: Do we need a local ordering here?
  SI = Singular.Ideal(SR, SR.(gens(I)))
  result = Singular.LibDeform.versal(SI, degree_cutoff)
  Sambient_ring = result[1][1]
  # TODO: transfer the ordering 
  # ambient_ring_ordering = ?
  RT = oscar_poly_ring(result[1][1]) # the ambient ring of the total space
  D = result[1][2]
  M = D[:Fs]
  ideal_total_space = ideal(RT, [M[j,i] for i in 1:ncols(M) for j in 1:nrows(M)])
  B = oscar_poly_ring(result[3][1])
  M = D[:Js]
  help_map = hom(RT, B, vcat(gens(B), [zero(B) for i in 1:ngens(R)]))
  tmp = help_map.(RT.([M[j,i] for i in 1:ncols(M) for j in 1:nrows(M)]))
  ideal_base = ideal(B, tmp)

  # for some reason, the equations defining the base scheme 
  # are not contained in the equations defining the total space.
  # TODO: Look up why! It seems to be anticipated, but what 
  # is the reason?
  ideal_total_space = ideal_total_space + ideal(RT, (RT.([M[j,i] for i in 1:ncols(M) for j in 1:nrows(M)])))

  QT, _ = quo(RT, ideal_total_space)
  QB, _ = quo(B, ideal_base)
  pr = hom(QB, QT, gens(QT)[1:ngens(QB)])
  Q, _ = quo(R, I)
  sp = hom(QT, Q, vcat([zero(R) for i in 1:ngens(QB)], gens(R)))
  X0 = Spec(Q)
  X = Spec(QT)
  Y = Spec(QB)
  p = SpecMor(X, Y, hom(OO(Y), OO(X), OO(X).(pr.(gens(QB)))))
  inc = SpecMor(X0, X, hom(OO(X), OO(X0), OO(X0).(sp.(gens(QT)))))
  return inc, p
end

function smodule_to_matrix(M::Singular.smodule)
  Avecs = Array.([M[i] for i in 1:ngens(M)])
  A = zero_matrix(base_ring(M), maximum(length.(Avecs)), length(Avecs))
  for j in 1:ncols(A)
    for i in 1:length(Avecs[j])
      A[i, j] = Avecs[j][i]
    end
  end
  return A
end

function delta_invariant(f::MPolyElem)
  R = parent(f)
  SR = singular_poly_ring(R)
  Sf = SR(f)
  result = Singular.LibHnoether.delta(Sf) # the extra zero is a flag for verbose output
end

function T2(f::MPolyElem)
  R = parent(f)
  SR = singular_poly_ring(R)
  Sf = S(f)
  result = Singular.LibSing.T_2(Sf, 0) # the extra zero is a flag for verbose output
  M = result[1]
  A = smodule_to_matrix(M)
  # TODO: Also extract the other information
  F = FreeMod(R, nrows(A))
  return quo(F, transpose(map_entries(R, A)))[1]
end

function T2(I::MPolyIdeal)
  R = base_ring(I)
  SR = singular_poly_ring(R)
  SI = Singular.Ideal(SR, SR.(gens(I)))
  result = Singular.LibSing.T_2(SI, 0) # the extra zero is a flag for verbose output
  M = result[1]
  A = smodule_to_matrix(M)
  # TODO: Also extract the other information
  F = FreeMod(R, nrows(A))
  return quo(F, transpose(map_entries(R, A)))[1]
end

function classify(f::MPolyElem)
  R = parent(f)
  o = negdegrevlex(gens(R))
  SR = singular_poly_ring(R, o)
  Sf = SR(f)
  Singular.LibClassify.classify(Sf) # This command prints
  return f
end
