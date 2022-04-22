export clear_denominators, base_ring_module, base_ring_module_map, has_solution

# for a free module F ≅ Sʳ over a localized ring S = R[U⁻¹] this 
# returns the module F♭ ≅ Rʳ.
function base_ring_module(F::FreeMod{T}) where {T<:AbsLocalizedRingElem}
  if !has_attribute(F, :base_ring_module) 
    L = base_ring(F)
    R = base_ring(L)
    Fb = FreeMod(R, ngens(F))
    set_attribute!(F, :base_ring_module, Fb)
  end
  return get_attribute(F, :base_ring_module)::base_ring_module_type(F)
end

base_ring_module_type(::Type{FreeMod{T}}) where {T<:AbsLocalizedRingElem} = FreeMod{base_ring_elem_type(T)}
base_ring_module_type(F::FreeMod{T}) where {T<:AbsLocalizedRingElem} = base_ring_module_type(typeof(F))

# for a free module F ≅ Sʳ over a localized ring S = R[U⁻¹] this 
# returns the canonical map F♭ ≅ Rʳ → Sʳ ≅ F.
function base_ring_module_map(F::FreeMod{T}) where {T<:AbsLocalizedRingElem}
  if !has_attribute(F, :base_ring_module_map) 
    Fb = base_ring_module(F)
    f = hom(Fb, F, gens(F))
    set_attribute!(F, :base_ring_module_map, f)
  end
  return get_attribute(F, :base_ring_module_map)::morphism_type(base_ring_module_type(F), typeof(F))
end

base_ring_module_map_type(::Type{FreeMod{T}}) where {T<:AbsLocalizedRingElem} = morphism_type(base_ring_module_type(FreeMod{T}), FreeMod{T})
base_ring_module_map_type(F::FreeMod{T}) where {T<:AbsLocalizedRingElem} = base_ring_module_map_type(typeof(F))

########################################################################
# 
# Atomic building blocks from [1] for computability of localizations
#
########################################################################
#
# [1] Posur: Linear systems over localizations of rings, arXiv:1709.08180v2
#

# For an m×n-matrix A with entries aᵢⱼ in a localized ring S = R[U⁻¹] 
# this returns a pair of matrices (B, D) ∈ Rᵐˣⁿ × Uⁿˣⁿ where D is a 
# diagonal matrix such that D ⋅ A = B
function clear_denominators(A::MatrixType) where {T<:AbsLocalizedRingElem, MatrixType<:MatrixElem{T}}
  m = nrows(A)
  n = ncols(A)
  S = base_ring(A)
  R = base_ring(S)
  D = zero(MatrixSpace(R, m, m))
  B = zero(MatrixSpace(R, m, n))
  for i in 1:m
    d = lcm(vec(denominator.(A[i,:])))
    D[i,i] = d
    for j in 1:n
      B[i, j] = numerator(A[i,j])*divexact(d, denominator(A[i,j]))
    end
  end
  return B, D
end

# Following a modified version of Lemma 3.1 and Remark 3.2 in [1], 
# we reduce the syzygy problem over a localization S = R[U⁻¹] 
# to a syzygy problem over the base ring R.
#
# Let A ∈ Sᵐˣⁿ be an arbitrary matrix and let (B, D) = `clear_denominators(A)` 
# be the pair of matrices over R such that D⋅A = B. Let L be a solution 
# of the syzygy problem for B. Then we have a commutative diagram 
#
#        L      B
#   R¹ˣᵖ → R¹ˣᵐ → R¹ˣⁿ→ 0
#   ↓      ↓      ↓ 
#   S¹ˣᵖ → S¹ˣᵐ → S¹ˣⁿ→ 0
#   ↓ ≅    ↓ D    ↓ ≅    
#   S¹ˣᵖ → S¹ˣᵐ → S¹ˣⁿ→ 0
#       L⋅D     A
#
# where all unlabeled maps are the canonical ones. Since D is an isomorphism, 
# the last row remains exact and hence solves the syzygy problem for A.
#
# The modification compared to [1] lies in the fact that we do not find 
# a common denominator for the whole matrix A at once, but one for each 
# row. That allows us to reduce the complexity of the entries of B.
#
# [1] Posur: Linear systems over localizations of rings, arXiv:1709.08180v2
#
function syz(A::MatrixType) where {T<:AbsLocalizedRingElem, MatrixType<:MatrixElem{T}}
  B, D = clear_denominators(A)
  L = syz(B)
  return L*D
end

# The annihilator of b as an element of a free module modulo the cokernel of A
# following Construction 3.6 in [1].
#
# [1] Posur: Linear systems over localizations of rings, arXiv:1709.08180v2
#
function ann(b::MatrixType, A::MatrixType) where {T<:RingElem, MatrixType<:MatrixElem{T}}
  R = base_ring(A)
  R === base_ring(b) || error("matrices must be defined over the same ring")
  nrows(b) == 1 || error("only matrices with one row are allowed!")
  m = nrows(A)
  n = ncols(A)
  Aext = vcat(b, A)
  L = syz(Aext)
  return ideal(R, vec(L[:, 1]))
end

# Following Definition 3.8 [1], this routine must check whether the intersection 
# of a multiplicative set U ⊂ R and an ideal I ⊂ R is nonempty. 
#
# If not, this returns a triple (false, zero(R), [0,…,0])
#
# If yes, this returns a triple (true, u, [a₁, …, aᵣ]) with u ∈ U ∩ I 
# and u = ∑ᵢ aᵢ⋅ fᵢ where I = ⟨f₁, …, fᵣ⟩ is generated by the fᵢ.
#
# [1] Posur: Linear systems over localizations of rings, arXiv:1709.08180v2
#
function has_nonepmty_intersection(U::AbsMultSet, I::Ideal)
  R = base_ring(U)
  R == base_ring(I) || error("the multiplicative set and the ideal must be defined over the same ring")
  error("this method is not implemented for multiplicative sets of type $(typeof(U)) and ideals of type $(typeof(I)); see Posur: Linear systems over localizations of rings, arXiv:1709.08180v2, Definition 3.8 for the requirements of the implementation")
end

# Let S = R[U⁻¹] be the localization of a coherent, computable ring R for which 
# the 'localization problem' has a solution; cf. [1].
#
# For a matrix A ∈ Sᵐˣⁿ and a vector b ∈ S¹ˣⁿ this uses Theorem 3.9 in [1]
# to check whether the linear system x ⋅ A = b has a solution x and 
# returns a pair (true, x) in the affirmative case and (false, zero(S¹ˣⁿ)) 
# otherwise.
#
# [1] Posur: Linear systems over localizations of rings, arXiv:1709.08180v2
#

# This first version reduces to the case of matrices without denominators.
function has_solution(A::MatrixType, b::MatrixType) where {T<:AbsLocalizedRingElem, MatrixType<:MatrixElem{T}}
  S = base_ring(A)
  R = base_ring(S)
  S === base_ring(b) || error("matrices must be defined over the same ring")
  nrows(b) == 1 || error("only matrices with one row are allowed!")
  B, D = clear_denominators(A)
  c, u = clear_denominators(b)
  (success, y, v) = has_solution(B, c, inverted_set(S))
  success || return (false, zero(MatrixSpace(S, 1, n)))
  # We have B = D⋅A and c = u ⋅ b as matrices. 
  # Now y⋅B = v⋅c ⇔ y⋅D ⋅A = v ⋅ u ⋅ b ⇔ v⁻¹ ⋅ u⁻¹ ⋅ y ⋅ D ⋅ A = b.
  # Take v⁻¹ ⋅ u⁻¹ ⋅ y ⋅ D to be the solution x of x ⋅ A = b.
  return (success, S(one(R), v*u[1,1])*S(y*D))
end

# This second version solves over the base ring and checks compatibility with 
# the given units.
function has_solution(
    A::MatrixType, b::MatrixType, U::AbsMultSet
  ) where {
    MatrixType<:MatrixElem
  }
  R = base_ring(A)
  R === base_ring(b) || error("matrices must be defined over the same ring")
  R === ambient_ring(U) || error("multiplicative set must be defined over the same ring as the matrices")
  m = nrows(A)
  nrows(b) == 1 || error("can not solve for more than one row vector")
  n = ncols(A)
  n == ncols(b) || error("matrix sizes are not compatible")
  Aext = vcat(-b, A)
  L = syz(Aext)
  I = ideal(R, vec(L[:, 1]))
  (success, u, a) = has_nonepmty_intersection(U, I)
  success || return (false, zero(MatrixSpace(R, 1, ngens(I))), zero(R))
  l = a*L 
  return (success, l[1, 2:end], l[1,1])
end


########################################################################
#
# a proof-of-concept implementation for localizations of modules over 
# polynomial rings
#
########################################################################

# compute the syzygies of a matrix
function syz(A::MatrixType) where {T<:MPolyElem, MatrixType<:MatrixElem{T}}
  R = base_ring(A)
  m = nrows(A)
  n = ncols(A)
  F = FreeMod(R, m)
  G = FreeMod(R, n)
  f = hom(F, G, A)
  K, inc, = kernel(f)
  g = Vector.(ambient_representatives_generators(K))
  p = length(g)
  L = zero(MatrixSpace(R, p, m))
  for i in 1:p
    for j in 1:m
      L[i, j] = g[i][j]
    end
  end
  return L
end

# concrete implementations of the above function
function has_nonepmty_intersection(U::MPolyPowersOfElement, I::MPolyIdeal)
  R = ambient_ring(U)
  R == base_ring(I) || error("the multiplicative set and the ideal must be defined over the same ring")

  d = prod(denominators(U))
  inradical(d, I) || return false, zero(R), zero(MatrixSpace(R, 1, ngens(I)))
  (k, f) = Oscar._minimal_power_such_that(d, (x->x in I))
  return true, f, coordinates(f, I)
end

function has_nonepmty_intersection(U::MPolyComplementOfPrimeIdeal, I::MPolyIdeal)
  R = ambient_ring(U)
  R == base_ring(I) || error("the multiplicative set and the ideal must be defined over the same ring")
  P = prime_ideal(U)
  for (f, i) in zip(gens(I), 1:ngens(I))
    if !(f in P)
      A = zero(MatrixSpace(R, 1, ngens(I)))
      A[1, i] = 1
      return true, f, A
    end
  end
  return false, zero(R), zero(MatrixSpace(R, 1, ngens(I)))
end

# missing functionality to write an element f ∈ I of an ideal as 
# a linear combination of the generators of I
function coordinates(f::MPolyElem, I::MPolyIdeal)
  R = parent(f)
  R == base_ring(I) || error("polynomial does not belong to the base ring of the ideal")
  f in I || error("polynomial does not belong to the ideal")
  singular_assure(I)
  Rsing = I.gens.Sx
  fsing = Singular.Ideal(Rsing, [Rsing(f)])
  a_s, u_s = Singular.lift(I.gens.S, fsing)
  A_s = Matrix(a_s)
  U_s = Matrix(u_s)
  (ncols(U_s) == nrows(U_s) == 1 && iszero(U_s[1,1])) || error("no suitable ordering was used")
  A = zero(MatrixSpace(R, 1, ngens(I)))
  for i in 1:ngens(I)
    A[1, i] = R(A_s[i, 1])
  end
  return A
end
