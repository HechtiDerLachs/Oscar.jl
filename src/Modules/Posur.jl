export clear_denominators, base_ring_module, base_ring_module_map, has_solution

export kernel, cokernel, coordinates

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

function clear_denominators(v::FreeModElem{<:AbsLocalizedRingElem})
  F = parent(v)
  L = base_ring(F)
  R = base_ring(L)
  d = lcm(denominator.(Vector(v)))
  u = elem_type(R)[]
  for a in Vector(v)
    push!(u, numerator(a)*div(d, denominator(a)))
  end
  Fb = base_ring_module(F)
  return sum([a*e for (a, e) in zip(u, gens(Fb))]), d
end

function clear_denominators(v::Vector{FreeModElem{RET}}) where {RET<:AbsLocalizedRingElem}
  u = clear_denominators.(v)
  return [a[1] for a in u], [a[2] for a in u]
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
  K, inc = kernel(f)
  return matrix(inc)
# g = Vector.(ambient_representatives_generators(K))
# p = length(g)
# L = zero(MatrixSpace(R, p, m))
# for i in 1:p
#   for j in 1:m
#     L[i, j] = g[i][j]
#   end
# end
# return L
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
  candidates = [(f, i) for (f, i) in zip(gens(I), 1:ngens(I)) if !(f in P)]
  length(candidates) == 0 && return false, zero(R), zero(MatrixSpace(R, 1, ngens(I)))
  d = maximum([total_degree(f) for (f, i) in candidates])
  (g, j) = candidates[1]
  for (h, k) in candidates
    if total_degree(h) < total_degree(g) 
      (g, j) = (h, k)
    end
  end
  A = zero(MatrixSpace(R, 1, ngens(I)))
  A[1, j] = 1
  return true, g, A
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

# missing functionality for maps of modules; check again with the definitions of `representing_matrix`!
compose(f::FreeModuleHom, g::FreeModuleHom) = hom(domain(f), codomain(g), representing_matrix(f)*representing_matrix(g))
compose(f::SubQuoHom, g::FreeModuleHom) = hom(domain(f), codomain(g), representing_matrix(f)*representing_matrix(g))
compose(f::SubQuoHom, g::SubQuoHom) = hom(domain(f), codomain(g), representing_matrix(f)*representing_matrix(g))
compose(f::FreeModuleHom, g::SubQuoHom) = hom(domain(f), codomain(g), representing_matrix(f)*representing_matrix(g))

########################################################################
# 
# Implementation of the generic code for the finitely presented modules
#
########################################################################

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

# For a SubQuo M over a localized ring S = R[U⁻¹] this returns the SubQuo N over R
# which contains all generators and relations for the saturation that have already 
# been cached. 
function pre_saturated_module(M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  has_attribute(M, :saturated_module) && return get_attribute(M, :saturated_module)::SubQuo{base_ring_elem_type(T)}
  if !has_attribute(M, :pre_saturated_module)
    (A, D) = clear_denominators(generator_matrix(M))
    (B, E) = clear_denominators(relations_matrix(M))
    S = base_ring(M)
    R = base_ring(S)
    F = ambient_free_module(M)
    Fb = base_ring_module(F)
    Mb = SubQuo(Fb, A, B)
    set_attribute!(M, :pre_saturation_data_gens, change_base_ring(S, D))
    set_attribute!(M, :pre_saturation_data_rels, change_base_ring(S, E))
    set_attribute!(M, :pre_saturated_module, Mb)
  end
  return get_attribute(M, :pre_saturated_module)::SubQuo{base_ring_elem_type(T)}
end

# For a SubQuo M over a localized ring S = R[U⁻¹] and its current 
# `pre_saturated_module` N this returns a matrix T 
# over R such that 
#
#   T ⋅ generator_matrix(M) ≡ generator_matrix(N) mod relations(N)
#
function pre_saturation_data_gens(M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  if !has_attribute(M, :pre_saturation_data_gens)
    pre_saturated_module(M)
  end
  return get_attribute(M, :pre_saturation_data_gens)::dense_matrix_type(T)
end

# For a SubQuo M over a localized ring S = R[U⁻¹] and its current 
# `pre_saturated_module` N this returns a matrix T 
# over R such that 
#
#   T ⋅ relations_matrix(M) ≡ relations_matrix(N)
#
function pre_saturation_data_rels(M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  if !has_attribute(M, :pre_saturation_data_rels)
    pre_saturated_module(M)
  end
  return get_attribute(M, :pre_saturation_data_rels)::dense_matrix_type(T)
end

base_ring_module_map_type(::Type{FreeMod{T}}) where {T<:AbsLocalizedRingElem} = morphism_type(base_ring_module_type(FreeMod{T}), FreeMod{T})
base_ring_module_map_type(F::FreeMod{T}) where {T<:AbsLocalizedRingElem} = base_ring_module_map_type(typeof(F))

# For a homomorphism of free modules over the same ring this returns the
# representing matrix.
function representing_matrix(f::FreeModuleHom{ModType, ModType, Nothing}) where {ModType<:FreeMod}
  F = domain(f)
  G = codomain(f)
  R = base_ring(domain(f))
  A = zero(MatrixSpace(R, rank(F), rank(G)))
  for i in 1:rank(F)
    v = f(F[i])
    for j in 1:rank(G)
      A[i, j] = v[j]
    end
  end
  return A
end

# When the codomain is a SubQuo, return a matrix A whose rows represent the 
# images of the base vectors in the ambient free module of the codomain.
function ambient_representing_matrix(
    f::FreeModuleHom{DomType, CodType, Nothing}
  ) where {DomType<:FreeMod, CodType<:SubQuo}
  return matrix(f)*generator_matrix(codomain(f))
end

function representing_matrix(
    f::FreeModuleHom{DomType, CodType, Nothing}
  ) where {DomType<:FreeMod, CodType<:SubQuo}
  return matrix(f)
  A = ambient_representing_matrix(f)
  G = ambient_free_module(codomain(f))
  h = hom(domain(f), G, A)
  n = ngens(codomain(f))
  m = rank(domain(f))
  B = zero(MatrixSpace(base_ring(G), m, n))
  for i in 1:m
    c = coordinates(G(vec(A[i,:])), codomain(f))
    for j in 1:n
      B[i, j] = c[j]
    end
  end
  return B
end

# When both the domain and the codomain are SubQuos, return the matrix 
# A whose rows represent the images of the generators in the ambient 
# free module of the codomain.
function ambient_representing_matrix(
    f::SubQuoHom{DomType, CodType}
  ) where {DomType<:SubQuo, CodType<:SubQuo}
  return matrix(f)*generator_matrix(codomain(f))
  F = domain(f)
  G = ambient_free_module(codomain(f))
  R = base_ring(domain(f))
  A = zero(MatrixSpace(R, ngens(F), rank(G)))
  for i in 1:ngens(F)
    v = repres(f(F[i]))
    for j in 1:rank(G)
      A[i, j] = v[j]
    end
  end
  return A
end

function representing_matrix(
    f::SubQuoHom{DomType, CodType}
  ) where {DomType<:SubQuo, CodType<:SubQuo}
  return matrix(f)
  M = domain(f)
  m = ngens(M)
  R = base_ring(M)
  F = FreeMod(R, m)
  A = ambient_representing_matrix(f)
  G = ambient_free_module(codomain(f))
  h = hom(F, G, A) 
  n = ngens(codomain(f))
  B = zero(MatrixSpace(R, m, n))
  for i in 1:m
    v = G(vec(A[i,:]))
    c = coordinates(v, codomain(f))
    for j in 1:n
      B[i, j] = c[j]
    end
  end
  return B
end

function representing_matrix(
    f::SubQuoHom{DomType, CodType}
  ) where {DomType<:SubQuo, CodType<:FreeMod}
  return matrix(f)
  F = domain(f)
  G = codomain(f)
  R = base_ring(domain(f))
  A = zero(MatrixSpace(R, ngens(F), rank(G)))
  for i in 1:ngens(F)
    v = repres(f(F[i]))
    for j in 1:rank(G)
      A[i, j] = v[j]
    end
  end
  return A
end

# For a SubQuo M = (im A + im B)/(im B) for matrices A and B this returns A.
function generator_matrix(M::SubQuo) 
  R = base_ring(M)
  g = ambient_representatives_generators(M) # This passes through way too many conversions!
                                            # Try to implement this with more low-level getters.
  r = length(g)
  n = rank(ambient_free_module(M))
  A = zero(MatrixSpace(R, r, n))
  for i in 1:r
    for j in 1:n
      A[i, j] = g[i][j]
    end
  end
  return A
end

# For a SubQuo M = (im A + im B)/(im B) for matrices A and B this returns B.
function relations_matrix(M::SubQuo)
  R = base_ring(M)
  g = relations(M) # This passes through way too many conversions!
                   # Try to implement this with more low-level getters.
  r = length(g)
  n = rank(ambient_free_module(M))
  A = zero(MatrixSpace(R, r, n))
  for i in 1:r
    for j in 1:n
      A[i, j] = g[i][j]
    end
  end
  return A
end

function as_matrix(v::FreeModElem)
  R = base_ring(parent(v))
  n = rank(parent(v))
  A = zero(MatrixSpace(R, 1, n))
  for i in 1:n
    A[1, i] = v[i]
  end
  return A
end

function as_matrix(F::FreeMod, v::Vector{T}) where {T<:FreeModElem}
  all(x->parent(x) === F, v) || error("elements do not belong to the same module")
  R = base_ring(F)
  n = rank(F)
  m = length(v)
  m == 0 && return zero(MatrixSpace(R, m, n))
  A = zero(MatrixSpace(R, m, n))
  for i in 1:m
    for j in 1:n
      A[i, j] = v[i][j]
    end
  end
  return A
end

as_matrix(F::FreeMod, v::Vector{T}) where {T<:SubQuoElem} = as_matrix(F, repres.(v))

function as_matrix(v::SRow{T}, n::Int) where {T<:RingElem} 
  w = zero(MatrixSpace(base_ring(v), 1, n))
  for (i, a) in v
    w[1, i] = a
  end
  return w
end
  

function sub(F::FreeMod{T}, A::MatElem{T}) where {T} 
  M = SubQuo(F, A, zero(MatrixSpace(base_ring(F), 1, rank(F))))
  inc = hom(M, F, ambient_representatives_generators(M))
  inc.matrix = A
  return M, inc
end

function quo(F::FreeMod{T}, A::MatElem{T}) where {T}
  E = one(MatrixSpace(base_ring(F), rank(F), rank(F)))
  M = SubQuo(F, E, A)
  proj = hom(F, M, gens(M))
  proj.matrix = E
  return M, proj
end

  
function kernel(
    f::FreeModuleHom{DomType, CodType, Nothing}
  ) where {
    T<:AbsLocalizedRingElem, 
    DomType<:FreeMod{T},
    CodType<:FreeMod{T}
  }
  S = base_ring(domain(f))
  A = representing_matrix(f)
  B, D = clear_denominators(A)
  Fb = base_ring_module(domain(f))
  Gb = base_ring_module(codomain(f))
  fb = hom(Fb, Gb, B)
  Kb, incb = kernel(fb)
  Cb = representing_matrix(incb)
  C = change_base_ring(S, Cb*D)
  K, inc = sub(domain(f), C)
  return K, inc
end

function cokernel(
    f::FreeModuleHom{DomType, CodType, Nothing}
  ) where {
    T<:AbsLocalizedRingElem, 
    DomType<:FreeMod{T},
    CodType<:FreeMod{T}
  }
  return sub(codomain(f), representing_matrix(f))
end

function coordinates(u::FreeModElem{T}, M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  S = base_ring(parent(u))
  R = base_ring(S)
  F = ambient_free_module(M)
  F === parent(u) || error("element does not belong to the correct module")

  # First check, whether this element is already contained in the `pre_saturated_module`
  (u_clear, d_u) = clear_denominators(u)
  Mb = pre_saturated_module(M)
  if represents_element(u_clear, Mb)
    yc = as_matrix(coordinates(u_clear, Mb), ngens(Mb))
    Tr = pre_saturation_data_gens(M)
    # We have yc ⋅ A' ≡ uc with A' = Tr ⋅ generator_matrix(M) and d_u ⋅ u = uc.
    # Then (1//d_u) ⋅ yc ⋅ T are the coordinates of u in the original generators 
    # generator_matrix(M).
    return S(one(R), d_u)*(yc*Tr) 
  end

  # If u_clear was not yet found in the presaturated module, do the full search.
  A = generator_matrix(M)
  r = nrows(A)
  B = relations_matrix(M)
  s = nrows(B)
  (success, x) = has_solution(vcat(A, B), as_matrix(u))
  success || error("element of FreeMod does not represent an element of the SubQuo")

  # In the affirmative case we have u = u'//d_u with u' not a representative of an 
  # element in the `pre_saturated_module(M)`. But the computations yield 
  #
  #   u = u'//d_u = y⋅A + z⋅B = v + w = v'//d_v + w'//d_w
  # 
  # with x = [y z]. Now we would like to cache v' as a new generator for the 
  # `pre_saturated_module(M)` and w' as a new relation of it. 
  y = x[1, 1:r]
  z = x[1, r+1:r+s]
  v = x*A
  w = y*B
  (v_clear, d_v) = clear_denominators(v)
  (w_clear, d_w) = clear_denominators(w)

  Mb = pre_saturated_module(M)
  Mbext = SubQuo(ambient_free_module(Mb), 
                 vcat(generator_matrix(Mb), v_clear), 
                 vcat(relations_matrix(Mb), w_clear))
  Tr = pre_saturation_data_gens(M) 
  # The matrix Tr ∈ Sᵖˣᵐ is the transition matrix from the 
  # A = `generator_matrix(M)` to A' = `generator_matrix(Mb)`, i.e.
  #
  #   Tr ⋅ A = A'. 
  #
  # For the extended set of generators in the pre-saturation, we 
  # need to extend this matrix by one more row given by d_v ⋅ y.
  set_attribute!(M, :pre_saturation_data_gens, 
                 vcat(Tr, d_v*y)
                )
  Tr = pre_saturation_data_rels(M)
  set_attribute!(M, :pre_saturation_data_rels, 
                 vcat(Tr, d_w*z)
                )
  set_attribute!(M, :pre_saturated_module, Mbext)
  # finally, return the computed coordinates
  return x[1, 1:r]
end

function kernel(
    f::FreeModuleHom{DomType, CodType, Nothing}
  ) where {
    T<:AbsLocalizedRingElem,
    DomType<:FreeMod{T},
    CodType<:SubQuo{T}
  }
  F = domain(f)
  S = base_ring(domain(f))
  M = ambient_representing_matrix(f)
  B = relations_matrix(codomain(f))
  MB = vcat(M, B)
  Lext = syz(MB)
  L = change_base_ring(S, Lext[:, 1:ncols(M)])
  K, inc = sub(F, L) 
  return K, inc
end
  
function kernel(
    f::SubQuoHom{DomType, CodType}
  ) where {
    T<:AbsLocalizedRingElem,
    DomType<:SubQuo{T},
    CodType<:ModuleFP{T}
  }
  F = ambient_free_module(domain(f))
  S = base_ring(F)
  A = generator_matrix(domain(f))
  H = FreeMod(S, nrows(A))
  h = hom(H, domain(f), one(MatrixSpace(S, rank(H), rank(H))))
  K, iK = kernel(hom(H, codomain(f), representing_matrix(f)))
  result = SubQuo(F, representing_matrix(iK)*generator_matrix(domain(f)), relations_matrix(domain(f)))
  return result, hom(result, domain(f), representing_matrix(iK))
end

function represents_element(u::FreeModElem{T}, M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  u_clear, d_u = clear_denominators(u)
  represents_element(u_clear, pre_saturated_module(M)) && return true
  
  # If u_clear was not yet found in the presaturated module, do the full search.
  A = generator_matrix(M)
  r = nrows(A)
  B = relations_matrix(M)
  s = nrows(B)
  (success, x) = has_solution(vcat(A, B), as_matrix(u))
  success || return false

  # In the affirmative case we have u = u'//d_u with u' not a representative of an 
  # element in the `pre_saturated_module(M)`. But the computations yield 
  #
  #   u = u'//d_u = y⋅A + z⋅B = v + w = v'//d_v + w'//d_w
  # 
  # with x = [y z]. Now we would like to cache v' as a new generator for the 
  # `pre_saturated_module(M)` and w' as a new relation of it. 
  y = x[1, 1:r]
  z = x[1, r+1:r+s]
  v = y*A
  w = z*B
  (v_clear, d_v) = clear_denominators(v)
  (w_clear, d_w) = clear_denominators(w)

  Mb = pre_saturated_module(M)
  Mbext = SubQuo(ambient_free_module(Mb), 
                 vcat(generator_matrix(Mb), v_clear), 
                 vcat(relations_matrix(Mb), w_clear))
  Tr = pre_saturation_data_gens(M) 
  # The matrix Tr ∈ Sᵖˣᵐ is the transition matrix from the 
  # A = `generator_matrix(M)` to A' = `generator_matrix(Mb)`, i.e.
  #
  #   Tr ⋅ A = A'. 
  #
  # For the extended set of generators in the pre-saturation, we 
  # need to extend this matrix by one more row given by d_v ⋅ y.
  set_attribute!(M, :pre_saturation_data_gens, 
                 vcat(Tr, d_v*y)
                )
  Tr = pre_saturation_data_rels(M)
  set_attribute!(M, :pre_saturation_data_rels, 
                 vcat(Tr, d_w*z)
                )
  set_attribute!(M, :pre_saturated_module, Mbext)

  return true
end
