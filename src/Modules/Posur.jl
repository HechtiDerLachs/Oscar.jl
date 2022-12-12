export kernel, cokernel, image, coordinates, represents_element
export syz, has_nonempty_intersection, base_ring_module

########################################################################
# 
# Generic code for localizations of finitely generated modules 
# following [1]
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
  D = zero_matrix(SMat, R, 0, m)
  #D = zero(MatrixSpace(R, m, m))
  B = zero(MatrixSpace(R, m, n))
  for i in 1:m
    d = lcm(vec(denominator.(A[i,:])))
    push!(D, sparse_row(R, [(i, d)]))
    #D[i,i] = d
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

# generic solution to the syzygy problem (thought of over the base ring)
function syz(A::MatrixElem)
  R = base_ring(A)
  m = nrows(A)
  n = ncols(A)
  F = FreeMod(R, m)
  G = FreeMod(R, n)
  f = hom(F, G, A)
  K, inc = kernel(f)
  return matrix(inc)
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
@doc Markdown.doc"""
    syz(A::MatrixElem)

For a matrix ``A ∈ Rᵐˣⁿ`` over a ring ``R`` this returns a matrix 
``L ∈ Rᵖˣᵐ`` whose rows generate the kernel of the homomorphism of 
free modules given by ``A``.
"""
function syz(A::MatrixElem{<:AbsLocalizedRingElem})
  B, D = clear_denominators(A)
  L = syz(B)
  return transpose(mul(transpose(D), transpose(L)))
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
@doc Markdown.doc"""
    has_nonempty_intersection(U::AbsMultSet, I::Ideal)

For a finitely generated ideal ``I ⊂ R`` and a multiplicative 
set ``U ⊂ R``, this checks whether the intersection ``U ∩ I`` 
is nonempty and returns a triple 

    (success, f, a).

In the affirmative case, `success` is `true`, ``f ∈ U ∩ I`` is 
some element in the intersection and ``a ∈ R¹ˣᵏ`` is a 
`Vector{elem_type(R)}` such that ``f = ∑ᵢ aᵢ⋅gᵢ`` where
``gᵢ`` are the elements in `gens(I)`.

When the intersection is empty, this returns `(false, f, a)`
with meaningless values for ``f`` and ``a``.

**Note:** When implementing methods of this function, it is 
recommended to choose ``f`` to be the 'least complex' in 
an appropriate sense for ``R``.
"""
function has_nonempty_intersection(U::AbsMultSet, I::Ideal)
  R = ambient_ring(U)
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
function has_solution(
    A::MatrixType, b::MatrixType;
    check::Bool=true
  ) where {T<:AbsLocalizedRingElem, MatrixType<:MatrixElem{T}}
  S = base_ring(A)
  R = base_ring(S)
  S === base_ring(b) || error("matrices must be defined over the same ring")
  nrows(b) == 1 || error("only matrices with one row are allowed!")
  B, D = clear_denominators(A)
  c, u = clear_denominators(b)
  (success, y, v) = has_solution(B, c, inverted_set(S), check=check)
  success || return (false, zero(MatrixSpace(S, 1, ncols(b))))
  # We have B = D⋅A and c = u ⋅ b as matrices. 
  # Now y⋅B = v⋅c ⇔ y⋅D ⋅A = v ⋅ u ⋅ b ⇔ v⁻¹ ⋅ u⁻¹ ⋅ y ⋅ D ⋅ A = b.
  # Take v⁻¹ ⋅ u⁻¹ ⋅ y ⋅ D to be the solution x of x ⋅ A = b.
  return (success, S(one(R), v*u[1,1])*change_base_ring(S, transpose(mul(transpose(D), transpose(y)))))
end

# This second version solves over the base ring and checks compatibility with 
# the given units.
function has_solution(
    A::MatrixType, b::MatrixType, U::AbsMultSet;
    check::Bool=true
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
  (success, u, a) = has_nonempty_intersection(U, I, check=check)
  success || return (false, zero(MatrixSpace(R, 1, ngens(I))), zero(R))
  l = a*L 
  return (success, l[1, 2:end], l[1,1])
end

########################################################################
# 
# Implementation of the generic code for the finitely presented modules
#
########################################################################

# for a free module F ≅ Sʳ over a localized ring S = R[U⁻¹] this 
# returns the module F♭ ≅ Rʳ.
@doc Markdown.doc"""
    base_ring_module(M::ModuleFP{T}) where {T<:AbsLocalizedRingElem}

For a finitely presented module ``M`` over a localized ring ``S = R[U⁻¹]`` 
this returns a module ``M'`` over ``R`` such that ``M ≅ M'[U⁻¹]``.

** Note: ** Such a choice is not canonical in general! Whenever ``M`` is 
not a free module, the user needs to specify a `base_ring_module` of ``M``.
If ``M`` arises as a localization of some ``R``-module ``M'``, then 
this connection is cached here. 
"""
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
  return get_attribute(M, :pre_saturation_data_gens)::SMat{elem_type(base_ring(M))}
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
  return get_attribute(M, :pre_saturation_data_rels)::SMat{elem_type(base_ring(M))}
end

base_ring_module_map_type(::Type{FreeMod{T}}) where {T<:AbsLocalizedRingElem} = morphism_type(base_ring_module_type(FreeMod{T}), FreeMod{T})
base_ring_module_map_type(F::FreeMod{T}) where {T<:AbsLocalizedRingElem} = base_ring_module_map_type(typeof(F))

# For a homomorphism of free modules over the same ring this returns the
# representing matrix.
function representing_matrix(f::FreeModuleHom{ModType, ModType, Nothing}) where {ModType<:FreeMod}
  return matrix(f)
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
end

# When both the domain and the codomain are SubQuos, return the matrix 
# A whose rows represent the images of the generators in the ambient 
# free module of the codomain.
function ambient_representing_matrix(
    f::SubQuoHom{DomType, CodType}
  ) where {DomType<:SubQuo, CodType<:SubQuo}
  return matrix(f)*generator_matrix(codomain(f))
end

function representing_matrix(
    f::SubQuoHom{DomType, CodType}
  ) where {DomType<:SubQuo, CodType<:SubQuo}
  return matrix(f)
end

function representing_matrix(
    f::SubQuoHom{DomType, CodType}
  ) where {DomType<:SubQuo, CodType<:FreeMod}
  return matrix(f)
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
  C = change_base_ring(S, transpose(mul(transpose(D), transpose(Cb))))
  #C = change_base_ring(S, Cb*D)
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
  return quo(codomain(f), representing_matrix(f))
end

function image(
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
    # yc = as_matrix(coordinates(u_clear, Mb), ngens(Mb))
    # Tr = pre_saturation_data_gens(M)
    # # We have yc ⋅ A' ≡ uc with A' = Tr ⋅ generator_matrix(M) and d_u ⋅ u = uc.
    # # Then (1//d_u) ⋅ yc ⋅ T are the coordinates of u in the original generators 
    # # generator_matrix(M).
    # result = S(one(R), d_u)*(yc*Tr) 
    # return sparse_row(result)
    return S(one(R), d_u)*mul(change_base_ring(S, coordinates(u_clear, Mb)), 
                                               pre_saturation_data_gens(M))
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
                 #vcat(Tr, d_v*y)
                 push!(Tr, sparse_row(mul(change_base_ring(base_ring(y), d_v), y)))
                )
  Tr = pre_saturation_data_rels(M)
  set_attribute!(M, :pre_saturation_data_rels, 
                 #vcat(Tr, d_w*z)
                 push!(Tr, sparse_row(mul(change_base_ring(base_ring(z), d_w), z)))
                )
  set_attribute!(M, :pre_saturated_module, Mbext)
  # finally, return the computed coordinates
  result = x[1, 1:r]
  return sparse_row(result)
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
  L = change_base_ring(S, Lext[:, 1:nrows(M)])
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
                 #vcat(Tr, d_v*y)
                 push!(Tr, sparse_row(mul(change_base_ring(base_ring(M), d_v), y)))
                )
  Tr = pre_saturation_data_rels(M)
  set_attribute!(M, :pre_saturation_data_rels, 
                 #vcat(Tr, d_w*z)
                 push!(Tr, sparse_row(mul(change_base_ring(base_ring(M), d_w), z)))
                )
  set_attribute!(M, :pre_saturated_module, Mbext)

  return true
end

### coercion of elements from modules over the base ring
function (F::FreeMod{T})(a::FreeModElem) where {T<:AbsLocalizedRingElem}
  G = parent(a) 
  base_ring(F) == base_ring(G) || base_ring(base_ring(F)) == base_ring(G) || error("base rings are not compatible")
  rank(F) == rank(G) || error("modules does not have the same rank as the parent of the vector")
  c = Vector(a)
  return sum([a*e for (a, e) in zip(c, gens(F))])
end

function (M::SubQuo{T})(f::FreeModElem; check::Bool = true) where {T<:AbsLocalizedRingElem}
  F = ambient_free_module(M)
  base_ring(parent(f)) == base_ring(base_ring(M)) && return M(F(f))
  parent(f) == F || error("ambient free modules are not compatible")
  (check && represents_element(f, M)) || error("not a representative of a module element")
  v = coordinates(f, M) # This is not the cheapest way, but the only one for which 
                        # the constructors in the module code are sufficiently generic.
                        # Clean this up!
  return sum([a*M[i] for (i, a) in v])
end

function base_ring_module(M::SubQuo{T}) where {T<:AbsLocalizedRingElem}
  has_attribute(M, :base_ring_module) || error("there is no associated module over the base ring")
  get_attribute(M, :base_ring_module)::SubQuo{base_ring_elem_type(T)}
end

function set_base_ring_module(F::FreeMod{LRET}, N::FreeMod{BRET}) where {LRET<:AbsLocalizedRingElem, BRET<:RingElem}
  S = base_ring(F)
  R = base_ring(N)
  base_ring(S) == R || error("base rings are not compatible")
  rank(F) == rank(N) || error("ranks are not compatible")
  set_attribute!(F, :base_ring_module, N)
  return N
end

function set_base_ring_module(
    M::SubQuo{LRET}, N::SubQuo{BRET};
    check::Bool=true
  ) where {LRET<:AbsLocalizedRingElem, BRET<:RingElem}
  S = base_ring(M)
  R = base_ring(N)
  base_ring(S) == R || error("base rings are not compatible")
  F = ambient_free_module(M)
  base_ring_module(F) == ambient_free_module(N) || error("ambient free modules are not compatible")
  if check
    for g in ambient_representatives_generators(N)
      represents_element(F(g), M) || error("generators of the base ring module are not elements of the localization")
    end
    for g in relations(N)
      iszero(M(g)) || error("relations are not preserved")
    end
  end
  set_attribute!(F, :base_ring_module, N)
  return N
end


########################################################################
# 
# Further generic implementations of module code
#
########################################################################

function iszero(v::SubQuoElem{<:AbsLocalizedRingElem}) 
  M = parent(v)
  Mb = pre_saturated_module(M)
  w = repres(v)
  b = as_matrix(repres(v))
  all(x->iszero(x), b) && return true

  (u, d) = clear_denominators(w)
  iszero(Mb(u)) && return true

  B = relations_matrix(M)
  success, y = has_solution(b, B)
  !success && return false

  # Cache the new relation in the pre_saturated_module
  bb = as_matrix(u)
  Mbext = SubQuo(ambient_free_module(Mb), 
                 generator_matrix(Mb), 
                 vcat(relations_matrix(Mb), bb))
  # The matrix Tr ∈ Sᵖˣᵐ is the transition matrix from the 
  # B = `relations_matrix(M)` to B' = `relations_matrix(Mb)`, i.e.
  #
  #   Tr ⋅ B = B'. 
  #
  # For the extended set of relations in the pre-saturation, we 
  # need to extend this matrix by one more row given by d ⋅ y.
  Tr = pre_saturation_data_rels(M)
  set_attribute!(M, :pre_saturation_data_rels, 
                 #vcat(Tr, d*y)
                 push!(Tr, sparse_row(d*y))
                )
  set_attribute!(M, :pre_saturated_module, Mbext)
  return true
end

