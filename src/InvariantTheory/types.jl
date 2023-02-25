mutable struct PrimaryInvarsCache{T}
  invars::Vector{T} # primary invariants
  ideal::MPolyIdeal{T} # ideal generated by the primary invariants

  function PrimaryInvarsCache{T}() where {T <: MPolyRingElem}
    z = new{T}()
    z.invars = T[]
    return z
  end
end

mutable struct SecondaryInvarsCache{T}
  invars::Vector{T} # secondary invariants
  is_irreducible::BitVector # is_irreducible[i] == true iff invars[i] is irreducible
  sec_in_irred::Vector{Vector{Int}}
  # sec_in_irred[i] gives the "exponent vector" for invars[i] in the irreducible
  # secondary invariants (hence length(sec_in_irred[i]) is equal to the number of
  # irreducible secondary invariants and not to length(invars))

  function SecondaryInvarsCache{T}() where {T <: MPolyRingElem}
    z = new{T}()
    z.invars = T[]
    z.is_irreducible = BitVector()
    z.sec_in_irred = Vector{Vector{Int}}()
    return z
  end
end

mutable struct FundamentalInvarsCache{PolyRingElemT, PolyRingT}
  invars::Vector{PolyRingElemT} # fundamental invariants

  # Graded polynomial ring in length(invars) variables such that
  # deg(gens(S)[i]) == deg(invars[i])
  S::PolyRingT

  # Remember whether the fundamental invariants were computed from the primary
  # and secondary ones
  via_primary_and_secondary::Bool

  # For a primary or irreducible secondary invariant f, toS[f] gives the
  # representation of f as a polynomial in the fundamental invariants.
  # This field is only set, if via_primary_and_secondary is true.
  toS::Dict{PolyRingElemT, PolyRingElemT}

  function FundamentalInvarsCache{PolyRingElemT, PolyRingT}() where {PolyRingElemT <: MPolyRingElem, PolyRingT <: MPolyRing}
    z = new{PolyRingElemT, PolyRingT}()
    z.invars = PolyRingElemT[]
    return z
  end
end

mutable struct InvRing{FldT, GrpT, PolyRingElemT, PolyRingT, ActionT}
  field::FldT
  poly_ring::PolyRingT

  group::GrpT
  action::Vector{ActionT}

  modular::Bool

  primary::PrimaryInvarsCache{PolyRingElemT}
  secondary::SecondaryInvarsCache{PolyRingElemT}
  fundamental::FundamentalInvarsCache{PolyRingElemT, PolyRingT}

  presentation::MPolyAnyMap{MPolyQuoRing{PolyRingElemT}, PolyRingT, Nothing, PolyRingElemT}

  reynolds_operator::MapFromFunc{PolyRingT, PolyRingT}

  molien_series::Generic.Frac{QQPolyRingElem}

  function InvRing(K::FldT, G::GrpT, action::Vector{ActionT}) where {FldT <: Field, GrpT <: AbstractAlgebra.Group, ActionT}
    n = degree(G)

    # We want to use divrem w.r.t. degrevlex e.g. for the computation of
    # secondary invariants and fundamental invariants
    R, = grade(polynomial_ring(K, "x" => 1:n, cached = false, ordering = :degrevlex)[1], ones(Int, n))
    PolyRingT = typeof(R)
    PolyRingElemT = elem_type(R)
    z = new{FldT, GrpT, PolyRingElemT, PolyRingT, ActionT}()
    z.field = K
    z.poly_ring = R
    z.group = G
    z.action = action
    z.modular = true
    if iszero(characteristic(K))
      z.modular = false
    else
      if !iszero(mod(order(G), characteristic(K)))
        z.modular = false
      end
    end
    return z
  end
end

struct AllMonomials{PolyRingT}
  R::PolyRingT
  d::Int

  function AllMonomials{PolyRingT}(R::PolyRingT, d::Int) where PolyRingT
    @assert d >= 0
    return new{PolyRingT}(R, d)
  end
end

struct InvRingBasisIterator{InvRingT, ReynoldsT, IteratorT, PolyRingElemT, MatrixT}
  R::InvRingT
  degree::Int
  dim::Int
  reynolds::Bool

  # If we compute the basis twisted by a character, we cache the operator here
  # instead of in the invariant ring. Otherwise this is `nothing`.
  reynolds_operator::ReynoldsT

  monomials::IteratorT
  monomials_collected::Vector{PolyRingElemT}
  kernel::MatrixT # used iff reynolds == false
end

abstract type VectorSpaceIterator{FieldT, IteratorT, ElemT} end

# This takes a basis of a vector space as an iterator and then "iterates" the
# space in three "phases":
# 1) iterate the basis using basis_iterator, so return one basis element at
#    a time
# 2) iterate all possible sums of basis elements
# 3) return random linear combinations of the basis elements (with integer
#    coefficients bounded by rand_bound)
#
# We collect the basis while iterating it, so that multiple iteration over the
# same VectorSpaceIterator do not need to recompute it. basis_iterator_state
# must always be a state of basis_iterator, so that
# iterate(basis_iterator, basis_iterator_state) returns the next element in the
# basis coming after basis_collected[end].
mutable struct VectorSpaceIteratorRand{FieldT, IteratorT, ElemT} <: VectorSpaceIterator{FieldT, IteratorT, ElemT}
  field::FieldT
  basis_iterator::IteratorT
  basis_collected::Vector{ElemT}
  basis_iterator_state::Any # I don't know the type of this and I don't think there
                       # is a "type-stable" way of finding it out
  rand_bound::Int

  function VectorSpaceIteratorRand(K::FieldT, basis_iterator::IteratorT, bound::Int = 10^5) where {FieldT, IteratorT}
    VSI = new{FieldT, IteratorT, eltype(basis_iterator)}()
    VSI.field = K
    VSI.basis_iterator = basis_iterator
    VSI.basis_collected = eltype(basis_iterator)[]
    VSI.rand_bound = bound
    return VSI
  end
end

# The same things as for VectorSpaceIteratorRand apply besides that in "phase 3"
# all elements of the vector space are iterated in deterministic order (it is
# supposed to be finite after all).
mutable struct VectorSpaceIteratorFiniteField{FieldT, IteratorT, ElemT} <: VectorSpaceIterator{FieldT, IteratorT, ElemT}
  field::FieldT
  basis_iterator::IteratorT
  basis_collected::Vector{ElemT}
  basis_iterator_state::Any # I don't know the type of this and I don't think there
                       # is a "type-stable" way of finding it out

  function VectorSpaceIteratorFiniteField(K::FieldT, basis_iterator::IteratorT) where {FieldT <: Union{Nemo.fpField, Nemo.FpField, fqPolyRepField, FqPolyRepField}, IteratorT}
    VSI = new{FieldT, IteratorT, eltype(basis_iterator)}()
    VSI.field = K
    VSI.basis_iterator = basis_iterator
    VSI.basis_collected = eltype(basis_iterator)[]
    return VSI
  end
end

struct MSetPartitions{T}
  M::MSet{T}
  num_to_key::Vector{Int}
  key_to_num::Dict{T, Int}

  function MSetPartitions(M::MSet{T}) where T
    num_to_key = collect(keys(M.dict))
    key_to_num = Dict{T, Int}()
    for i = 1:length(num_to_key)
      key_to_num[num_to_key[i]] = i
    end
    return new{T}(M, num_to_key, key_to_num)
  end
end

mutable struct MSetPartitionsState
  f::Vector{Int}
  c::Vector{Int}
  u::Vector{Int}
  v::Vector{Int}
  a::Int
  b::Int
  l::Int

  function MSetPartitionsState(MSP::MSetPartitions)
    m = length(MSP.num_to_key)
    n = length(MSP.M)
    f = zeros(Int, n + 1)
    c = zeros(Int, n*m + 1)
    u = zeros(Int, n*m + 1)
    v = zeros(Int, n*m + 1)

    for j = 1:m
      c[j] = j
      u[j] = MSP.M.dict[MSP.num_to_key[j]]
      v[j] = MSP.M.dict[MSP.num_to_key[j]]
    end
    f[1] = 1
    f[2] = m + 1
    a = 1
    b = m + 1
    l = 1

    return new(f, c, u, v, a, b, l)
  end
end

# Handle vector spaces of multivariate polynomials by writing them in the basis
# of the monomials.
mutable struct BasisOfPolynomials{PolyRingT, FieldElemT}
  R::PolyRingT

  # Number the basis monomials, we identify a monomial with its exponent vector
  monomial_to_column::Dict{Vector{Int}, Int}

  # Write the polynomials coefficient-wise in the rows of a sparse matrix. The
  # column i contains the coefficients corresponding to the monomial m with
  # monomial_to_column[m] == i.
  M::SMat{FieldElemT}

  function BasisOfPolynomials(R::MPolyRing)
    K = coefficient_ring(R)
    B = new{typeof(R), elem_type(K)}()
    B.R = R
    B.monomial_to_column = Dict{Vector{Int}, Int}()
    B.M = sparse_matrix(K)
    return B
  end

  function BasisOfPolynomials(R::PolyRingT, polys::Vector{<: MPolyRingElem}) where {PolyRingT <: MPolyRing}
    return BasisOfPolynomials(R, polys, enumerate_monomials(polys))
  end

  function BasisOfPolynomials(R::PolyRingT, polys::Vector{<: MPolyRingElem}, monomial_to_column::Dict{Vector{Int}, Int}) where {PolyRingT <: MPolyRing}
    if isempty(polys)
      return BasisOfPolynomials(R)
    end

    K = coefficient_ring(R)
    B = new{typeof(R), elem_type(K)}()
    B.R = R

    B.monomial_to_column = monomial_to_column

    M = polys_to_smat(polys, monomial_to_column, copy = true)
    rref!(M, truncate = true)
    B.M = M

    return B
  end
end

# Cache power products (= monomials) of elements in `base` of certain degrees.
mutable struct PowerProductCache{RingType, T}
  # The base ring (needed for empty `base`)
  ring::RingType

  base::Vector{T}

  # Store all power products of degree d
  power_products::Dict{Int, Vector{T}}

  # The exponent vector of a power product w.r.t. `base`
  exponent_vectors::Dict{T, Vector{Int}}

  # Whether the exponent vectors for a certain degree were computed
  exponent_vectors_known::Dict{Int, Bool}

  # The last entry of `base` involved in the power product
  last_factor::Dict{T, Int}

  function PowerProductCache(R::S, base::Vector{T}) where {S <: Ring, T <: RingElem}
    power_products = Dict{Int, Vector{T}}()
    exponent_vectors = Dict{T, Vector{Int}}()
    exponent_vectors_known = Dict{Int, Bool}()
    last_factor = Dict{T, Int}()
    return new{typeof(R), T}(R, copy(base), power_products, exponent_vectors, exponent_vectors_known, last_factor)
  end
end
