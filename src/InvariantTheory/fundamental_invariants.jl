
################################################################################
#
#  King's algorithm
#
################################################################################

# Computes a d-truncated Gröbner basis of I
# TODO: This should not be in this file and integrated in the general groebner_basis
# functionality
function _groebner_basis(I::MPolyIdeal, d::Int; ordering::MonomialOrdering = default_ordering(base_ring(I)))
  singular_assure(I, ordering)
  R = I.gens.Sx
  J = Singular.Ideal(R, gens(I.gens.S)...)
  G = Singular.with_degBound(d) do
        return Singular.std(J)
      end
  BA = IdealGens(base_ring(I), G)
  return BA
end

# [Kin13, p. 5] See also [DK15, Algorithm 3.8.2]
function fundamental_invariants_via_king(RG::InvRing, beta::Int = 0)
  @assert !is_modular(RG)

  Rgraded = polynomial_ring(RG)
  R = forget_grading(Rgraded)
  # R needs to have the correct ordering for application of divrem
  @assert ordering(R) == :degrevlex
  ordR = degrevlex(gens(R))

  S = elem_type(R)[]
  G = IdealGens(R, elem_type(R)[])
  singular_assure(G, ordR)
  GO = elem_type(R)[]

  g = order(Int, group(RG))
  if is_cyclic(group(RG))
    dmax = g
  else
    # We get a somewhat better bound if the group is not cyclic, see [DK15, Theorem 3.2.8]
    if iseven(g)
      dmax = floor(Int, 3//4*g)
    else
      dmax = floor(Int, 5//8*g)
    end
  end
  if beta > 0 && beta < dmax
    dmax = beta
  end
  d = 1
  while d <= dmax
    if !isempty(S)
      I = ideal(R, GO)

      if total_degree(S[end]) == d - 2
        GO = gens(groebner_basis(I, ordering = ordR))
        if is_zero(dim(I))
          mons = gens(ideal(R, Singular.kbase(I.gb[ordR].S)))
          dmax = maximum( total_degree(f) for f in mons )
          d > dmax ? break : nothing
        end
        G = I.gb[ordR]
      elseif total_degree(S[end]) == d - 1
        G = _groebner_basis(I, d, ordering = ordR)
        GO = collect(G)
      end
    end

    # TODO: Properly wrap kbase (or reimplement it; an iterator would be lovely)
    mons = gens(ideal(R, Singular.kbase(G.S, d)))
    if isempty(mons)
      break
    end

    for m in mons
      f = forget_grading(reynolds_operator(RG, Rgraded(m)))
      if is_zero(f)
        continue
      end

      _, g = divrem(f, GO)
      if is_zero(g)
        continue
      end

      push!(S, inv(leading_coefficient(f))*f)
      push!(GO, g)
    end

    d += 1
  end

  invars_cache = FundamentalInvarsCache{elem_type(Rgraded), typeof(Rgraded)}()
  invars_cache.invars = [ Rgraded(f) for f in S ]
  invars_cache.via_primary_and_secondary = false
  invars_cache.S = graded_polynomial_ring(coefficient_ring(R), [ "y$i" for i = 1:length(S) ], [ total_degree(f) for f in S ])[1]
  return invars_cache
end

################################################################################
#
#  Via primary and secondary invariants
#
################################################################################

# By definition, an element of the irreducible secondary invariants cannot be
# written as a polynomial expression in the primary invariants and the other
# irreducible secondary invariants (note that this is also true in the modular
# case in OSCAR!).
# Hence if we take the primary and irreducible secondary invariants, we only have
# to make sure, that none of the *primary* invariants is in the algebra
# generated by the others.
function fundamental_invariants_via_primary_and_secondary(IR::InvRing)
  R = polynomial_ring(IR)
  K = coefficient_ring(R)

  invars_cache = FundamentalInvarsCache{elem_type(R), typeof(R)}()
  invars_cache.via_primary_and_secondary = true

  if isempty(irreducible_secondary_invariants(IR))
    # The easy case: there are no irreducible secondary invariants, so `IR` is
    # generated by the primary invariants

    invars_cache.invars = primary_invariants(IR)
    invars_cache.S = graded_polynomial_ring(K, [ "y$i" for i = 1:length(invars_cache.invars) ], [ total_degree(forget_grading(f)) for f in invars_cache.invars ])[1]
    invars_cache.toS = Dict{elem_type(R), elem_type(invars_cache.S)}(invars_cache.invars[i] => gen(invars_cache.S, i) for i = 1:length(invars_cache.invars))

    return invars_cache
  end

  invars = append!(irreducible_secondary_invariants(IR), primary_invariants(IR))

  res, rels = _minimal_subalgebra_generators_with_relations(invars, ideal(R, [ zero(R) ]), check = false, start = length(irreducible_secondary_invariants(IR)))

  # Sort the result by degree
  sp = sortperm(res, lt = (x, y) -> total_degree(forget_grading(x)) < total_degree(forget_grading(y)))
  res = res[sp]

  # Bookkeeping: we need to transform the relations in rels to the new ordering
  # (and potentially less variables)
  T, _ = graded_polynomial_ring(K, [ "y$i" for i = 1:length(res) ], [ total_degree(forget_grading(x)) for x in res ])

  invars_cache.invars = res
  invars_cache.S = T

  t = gens(T)[invperm(sp)]
  invars_cache.toS = Dict{elem_type(R), elem_type(T)}()
  for (f, g) in zip(invars, rels)
    invars_cache.toS[f] = g(t...)
  end
  return invars_cache
end

################################################################################
#
#  User functions
#
################################################################################

@doc raw"""
    fundamental_invariants(IR::InvRing, algorithm::Symbol = :default; beta::Int = 0)

Return a system of fundamental invariants for `IR`.

The result is cached, so calling this function again with argument `IR` 
will be fast and give the same result.

# Implemented Algorithms

In the non-modular case the function relies on King's algorithm [Kin13](@cite) which
finds a system of fundamental invariants directly, without computing primary and
secondary invariants.
If an upper bound for the degrees of fundamental invariants is known, this can be
supplied by the keyword argument `beta` and might result in an earlier termination
of the algorithm. By default, the algorithm uses the bounds from [DH00](@cite)
and [Sez02](@cite).

Alternatively, if specified by `algorithm = :primary_and_secondary`, the function computes
fundamental invariants from a collection of primary and irreducible secondary
invariants.
The optional keyword argument `beta` is ignored for this algorithm.

In the modular case, only the second method is available for theoretical reasons.

# Examples
```jldoctest
julia> K, a = CyclotomicField(3, "a")
(Cyclotomic field of order 3, a)

julia> M1 = matrix(K, [0 0 1; 1 0 0; 0 1 0])
[0   0   1]
[1   0   0]
[0   1   0]

julia> M2 = matrix(K, [1 0 0; 0 a 0; 0 0 -a-1])
[1   0        0]
[0   a        0]
[0   0   -a - 1]

julia> G = matrix_group(M1, M2)
Matrix group of degree 3 over Cyclotomic field of order 3

julia> IR = invariant_ring(G)
Invariant ring of
Matrix group of degree 3 over Cyclotomic field of order 3
with generators
AbstractAlgebra.Generic.MatSpaceElem{nf_elem}[[0 0 1; 1 0 0; 0 1 0], [1 0 0; 0 a 0; 0 0 -a-1]]

julia> fundamental_invariants(IR)
4-element Vector{MPolyDecRingElem{nf_elem, AbstractAlgebra.Generic.MPoly{nf_elem}}}:
 x[1]^3 + x[2]^3 + x[3]^3
 x[1]*x[2]*x[3]
 x[1]^6 + x[2]^6 + x[3]^6
 x[1]^3*x[2]^6 + x[1]^6*x[3]^3 + x[2]^3*x[3]^6
```
"""
function fundamental_invariants(IR::InvRing, algorithm::Symbol = :default; beta::Int = 0)
  if !isdefined(IR, :fundamental)
    if algorithm == :default
      algorithm = is_modular(IR) ? :primary_and_secondary : :king
    end

    if algorithm == :king
      IR.fundamental = fundamental_invariants_via_king(IR, beta)
    elseif algorithm == :primary_and_secondary
      IR.fundamental = fundamental_invariants_via_primary_and_secondary(IR)
    else
      error("Unsupported argument :$(algorithm) for algorithm")
    end
  end
  return copy(IR.fundamental.invars)
end
