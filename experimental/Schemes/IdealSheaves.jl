export IdealSheaf

export scheme, covering, getindex, subscheme, covered_patches, extend!, ideal_dict

export ideal_sheaf_type

export is_regular_sequence, as_smooth_lci, is_defined_on

export order_on_divisor

@attributes mutable struct IdealSheaf{
    CoveredSchemeType<:AbsCoveredScheme,
    CoveringType<:Covering
  }
  X::CoveredSchemeType # the parent
  C::CoveringType # the covering on which this sheaf is defined
  ideals::Dict{AbsSpec, Ideal}

  # fields for caching
  cached_ideals::Dict{AbsSpec, Ideal}

  function IdealSheaf(
      X::AbsCoveredScheme, 
      C::Covering,
      I::Dict{<:AbsSpec, <:Ideal};
      check::Bool=true
    )
    C in coverings(X) || error("reference covering not found")
    for X in keys(I)
      X in C || error("affine patch not found")
      base_ring(I[X]) == OO(X) || error("ideal does not belong to the correct ring")
    end

    # make sure that all of X is indeed covered by patches on which the sheaf is defined
    for U in basic_patches(C)
      if !haskey(I, U) 
        haskey(affine_refinements(C), U) || error("patch $U not covered by the given ideal sheaf")

        Uref = affine_refinements(C)[U]
        found = false
        for (V, a) in Uref
          if all(x->haskey(I, x), affine_patches(V)) 
            found = true
            break
          end
        end
        !found && error("patch $U not covered by the given ideal sheaf")
      end
    end

    if check # Do the more expensive checks whether the generated ideals coincide on the overlaps
      for U in keys(I)
        for V in keys(I)
          f, g, incU, incV = intersect(U, V, C)
          fext = compose(f, incV)
          gext = compose(g, incU)
          WU = domain(f)
          WV = domain(g)
          for D in affine_patches(WU) 
            incD = inclusion_map(D, U)
            pullback(incD)(I[U]) == pullback(fext[D])(I[V]) || error("ideals do not coincide on the patches $U and $V")
          end
        end
      end


    end
    return new{typeof(X), typeof(C)}(X, C, I)
  end
end

### getter methods

scheme(I::IdealSheaf) = I.X
covering(I::IdealSheaf) = I.C
covered_patches(I::IdealSheaf) = [U for U in keys(I.ideal_gens)]

function getindex(I::IdealSheaf, U::Spec)
  haskey(I.ideals, U) && return I.ideals[U] 
  J = ideal(OO(U), [zero(OO(U))])
  I.ideals[U] = J
  return J
end

ideal_dict(I::IdealSheaf) = I.ideals

set_name!(X::IdealSheaf, name::String) = set_attribute!(X, :name, name)
name_of(X::IdealSheaf) = get_attribute(X, :name)::String
has_name(X::IdealSheaf) = has_attribute(X, :name)

function ideal_sheaf_type(::Type{T}) where {T<:CoveredScheme}
  return IdealSheaf{T, covering_type(T)}
end

ideal_sheaf_type(X::T) where {T<:CoveredScheme} = ideal_sheaf_type(typeof(X))

function IdealSheaf(X::ProjectiveScheme, g::Vector{RingElemType}) where {RingElemType<:MPolyElem_dec}
  X_covered = as_covered_scheme(X)
  C = default_covering(X_covered)
  r = fiber_dimension(X)
  I = Dict{AbsSpec, Ideal}()
  for i in 0:r
    I[C[i+1]] = ideal(OO(C[i+1]), dehomogenize(X, i).(g))
  end
  return IdealSheaf(X_covered, C, I, check=false)
end

function IdealSheaf(
    X::ProjectiveScheme, 
    C::Covering, 
    g::Vector{RingElemType}
  ) where {RingElemType<:MPolyElem_dec}
  X_covered = as_covered_scheme(X)
  r = fiber_dimension(X)
  I = Dict{AbsSpec, Ideal}()
  for U in patches(C)
    I[U] = ideal(OO(U), dehomogenize(X, U).(g))
  end
  return IdealSheaf(X_covered, C, I, check=false)
end

# this constructs the empty ideal sheaf
function IdealSheaf(X::CoveredScheme) 
  C = default_covering(X)
  I = Dict{AbsSpec, Ideal}()
  return IdealSheaf(X, C, I, check=false)
end

# internal routine to set up an ideal sheaf by automatic extension 
# from one prescribed set of generators on one affine patch
function IdealSheaf(X::CoveredScheme, C::Covering, U::Spec, g::Vector{RET}) where {RET<:MPolyElem}
  C in coverings(X) || error("the covering does not belong to the scheme")
  U in patches(C) || error("the affine open patch does not belong to the covering")
  for f in g
    parent(f) == ambient_ring(U) || error("the generators do not belong to the correct ring")
  end
  D = Dict{AbsSpec, Ideal}()
  D[U] = ideal(OO(U), g)
  D = extend!(C, D, check=false)
  I = IdealSheaf(X, C, D, check=false)
  return I
end

# more user facing routine with an automatic lookup of the associated affine patch.
# Warning: This might be ambiguous and lead to unexpected results since one affine 
# patch can be used in different coverings!
function IdealSheaf(X::CoveredScheme, g::Vector{RET}) where {RET<:MPolyElem} 
  length(g) == 0 && IdealSheaf(X)
  R = parent(g[1])
  for i in 2:length(g)
    R == parent(g[i]) || error("elements do not belong to the same ring")
  end
  for C in coverings(X)
    for U in patches(C)
      R == ambient_ring(U) && return IdealSheaf(X, C, U, g)
    end
  end
  error("the given set of generators could not be associated to an affine patch of the scheme")
end

function IdealSheaf(X::CoveredScheme, C::Covering, g::Vector{RET}) where {RET<:MPolyElem} 
  length(g) == 0 && IdealSheaf(X)
  R = parent(g[1])
  for i in 2:length(g)
    R == parent(g[i]) || error("elements do not belong to the same ring")
  end
  C in coverings(X) || error("covering is not listed")
  for U in patches(C)
    R == base_ring(OO(U)) && return IdealSheaf(X, C, U, g)
  end
  error("the given set of generators could not be associated to an affine patch of the scheme")
end

# pullback of an ideal sheaf for internal use between coverings of the same scheme
function (F::CoveringMorphism)(I::IdealSheaf)
  X = scheme(I)
  D = codomain(F)
  D == covering(I) || error("ideal sheaf is not defined on the correct covering")
  C = domain(F)
  new_dict = Dict{AbsSpec, Ideal}()

  # go through the patches of C and pull back the generators 
  # whenever they are defined on the target patch
  for U in patches(C)
    f = F[U]
    V = codomain(f)
    # for the basic patches here
    if haskey(ideal_dict(I), V)
      new_dict[U] = ideal(OO(U), pullback(f).(I[V]))
    end
    # check for affine refinements
    if haskey(affine_refinements(D), V)
      Vrefs = affine_refinements(D)[V]
      # pull back the refinement
      for W in Vrefs
        h = pullback(f).(gens(W))
        # take care to discard possibly empty preimages of patches
        j = [i for i in 1:length(h) if !iszero(h)]
        Wpre = SpecOpen(U, h[j])
        add_affine_refinement!(C, Wpre)
        for i in 1:length(j)
          if haskey(ideal_dict(I), Wpre[i])
            new_dict[Wpre[i]] = lifted_numerator.(pullback(f).(I[V[j[i]]]))
          end
        end
      end
    end
  end
  return IdealSheaf(X, C, new_dict)
end

function +(I::IdealSheaf, J::IdealSheaf) 
  X = scheme(I)
  X == scheme(J) || error("ideal sheaves are not defined over the same scheme")
  new_dict = Dict{AbsSpec, Ideal}()
  CI = covering(I)
  CJ = covering(J)
  CI == CJ || error("addition on ideal sheaves on different coverings is not implemented")
  for U in patches(CI)
    new_dict[U] = I[U] + J[U]
  end
  return IdealSheaf(X, CI, new_dict, check=false)
end

function *(I::IdealSheaf, J::IdealSheaf) 
  X = scheme(I)
  X == scheme(J) || error("ideal sheaves are not defined over the same scheme")
  new_dict = Dict{AbsSpec, Ideal}()
  CI = covering(I)
  CJ = covering(J)
  CI == CJ || error("addition on ideal sheaves on different coverings is not implemented")
  for U in patches(CI)
    new_dict[U] = I[U] * J[U]
  end
  return IdealSheaf(X, CI, new_dict, check=false)
end

@Markdown.doc """
    simplify!(I::IdealSheaf)

Replaces the set of generators of the ideal sheaf by a minimal 
set of random linear combinations in every affine patch. 
"""
function simplify!(I::IdealSheaf)
  for U in patches(covering(I))
    n = length(I[U]) 
    n == 0 && continue
    J = ideal(OO(U), I[U])
    R = base_ring(OO(U))
    kk = coefficient_ring(R)
    new_gens = elem_type(base_ring(OO(U)))[]
    K = ideal(OO(U), new_gens) 
    while !issubset(J, K)
      new_gen = dot([rand(kk, 1:100) for i in 1:n], I[U])
      while new_gen in K
        new_gen = dot([rand(kk, 1:100) for i in 1:n], I[U])
      end
      push!(new_gens, new_gen)
      K = ideal(OO(U), new_gens)
    end
    I[U] = new_gens
  end
  return I
end


### Given an ideal sheaf I, return the associated 
# subscheme
#
# **Note:** This must be cached!
#
# TODO: Also return the associated closed embedding.
function subscheme(I::IdealSheaf) 
  X = scheme(I)
  C = covering(I)
  new_patches = [subscheme(C[i], I[C[i]]) for i in 1:npatches(C)]
  new_glueings = Dict{Tuple{AbsSpec, AbsSpec}, AbsGlueing}()
  for (U, V) in keys(glueings(C))
    i = C[U]
    j = C[V]
    Unew = new_patches[i]
    Vnew = new_patches[j]
    G = C[U, V]
    new_glueings[(Unew, Vnew)] = restriction(C[U, V], Unew, Vnew, check=false)
    new_glueings[(Vnew, Unew)] = inverse(new_glueings[(Unew, Vnew)])
  end
  Cnew = Covering(new_patches, new_glueings, check=false)
  return CoveredScheme(Cnew)
end


@Markdown.doc """
    extend!(C::Covering, D::Dict{SpecType, IdealType}) where {SpecType<:Spec, IdealType<:Ideal}

For ``C`` a covering and ``D`` a dictionary holding vectors of 
polynomials on affine patches of ``C`` this function extends the 
collection of polynomials over all patches in a compatible way; 
meaning that on the overlaps the restrictions of either two sets 
of polynomials coincides.

This proceeds by crawling through the glueing graph and taking 
closures in the patches ``Uⱼ`` of the subschemes 
``Zᵢⱼ = V(I) ∩ Uᵢ ∩ Uⱼ`` in the intersection with a patch ``Uᵢ`` 
on which ``I`` had already been described.
"""
function extend!(
    C::Covering, D::Dict{AbsSpec, Ideal};
    check::Bool=true
  )
  gg = glueing_graph(C)
  # push all nodes on which I is known in a heap
  dirty_patches = collect(keys(D))
  while length(dirty_patches) > 0
    U = pop!(dirty_patches)
    N = neighbor_patches(C, U)
    Z = subscheme(U, D[U])
    for V in N
      # check whether this node already knows about D
      haskey(D, V)  && continue

      # if not, extend D to this patch
      f, _ = glueing_morphisms(C[V, U])
      pZ = preimage(f, Z)
      ZV = closure(pZ, V)
      D[V] = ideal(OO(V), defining_ideal(ZV))
      V in dirty_patches || push!(dirty_patches, V)
      if check
        f, g, incU, incV = intersect(U, V, C)
        fext = compose(f, incV)
        gext = compose(g, incU)
        WU = domain(f)
        WV = domain(g)
        for W in affine_patches(WU) 
          incW = inclusion_map(W, U)
          I1 = pullback(incW)(D[U]) 
          I2 = pullback(fext[W])(D[V]) 
          !(I1 == I2) || error("ideals do not coincide on the intersection")
        end
      end
    end
  end
  for U in basic_patches(C) 
    if !haskey(D, U)
      D[U] = ideal(OO(U), zero(OO(U)))
    end
  end
  # TODO: Extend trivially to disjoint components?
  return D
end

function Base.show(io::IO, I::IdealSheaf)
  if has_name(I)
    print(io, name_of(I))
    return 
  end
  print(io, "sheaf of ideals on $(scheme(I))")
end

function canonically_isomorphic(I::T, J::T) where{T<:IdealSheaf}
  X = scheme(I)
  X == scheme(J) || return false
  C = covering(I)
  C == covering(J) || error("comparison not implemented")
  for U in patches(C)
    if I[U] != J[U]
      return false
    end
  end
  return true
end

# prepares a refinement C' of the covering for the ideal sheaf I 
# such that I can be generated by a regular sequence defining a smooth 
# local complete intersection subscheme in every patch U of C' and 
# returns the ideal sheaf with those generators on C'.
#function as_smooth_lci(
#    I::IdealSheaf;
#    verbose::Bool=false,
#    check::Bool=true,
#    codimension::Int=dim(scheme(I))-dim(subscheme(I)) #assumes both scheme(I) and its subscheme to be equidimensional
#  )
#  X = scheme(I)
#  C = covering(I)
#  SpecType = affine_patch_type(C)
#  PolyType = poly_type(SpecType)
#  new_gens_dict = Dict{SpecType, Vector{PolyType}}()
#  for U in patches(C)
#    V, spec_dict = as_smooth_lci(U, I[U], 
#                                 verbose=verbose, 
#                                 check=check, 
#                                 codimension=codimension) 
#    add_affine_refinement!(C, V)
#    merge!(new_gens_dict, spec_dict)
#  end
#  Iprep = IdealSheaf(X, C, new_gens_dict)
#  set_attribute!(Iprep, :is_regular_sequence, true)
#  return Iprep
#end
#
#function as_smooth_lci(
#    U::Spec, g::Vector{T}; 
#    verbose::Bool=false,
#    check::Bool=true,
#    codimension::Int=dim(U)-dim(subscheme(U, g)) # this assumes both U and its subscheme to be equidimensional
#  ) where {T<:MPolyElem}
#  verbose && println("preparing $g as a local complete intersection on $U")
#  f = numerator.(gens(localized_modulus(OO(U))))
#  f = [a for a in f if !iszero(a)]
#  verbose && println("found $(length(f)) generators for the ideal defining U")
#  h = vcat(f, g)
#  r = length(f)
#  s = length(g)
#  Dh = jacobi_matrix(h)
#  (ll, ql, rl, cl) = _non_degeneration_cover(subscheme(U, g), Dh, codimension + codim(U), 
#                          verbose=verbose, check=check, 
#                          restricted_columns=[collect(1:r), [r + k for k in 1:s]])
#
#  n = length(ll)
#  # first process the necessary refinements of U
#  # The restricted columns in the call to _non_degenerate_cover 
#  # assure that the first codim(U) entries of every cl[i] are 
#  # indices of some element of f. However, we can discard these, 
#  # as they are trivial generators of the ideal sheaf on U.
#  minor_list = [det(Dh[rl[i], cl[i]]) for i in 1:n]
#  V = Vector{open_subset_type(U)}()
#  SpecType = typeof(U)
#  PolyType = poly_type(U)
#  spec_dict = Dict{SpecType, Vector{PolyType}}()
#  g = Vector{PolyType}()
#  W = SpecOpen(U, minor_list)
#  for i in 1:n
#    spec_dict[W[i]] = h[cl[i][codim(U)+1:end]]
#  end
#  return W, spec_dict
#end
#

function is_prime(I::IdealSheaf) 
  return all(U->is_prime(I[U]), patches(default_covering(scheme(I))))
end

function _minimal_power_such_that(I::Ideal, P::PropertyType) where {PropertyType}
  whole_ring = ideal(base_ring(I), [one(base_ring(I))])
  P(whole_ring) && return (0, whole_ring)
  P(I) && return (1, I)
  I_powers = [(1,I)]

  while !P(last(I_powers)[2])
    push!(I_powers, (last(I_powers)[1]*2, last(I_powers)[2]^2))
  end
  upper = pop!(I_powers)
  lower = pop!(I_powers)
  while upper[1]!=lower[1]+1
    middle = pop!(I_powers)
    middle = (lower[1]+middle[1], lower[2]*middle[2])
    if P(middle[2])
      upper = middle
    else
      lower = middle
    end
  end
  return upper
end

### resolve another compatibility issue
saturated_ideal(I::MPolyIdeal) = I

function order_on_divisor(
    f::VarietyFunctionFieldElem, 
    I::IdealSheaf;
    check::Bool=true
  )
  @show "call"
  if check
    @show "check"
    is_prime(I) || error("ideal sheaf must be a sheaf of prime ideals")
  end
  X = scheme(I) 
  X == variety(parent(f)) || error("schemes not compatible")
  C = covering(I)
  C == default_covering(X) || error("change of coverings not implemented")
  
  order_dict = Dict{AbsSpec, Int}()
  for U in patches(C)
    @show U
    L, map = Localization(OO(U), 
                          MPolyComplementOfPrimeIdeal(saturated_ideal(I[U]))
                         )
    typeof(L)<:Union{MPolyLocalizedRing{<:Any, <:Any, <:Any, <:Any, 
                                        <:MPolyComplementOfPrimeIdeal},
                     MPolyQuoLocalizedRing{<:Any, <:Any, <:Any, <:Any, 
                                           <:MPolyComplementOfPrimeIdeal}
                    } || error("localization was not successful")
    floc = f[U]
    @show floc
    a = numerator(floc)
    b = denominator(floc)
    # TODO: cache groebner bases in a reasonable way.
    P = L(prime_ideal(inverted_set(L)))
    @show gens(P)
    if one(L) in P 
      continue # the multiplicity is -∞ in this case and does not count
    end
    upper = _minimal_power_such_that(P, x->!(L(a) in x))[1]-1
    lower = _minimal_power_such_that(P, x->!(L(b) in x))[1]-1
    @show upper
    @show lower
    order_dict[U] = upper-lower
  end
  return minimum(values(order_dict))
end

### Compatibility fix
@attr function saturated_ideal(I::MPolyQuoIdeal) 
  A = base_ring(I)
  R = base_ring(A)
  return ideal(R, lift.(gens(I))) + modulus(A)
end
