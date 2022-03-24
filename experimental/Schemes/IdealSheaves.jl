export IdealSheaf

export scheme, covering, getindex, subscheme, covered_patches, extend!, ideal_dict

export ideal_sheaf_type

export is_regular_sequence, as_smooth_lci, is_defined_on

using Infiltrator
@attributes mutable struct IdealSheaf{
    CoveredSchemeType<:CoveredScheme,
    CoveringType<:Covering,
    SpecType<:Spec,
    RingElemType<:MPolyElem
  }
  X::CoveredSchemeType # Der parent
  C::CoveringType
  ideal_gens::Dict{SpecType, Vector{RingElemType}}

  # fields for caching
  cached_ideals::Dict{SpecType, Any}

  function IdealSheaf(
      X::CoveredSchemeType, 
      C::CoveringType, 
      I::Dict{SpecType, Vector{RingElemType}};
      check::Bool=true
    ) where {
      CoveredSchemeType<:CoveredScheme,
      CoveringType<:Covering,
      SpecType<:Spec,
      RingElemType<:MPolyElem
    }
    C in coverings(X) || error("reference covering not found")
    for X in keys(I)
      X in C || error("affine patch not found")
      for f in I[X]
        parent(f) == base_ring(OO(X)) || error("element does not belong to the correct ring")
      end
    end
    if check
      for ((X, Y), G) in glueings(C)
        # We also allow ideal sheaves that are not fully specified on all 
        # patches, assuming that canonical extension is possible.
        X in keys(I) || continue
        Y in keys(I) || continue
        (U, V) = glueing_domains(G)
        (f, g) = glueing_morphisms(G)
        for i in 1:npatches(U)
          inc = inclusion_map(U[i], X)
          pullback(inc)(ideal(OO(X), I[X])) == pullback(f[i])(ideal(OO(Y), I[Y])) || error("ideals do not coincide on the glueing of $X and $Y")
        end
        for j in 1:npatches(V)
          inc = inclusion_map(V[j], Y)
          I1 = pullback(inc)(ideal(OO(Y), I[Y])) 
          I2 = pullback(g[j])(ideal(OO(X), I[X]))
          pullback(inc)(ideal(OO(Y), I[Y])) == pullback(g[j])(ideal(OO(X), I[X])) || error("ideals do not coincide on the glueing of $X and $Y")
        end
      end
    end
    return new{CoveredSchemeType, CoveringType, SpecType, RingElemType}(X, C, I)
  end
end

### getter methods

scheme(I::IdealSheaf) = I.X
covering(I::IdealSheaf) = I.C
covered_patches(I::IdealSheaf) = [U for U in keys(I.ideal_gens)]

function getindex(I::IdealSheaf, U::Spec)
  haskey(I.ideal_gens, U) && return I.ideal_gens[U] 
  return poly_type(U)[]
end

ideal_dict(I::IdealSheaf) = I.ideal_gens
is_defined_on(I::IdealSheaf, U::Spec) = haskey(I.ideal_gens, U)

set_name!(X::IdealSheaf, name::String) = set_attribute!(X, :name, name)
name_of(X::IdealSheaf) = get_attribute(X, :name)::String
has_name(X::IdealSheaf) = has_attribute(X, :name)

function is_regular_sequence(I::IdealSheaf)
  if !has_attribute(I, :is_regular_sequence) 
    return false
  end
  return get_attribute(I, :is_regular_sequence)::Bool
end

function ideal_sheaf_type(X::T) where {T<:CoveredScheme}
  return IdealSheaf{T, covering_type(T), affine_patch_type(T), poly_type(affine_patch_type(T))}
end

function ideal_sheaf_type(::Type{T}) where {T<:CoveredScheme}
  return IdealSheaf{T, covering_type(T), affine_patch_type(T), poly_type(affine_patch_type(T))}
end

function setindex!(I::IdealSheaf, g::Vector{RET}, U::Spec) where {RET<:MPolyElem} 
  for f in g
    parent(f) == base_ring(OO(U)) || error("polynomials do not belong to the correct ring")
  end
  I.ideal_gens[U] = g
  return I
end

function IdealSheaf(X::ProjectiveScheme, g::Vector{RingElemType}) where {RingElemType<:MPolyElem_dec}
  X_covered = as_covered_scheme(X)
  C = default_covering(X_covered)
  r = fiber_dimension(X)
  I = Dict{affine_patch_type(X), Vector{poly_type(affine_patch_type(X))}}()
  for i in 0:r
    I[C[i+1]] = lifted_numerator.(dehomogenize(X, i).(g))
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
  I = Dict{affine_patch_type(X), Vector{poly_type(affine_patch_type(X))}}()
  for U in patches(C)
    I[U] = lifted_numerator.(dehomogenize(X, U).(g))
  end
  return IdealSheaf(X_covered, C, I, check=false)
end

# this constructs the empty ideal sheaf
function IdealSheaf(X::CoveredScheme) 
  C = default_covering(X)
  D = Dict{affine_patch_type(X), Vector{poly_type(affine_patch_type(X))}}()
  return IdealSheaf(X, C, D, check=false)
end

# internal routine to set up an ideal sheaf by automatic extension 
# from one prescribed set of generators on one affine patch
function IdealSheaf(X::CoveredScheme, C::Covering, U::Spec, g::Vector{RET}) where {RET<:MPolyElem}
  C in coverings(X) || error("the covering does not belong to the scheme")
  U in patches(C) || error("the affine open patch does not belong to the covering")
  for f in g
    parent(f) == base_ring(OO(U)) || error("the generators do not belong to the correct ring")
  end
  D = Dict{typeof(U), typeof(g)}()
  D[U] = [f for f in g if !iszero(OO(U)(f))]
  I = IdealSheaf(X, C, D)
  extend!(I)
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
      R == base_ring(OO(U)) && return IdealSheaf(X, C, U, g)
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
  SpecType = affine_patch_type(C)
  PolyType = poly_type(SpecType)
  new_dict = Dict{SpecType, Vector{PolyType}}()

  # go through the patches of C and pull back the generators 
  # whenever they are defined on the target patch
  for U in patches(C)
    f = F[U]
    V = codomain(f)
    # for the basic patches here
    if haskey(ideal_dict(I), V)
      new_dict[U] = lifted_numerator.(pullback(f).(I[V]))
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
  SpecType = affine_patch_type(X)
  PolyType = poly_type(SpecType)
  new_dict = Dict{SpecType, Vector{PolyType}}()
  CI = covering(I)
  CJ = covering(J)
  CI == CJ || error("addition on ideal sheaves on different coverings is not implemented")
  for U in patches(CI)
    new_dict[U] = vcat(I[U], J[U])
  end
  return IdealSheaf(X, CI, new_dict, check=false)
end

function *(I::IdealSheaf, J::IdealSheaf) 
  X = scheme(I)
  X == scheme(J) || error("ideal sheaves are not defined over the same scheme")
  SpecType = affine_patch_type(X)
  PolyType = poly_type(SpecType)
  new_dict = Dict{SpecType, Vector{PolyType}}()
  CI = covering(I)
  CJ = covering(J)
  CI == CJ || error("addition on ideal sheaves on different coverings is not implemented")
  for U in patches(CI)
    new_dict[U] = [f*g for f in I[U] for g in J[U]]
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
function subscheme(I::IdealSheaf) 
  X = scheme(I)
  C = covering(I)
  new_patches = [subscheme(C[i], I[C[i]]) for i in 1:npatches(C)]
  new_glueings = Dict{Tuple{affine_patch_type(C), affine_patch_type(C)}, glueing_type(C)}()
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
    extend!(I::IdealSheaf)

For ``I`` an ideal sheaf on a covered scheme ``X``, given with respect 
to a covering `C = {Uᵢ}` with ``I`` defined only on a subset of 
the affine patches, this extends the ideal sheaf to all of ``X``.

This proceeds by crawling through the glueing graph and taking 
closures in the patches ``Uⱼ`` of the subschemes 
``Zᵢⱼ = V(I) ∩ Uᵢ ∩ Uⱼ`` in the intersection with a patch ``Uᵢ`` 
on which ``I`` had already been described.
"""
function extend!(I::IdealSheaf)
  X = scheme(I)
  C = covering(I)
  gg = glueing_graph(C)
  # push all nodes on which I is known in a heap
  dirty_patches = covered_patches(I)
  while length(dirty_patches) > 0
    U = pop!(dirty_patches)
    N = neighbor_patches(C, U)
    Z = subscheme(U, I[U])
    for V in N
      # check whether this node already knows about I
      V in covered_patches(I) && continue

      # if not, extend I to this patch
      f, _ = glueing_morphisms(C[V, U])
      ZV = closure(preimage(f, Z))
      I[V] = [f for f in gens(defining_ideal(ZV)) if !iszero(OO(V)(f))]
      V in dirty_patches || push!(dirty_patches, V)
    end
  end
  # TODO: Extend trivially to disjoint components?
  return I
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
    if ideal(OO(U), I[U]) != ideal(OO(U), J[U])
      return false
    end
  end
  return true
end

# prepares a refinement C' of the covering for the ideal sheaf I 
# such that I can be generated by a regular sequence defining a smooth 
# local complete intersection subscheme in every patch U of C' and 
# returns the ideal sheaf with those generators on C'.
function as_smooth_lci(
    I::IdealSheaf;
    verbose::Bool=false,
    check::Bool=true,
    codimension::Int=dim(scheme(I))-dim(subscheme(I)) #assumes both scheme(I) and its subscheme to be equidimensional
  )
  X = scheme(I)
  C = covering(I)
  SpecType = affine_patch_type(C)
  PolyType = poly_type(SpecType)
  new_gens_dict = Dict{SpecType, Vector{PolyType}}()
  for U in patches(C)
    V, spec_dict = as_smooth_lci(U, I[U], 
                                 verbose=verbose, 
                                 check=check, 
                                 codimension=codimension) 
    add_affine_refinement!(C, V)
    merge!(new_gens_dict, spec_dict)
  end
  Iprep = IdealSheaf(X, C, new_gens_dict)
  set_attribute!(Iprep, :is_regular_sequence, true)
  return Iprep
end

function as_smooth_lci(
    U::Spec, g::Vector{T}; 
    verbose::Bool=false,
    check::Bool=true,
    codimension::Int=dim(U)-dim(subscheme(U, g)) # this assumes both U and its subscheme to be equidimensional
  ) where {T<:MPolyElem}
  verbose && println("preparing $g as a local complete intersection on $U")
  f = numerator.(gens(localized_modulus(OO(U))))
  f = [a for a in f if !iszero(a)]
  verbose && println("found $(length(f)) generators for the ideal defining U")
  h = vcat(f, g)
  r = length(f)
  s = length(g)
  Dh = jacobi_matrix(h)
  (ll, ql, rl, cl) = _non_degeneration_cover(subscheme(U, g), Dh, codimension + codim(U), 
                          verbose=verbose, check=check, 
                          restricted_columns=[collect(1:r), [r + k for k in 1:s]])

  n = length(ll)
  # first process the necessary refinements of U
  # The restricted columns in the call to _non_degenerate_cover 
  # assure that the first codim(U) entries of every cl[i] are 
  # indices of some element of f. However, we can discard these, 
  # as they are trivial generators of the ideal sheaf on U.
  minor_list = [det(Dh[rl[i], cl[i]]) for i in 1:n]
  V = Vector{open_subset_type(U)}()
  SpecType = typeof(U)
  PolyType = poly_type(U)
  spec_dict = Dict{SpecType, Vector{PolyType}}()
  g = Vector{PolyType}()
  W = SpecOpen(U, minor_list)
  for i in 1:n
    spec_dict[W[i]] = h[cl[i][codim(U)+1:end]]
  end
  return W, spec_dict
end


