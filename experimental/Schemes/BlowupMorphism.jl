export BlowupMorphism
export center, projection, exceptional_divisor

mutable struct BlowupMorphism{
                              CodomainType<:AbsCoveredScheme
                             }
  projective_bundle::CoveredProjectiveScheme 
  codomain::CodomainType   # i.A. ein CoveredScheme
  center::IdealSheaf      # on codomain
  projection::AbsCoveredSchemeMorphism
  domain::AbsCoveredScheme # i.A. ein CoveredScheme
  exceptional_divisor::EffectiveCartierDivisor

  function BlowupMorphism(
      IP::CoveredProjectiveScheme,
      I::IdealSheaf
    )
    X = base_scheme(IP)
    X === scheme(I) || error("ideal sheaf not compatible with blown up variety")
    return new{typeof(X)}(IP, X, I)
  end
end

function domain(p::BlowupMorphism)
  if !isdefined(p, :domain)
    p.domain = covered_scheme(p.projective_bundle)
  end
  return p.domain
end

codomain(p::BlowupMorphism) = p.codomain
center(p::BlowupMorphism) = p.center

function projection(p::BlowupMorphism)
  if !isdefined(p, :projection)
    p.projection = covered_projection_to_base(p.projective_bundle)
  end
  return p.projection
end

# TODO: Find better name!
covered_projective_scheme(p::BlowupMorphism) = p.projective_bundle

@Markdown.doc """
    exceptional_divisor(p::BlowupMorphism)

For a `BlowupMorphism` ``p : Y → X`` coming from the blowup of an 
`IdealSheaf` ``ℐ`` on X, return the `EffectiveCartierDivisor` ``E`` 
on ``Y`` associated to the (relative) tautological bundle ``𝒪(1)``. 

On a pair of charts ``V → U`` of the `covered_scheme` of the 
`projection` of ``p`` this returns the pullback of the `i`-th 
generator of ``ℐ(U)`` when ``V`` is the `i-1`-st canonical chart 
of the local blowup over ``U``.
"""
function exceptional_divisor(p::BlowupMorphism)
  if !isdefined(p, :exceptional_divisor)
    error("exceptional divisor needs to be cached during construction")
    Y = domain(p)
    pr = projection(p)
    pr_cov = covering_morphism(pr)
    IC = center(p)
    ideals_on_patches = IdDict{AbsSpec, Ideal}()
    mult_flag = false # To compute the multiplicity only once 
    multiplicity = one(ZZ)
    for U in domain(pr_cov)
      pr_U = pr_cov[U]
      V = codomain(pr_U)
      J = ideal(OO(U), pullback(pr_U).(gens(IC(V))))
      J_rad = radical(J)
      # TODO: Pick the "simplest" chart for the following computation.
      # We could also first use elimpart for simplification.
      if !mult_flag && !(J == J_rad)
        R = base_ring(OO(U))
        S = MPolyComplementOfPrimeIdeal(saturated_ideal(J_rad))
        R_loc, loc_map = localization(R, S)
        F = FreeMod(R_loc, 1)
        JF, _ = sub(F, [g*F[1] for g in gens(saturated_ideal(J))])
        M, _ = quo(F, JF)
        multiplicity = length(M)
        mult_flag = true
      end
      ideals_on_patches[U] = J_rad
    end
    IE = IdealSheaf(Y, ideals_on_patches)
    p.exceptional_divisor = WeilDivisor(Y, ZZ, IdDict{IdealSheaf, elem_type(ZZ)}(IE => multiplicity))
  end
  return p.exceptional_divisor
end

### Auxiliary function which were not there; to be moved

@attr function radical(I::MPolyQuoLocalizedIdeal)
  L = base_ring(I)
  J = pre_image_ideal(I)
  J_rad = radical(J)
  return ideal(L, [g for g in L.(gens(J_rad)) if !iszero(g)])
end

@attr function radical(I::MPolyLocalizedIdeal)
  L = base_ring(I)
  J = pre_saturated_ideal(I)
  J_rad = radical(J)
  return ideal(L, [g for g in L.(gens(J_rad))])
end

@attr function dim(I::MPolyQuoLocalizedIdeal)
  return dim(pre_image_ideal(I))
end

@attr function dim(I::MPolyLocalizedIdeal)
  return dim(saturated_ideal(I))
end

@Markdown.doc """
    strict_transform(p::BlowupMorphism, inc::CoveredClosedEmbedding)

For a `BlowupMorphism` ``p : Y → X`` and a `CoveredClosedEmbedding` 
``ι : Z ↪ X``, compute the strict transform ``Z'`` of ``Z`` along ``p`` and 
return a triple ``(Z', j, π)`` containing the `CoveredClosedEmbedding` 
``j : Z' ↪ Y`` and the induced projection ``π : Z' → Z``.

!!! note The projection is not yet implemented! Instead, `nothing` is returned 
as the third item.
"""
function strict_transform(p::BlowupMorphism, inc::CoveredClosedEmbedding)
  Y = domain(p)
  X = codomain(p)
  Z = domain(inc)
  codomain(inc) === X || error("maps must have the same codomain")
  ID = IdDict{AbsSpec, Ideal}()
  pr = projection(p)
  p_cov = covering_morphism(pr)
  CY = domain(p_cov)
  # We first apply elim_part to all the charts.
  CY_simp, phi, psi = simplify(CY)
  # register the simplification in Y
  push!(coverings(Y), CY_simp)
  refinements(Y)[(CY_simp, CY)] = phi
  refinements(Y)[(CY, CY_simp)] = psi
  CY === default_covering(Y) && set_attribute!(Y, :simplified_covering, CY_simp)

  # compose the covering morphisms
  p_cov_simp = compose(phi, p_cov)
  CX = codomain(p_cov)
  E = exceptional_divisor(p)
  for U in patches(CY_simp)
    p_res = p_cov_simp[U]
    V = codomain(p_res)
    J = image_ideal(inc)(V)
    g = maps_with_given_codomain(inc, V)
    pbJ = ideal(OO(U), pullback(p_res).(gens(J)))
    pbJ_sat = saturated_ideal(pbJ)
    pbJ_sat = saturation(pbJ_sat, ideal(base_ring(pbJ_sat), lifted_numerator.(E(U))))
    pbJ = ideal(OO(U), [g for g in OO(U).(gens(pbJ_sat)) if !iszero(g)])
    ID[U] = pbJ
  end

  I_trans = IdealSheaf(Y, ID, check=false) # TODO: Set to false
  inc_Z_trans = CoveredClosedEmbedding(Y, I_trans, covering=CY_simp, check=false)
  inc_cov = covering_morphism(inc_Z_trans)

  Z_trans = domain(inc_Z_trans)
  pr_res = restrict(projection(p), inc_Z_trans, inc)
  return Z_trans, inc_Z_trans, pr_res
end

#=
#  Z' ↪ Y
#       ↓ f
#  Z ↪  X
#
#  Assuming f(Z') ⊂ Z, we compute and return the restriction f : Z' → Z.
=#
function restrict(f::AbsCoveredSchemeMorphism,
    inc_dom::CoveredClosedEmbedding,
    inc_cod::CoveredClosedEmbedding;
    check::Bool=true
  )
  f_cov = covering_morphism(f)
  inc_dom_cov = covering_morphism(inc_dom)
  inc_cod_cov = covering_morphism(inc_cod)

  # We need to do the following.
  # - Pass to a common refinement ref_cod in X that both 
  #   f and inc_cod can restrict to.
  # - Pass to a common refinement in Y
  ref_cod, a, b = _register!(common_refinement(codomain(f_cov), codomain(inc_cod_cov)), codomain(f))
  inc_cod_ref = restrict(inc_cod, ref_cod)
  f_res = restrict(f, ref_cod)
  ref_dom, aa, bb = _register!(common_refinement(domain(f_res), codomain(inc_dom_cov)), domain(f))
  inc_dom_ref = restrict(inc_dom, ref_dom)
  inc_dom_ref = compose(inc_dom_ref, aa)
  # Collecting the maps for the restricted projection here
  map_dict = IdDict{AbsSpec, AbsSpecMor}()
  for U in patches(domain(inc_dom_ref))
    q_res = compose(inc_dom_ref[U], f_res[codomain(inc_dom_ref[U])])
    V = codomain(q_res)
    g = maps_with_given_codomain(inc_cod_ref, V)
    if !isone(length(g))
      error()
    end
    pre_V = domain(first(g))
    map_dict[U] = restrict(q_res, domain(q_res), pre_V, check=false)
  end
  psi = CoveringMorphism(domain(inc_dom_ref), domain(inc_cod_ref), map_dict, check=false)
  return CoveredSchemeMorphism(domain(inc_dom), domain(inc_cod), psi)
end

function _register!(data::Tuple{<:Covering, <:CoveringMorphism, <:CoveringMorphism},
    X::AbsCoveredScheme
  )
  push!(coverings(X), data[1])
  refinements(X)[(domain(data[2]), codomain(data[2]))] = data[2]
  refinements(X)[(domain(data[3]), codomain(data[3]))] = data[3]
  return data
end

function maps_with_given_codomain(phi::CoveringMorphism, V::AbsSpec)
  result = Vector{AbsSpecMor}()
  for U in keys(morphisms(phi))
    floc = morphisms(phi)[U]
    codomain(floc) === V || continue
    push!(result, floc)
  end
  return result
end

#function saturation(I::MPolyLocalizedIdeal, J::MPolyLocalizedIdeal)
#  L = base_ring(I) 
#  L === base_ring(J) || error("ideals must be defined over the same ring")
#  II = pre_saturated_ideal(I)
#  JJ = pre_saturated_ideal(J)
#  KK = saturation(II, JJ)
#  return ideal(R, [g for g in R.(gens(KK)) if !iszero(g)])
#end
#
#function saturation(I::MPolyQuoLocalizedIdeal, J::MPolyQuoLocalizedIdeal)
#  L = base_ring(I) 
#  L === base_ring(J) || error("ideals must be defined over the same ring")
#  II = pre_image_ideal(I)
#  JJ = pre_image_ideal(J)
#  KK = saturation(II, JJ)
#  return ideal(R, [g for g in R.(gens(KK)) if !iszero(g)])
#end
#
#function saturation(I::MPolyQuoIdeal, J::MPolyQuoIdeal)
#  L = base_ring(I) 
#  L === base_ring(J) || error("ideals must be defined over the same ring")
#  II = saturated_ideal(I)
#  JJ = saturated_ideal(J)
#  KK = saturation(II, JJ)
#  return ideal(R, [g for g in R.(gens(KK)) if !iszero(g)])
#end

