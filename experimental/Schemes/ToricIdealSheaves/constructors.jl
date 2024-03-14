###############################################
# 1. Ideal sheaves from toric divisors
###############################################

@doc raw"""
    ideal_sheaf(td::ToricDivisor)

Return the ideal sheaf corresponding to a toric divisor.

# Examples
```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> td = toric_divisor(P3, [0, 1, 0, 0])
Torus-invariant, prime divisor on a normal toric variety

julia> ideal_sheaf(td)
Sheaf of ideals
  on normal, smooth toric variety
with restrictions
  1: ideal(x_2_1)
  2: ideal(x_2_2)
  3: ideal(1)
  4: ideal(x_2_4)
```
"""
@attr AbsIdealSheaf function ideal_sheaf(td::ToricDivisor)
  @assert is_cartier(td) "ideal sheaf can only be generated if the divisor is cartier"
  X = toric_variety(td)
  if is_prime(td)
    S = cox_ring(X)
    x = gens(S)
    j = findfirst(x->x==1, coefficients(td)) # Find out which one of the rays we actually have
    @assert j !== nothing "no ray was found"
    II = IdealSheaf(X, ideal(S, x[j]))
    return II
  end
  coeffs = coefficients(td)::Vector{ZZRingElem}
  prime_divisors = torusinvariant_prime_divisors(X)
  return prod(II^k for (II, k) in zip(ideal_sheaf.(prime_divisors), coeffs))
end



###############################################
# 2. Ideal sheaves from ideals in the Cox ring
###############################################

function IdealSheaf(X::NormalToricVariety, I::MPolyIdeal)
  @req base_ring(I) === cox_ring(X) "ideal must live in the cox ring of the variety"

  # We currently only support this provided that the following conditions are met:
  # 1. All maximal cones are smooth, i.e. the fan is smooth/X is smooth.
  # 2. The dimension of all maximal cones matches the dimension of the fan.
  @req is_pure(X) "Currently, ideal sheaves require that all maximal cones have the dimension of the variety"

  ideal_dict = IdDict{AbsAffineScheme, Ideal}()

  if is_smooth(X)
    # We need to dehomogenize the ideal I in the Cox ring S to the local
    # charts U_sigma, with sigma a cone in the fan of the variety.
    # To this end we use Proposition 5.2.10 from Cox-Little-Schenck, p. 223ff.
    # Abstractly, the chart U_sigma is isomorphic to C^n with n the number
    # of ray generators of sigma, owing to the assumptions 1 an 2 above.
    # Note however that the coordinates of C^n are not one to one to
    # the homogeneous coordinates of the Cox ring. Rather, the coordinates 
    # of the affine pieces correspond to the `hilbert_basis(polarize(sigma))`.

    # TODO: In the long run we should think about making the creation of the 
    # following dictionary lazy. But this requires partial rewriting of the 
    # ideal sheaves as a whole, so we postpone it for the moment.

    IM = maximal_cones(IncidenceMatrix, X)
    for (k, U) in enumerate(affine_charts(X))

      # We first create the morphism \pi_s* from p. 224, l. 3.
      indices = [k for k in row(IM, k)]
      help_ring, x_rho = polynomial_ring(QQ, ["x_$j" for j in indices])
      imgs_phi_star = [j in indices ? x_rho[findfirst(k->k==j, indices)] : one(help_ring) for j in 1:n_rays(X)]
      phi_s_star = hom(cox_ring(X), help_ring, imgs_phi_star)

      # Now we need to create the inverse of alpha*.
      imgs_alpha_star = elem_type(help_ring)[]
      for m in hilbert_basis(weight_cone(U))
        img = one(help_ring)
        for j in 1:length(indices)
          u_rho = matrix(ZZ,rays(X))[indices[j]:(indices[j]),:]
          expo = (u_rho*m)[1]
          img = img * x_rho[j]^expo
        end
        push!(imgs_alpha_star, img)
      end
      alpha_star = hom(OO(U), help_ring, imgs_alpha_star)

      # TODO: There should be better ways to create this map!
      # Presumably, one can invert the matrix with the `expo`s as entries?
      # @larskastner If you can confirm this, let's change this.
      alpha_star_inv = inverse(alpha_star)
      ideal_dict[U] = ideal(OO(U), [alpha_star_inv(phi_s_star(g)) for g in gens(I)])
    end
  else
    for (k, U) in enumerate(affine_charts(X))
      ideal_dict[U] = _dehomogenize_to_chart(X, I, k)
    end
  end

  return IdealSheaf(X, ideal_dict, check=false) # TODO: Set the check to false eventually.
end

@doc raw"""
    ideal_sheaf(X::NormalToricVariety, I::MPolyIdeal)

Create a sheaf of ideals on a toric variety ``X`` from a homogeneous ideal 
`I` in its `cox_ring`.

# Examples
```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> (x1,x2,x3,x4) = gens(cox_ring(P3));

julia> I = ideal([x2,x3])
Ideal generated by
  x2
  x3

julia> IdealSheaf(P3, I);
```
"""
ideal_sheaf(X::NormalToricVariety, I::MPolyIdeal) = IdealSheaf(X, I)



###############################################
# 3. Ideal sheaves from cones in the fan
###############################################

@doc raw"""
    ideal_sheaf(X::NormalToricVariety, tau::Cone)

Construct the sheaf of ideals on `X` which is determined by the 
cone `tau` in the Orbit-cone-correspondence; see Cox-Little-Schenck, 
Theorem 3.2.6.
"""
function ideal_sheaf(X::NormalToricVariety, tau::Cone)
  @assert tau in fan(X) "cone must be in the fan of the variety"
  A = _to_matrix(rays(tau))
  A = matrix(ZZ, rays(tau))
  (r, K) = kernel(A)
  w = _colum_vectors_to_rays(K)
  w = vcat(w, -w)
  # TODO: Can we use a direct command instead of this hack?
  tau_perp = positive_hull(w)
  # Maybe it's a mistake in the book and we really need the dual?
  #tau_perp = polarize(tau)
  ideal_dict = IdDict{AbsAffineScheme, Ideal}()
  # We are using Equation (3.2.7) in CLS to determine the local 
  # form of the ideal.
  for U in affine_charts(X)
    cu = cone(U)
    cu_pol = weight_cone(U)
    inter = intersect(tau_perp, cu_pol)
    @assert is_pointed(inter) "intersection must be a pointed cone"
    hb_inter = hilbert_basis(inter)
    if iszero(length(hb_inter))
      ideal_dict[U] = ideal(OO(U), one(OO(U)))
      #ideal_dict[U] = ideal(OO(U), elem_type(OO(U))[])
      continue
    end
    B = _to_integer_column_matrix(hb_inter)
    hb_cu_pol = hilbert_basis(cu_pol)
    A = _to_integer_column_matrix(hb_cu_pol)
    C = identity_matrix(ZZ, ncols(A))
    # For some reason `solve_mixed` returns the transpose of the actual solution, 
    # so we have to correct this.
    S = transpose(solve_mixed(ZZMatrix, A, B, C))
    x = gens(OO(U))
    g = elem_type(OO(U))[prod(x[i]^S[i, j] for i in 1:length(x); init=one(OO(U))) for j in 1:ncols(S)] # The generators of the ideal on U
    ideal_dict[U] = ideal(OO(U), g)
  end
  #return IdealSheaf(X, ideal_dict, check=true) #TODO: Set to false
  return ideal_dict
end

# TODO: Why don't we have that already? Is this too expensive and 
# we don't want to do it that way?
function Base.in(tau::Cone, Sigma::PolyhedralFan)
  # Check that all the rays of tau are also rays of Sigma
  indices = [findfirst(w->w==v, rays(Sigma)) for v in rays(tau)]
  any(x->x===nothing, indices) && return false
  # Now check that this cone is really in Sigma
  all_cones = cones(Sigma)
  return any(j->all(i -> all_cones[j, i], indices), 1:nrows(all_cones))
end

function _dehomogenize_to_chart(X::NormalToricVariety, I::MPolyIdeal, k::Int)
  S = cox_ring(X)
  r = matrix(ZZ, rays(X))
  max_cones = maximal_cones(X)
  sigma = max_cones[k]
  ray_indices_sigma = ray_indices(maximal_cones(X))[k, :]
  loc_vars = [x for (i, x) in enumerate(gens(S)) if !ray_indices_sigma[i]]
  inv_set = MPolyPowersOfElement(S, loc_vars)
  S_loc, loc_map = localization(S, inv_set)
  I_loc = loc_map(I)
  
  U = affine_charts(X)[k]
  hb_U = hilbert_basis(polarize(sigma)) # corresponds to the variables of OO(U)
  x = gens(S_loc)
  img_gens = [prod(x[l]^Int(dot(hb_U[j], r[l, :])) for l in 1:nrows(r); init=one(S_loc)) for j in 1:length(hb_U)]
  A, pr = quo(S_loc, I_loc)
  y = pr.(img_gens)
  # preimage is not implemented for these maps, but kernel works. So we use that for the moment.
  #beta = hom(OO(U), S_loc, img_gens; check=true)
  help = hom(OO(U), A, y)
  #J = preimage(beta, I_loc)
  kernel(help)
end

