@doc raw"""
    blow_up(m::NormalToricVariety, I::ToricIdealSheafFromCoxRingIdeal; coordinate_name::String = "e")

Blow up the toric variety along the center given by a toric ideal sheaf.

# Examples
```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> x1, x2, x3, x4 = gens(cox_ring(P3))
4-element Vector{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}:
 x1
 x2
 x3
 x4

julia> II = ideal_sheaf(P3, ideal([x1*x2]))
Sheaf of ideals
  on normal toric variety
with restrictions
  1: Ideal (x_1_1*x_2_1)
  2: Ideal (x_2_2)
  3: Ideal (x_1_3)
  4: Ideal (x_1_4*x_2_4)

julia> blow_down_morphism = blow_up(P3, II)
Blowup
  of normal toric variety
  in sheaf of ideals with restrictions
    1b: Ideal (x_1_1*x_2_1)
    2b: Ideal (x_2_2)
    3b: Ideal (x_1_3)
    4b: Ideal (x_1_4*x_2_4)
with domain
  scheme over QQ covered with 4 patches
    1a: [x_1_1, x_2_1, x_3_1]   scheme(0)
    2a: [x_1_2, x_2_2, x_3_2]   scheme(0)
    3a: [x_1_3, x_2_3, x_3_3]   scheme(0)
    4a: [x_1_4, x_2_4, x_3_4]   scheme(0)
and exceptional divisor
  effective cartier divisor defined by
    sheaf of ideals with restrictions
      1a: Ideal (x_1_1*x_2_1)
      2a: Ideal (x_2_2)
      3a: Ideal (x_1_3)
      4a: Ideal (x_1_4*x_2_4)
```
"""
function blow_up(m::NormalToricVariety, I::ToricIdealSheafFromCoxRingIdeal; coordinate_name::String = "e")
  defining_ideal = ideal_in_cox_ring(I)
  if all(x -> x in gens(base_ring(defining_ideal)), gens(defining_ideal))
    return blow_up(m, defining_ideal; coordinate_name) # Apply toric method
  else
    return blow_up(I) # Reroute to scheme theory
  end
end


@doc raw"""
    blow_up(v::NormalToricVariety, new_ray::AbstractVector{<:IntegerUnion}; coordinate_name::String = "e")

Blow up the toric variety by subdividing the fan of the variety with the
provided new ray. Note that this ray must be a primitive element in the
lattice Z^d, with d the dimension of the fan. This function returns the
corresponding blowdown morphism.

By default, we pick "e" as the name of the homogeneous coordinate for
the exceptional divisor. As third optional argument one can supply
a custom variable name.

# Examples
```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> blow_down_morphism = blow_up(P3, [0, 1, 1])
Toric blowdown morphism

julia> bP3 = domain(blow_down_morphism)
Normal toric variety

julia> cox_ring(bP3)
Multivariate polynomial ring in 5 variables over QQ graded by
  x1 -> [1 0]
  x2 -> [0 1]
  x3 -> [0 1]
  x4 -> [1 0]
  e -> [1 -1]
```
"""
function blow_up(v::NormalToricVariety, new_ray::AbstractVector{<:IntegerUnion}; coordinate_name::String = "e")
  new_variety = normal_toric_variety(star_subdivision(v, new_ray))
  inx = _get_maximal_cones_containing_vector(polyhedral_fan(v), new_ray)
  old_rays = matrix(ZZ, rays(v))
  cone_generators = matrix(ZZ, [old_rays[i,:] for i in 1:nrows(old_rays) if ray_indices(maximal_cones(v))[inx[1], i]])
  powers = solve_mixed(ZZMatrix, transpose(cone_generators), transpose(matrix(ZZ, [new_ray])), identity_matrix(ZZ, ncols(old_rays)))
  gens_S = gens(cox_ring(v))
  variables = [gens_S[i] for i in 1:nrows(old_rays) if ray_indices(maximal_cones(v))[inx[1], i]]
  list_of_gens = [variables[i]^powers[i] for i in 1:length(powers) if powers[i] != 0]
  center = ideal_sheaf(v, ideal([variables[i]^powers[i] for i in 1:length(powers) if powers[i] != 0]))
  return ToricBlowdownMorphism(v, new_variety, coordinate_name, center, new_ray)
end

@doc raw"""
    blow_up(v::NormalToricVariety, n::Int; coordinate_name::String = "e")

Blow up the toric variety by subdividing the n-th cone in the list
of *all* cones of the fan of `v`. This cone need not be maximal.
This function returns the corresponding blowdown morphism.

By default, we pick "e" as the name of the homogeneous coordinate for
the exceptional divisor. As third optional argument one can supply
a custom variable name.

# Examples
```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> blow_down_morphism = blow_up(P3, 5)
Toric blowdown morphism

julia> bP3 = domain(blow_down_morphism)
Normal toric variety

julia> cox_ring(bP3)
Multivariate polynomial ring in 5 variables over QQ graded by
  x1 -> [1 0]
  x2 -> [0 1]
  x3 -> [0 1]
  x4 -> [1 0]
  e -> [1 -1]
```
"""
function blow_up(v::NormalToricVariety, n::Int; coordinate_name::String = "e")
  gens_S = gens(cox_ring(v))
  center = ideal_sheaf(v, ideal([gens_S[i] for i in 1:number_of_rays(v) if cones(v)[n,i]]))
  new_variety = normal_toric_variety(star_subdivision(v, n))
  rays_of_variety = matrix(ZZ, rays(v))
  new_ray = vec(sum([rays_of_variety[i, :] for i in 1:number_of_rays(v) if cones(v)[n, i]]))
  return ToricBlowdownMorphism(v, new_variety, coordinate_name, center, new_ray)
end


@doc raw"""
    blow_up(v::NormalToricVariety, I::MPolyIdeal; coordinate_name::String = "e")

Blow up the toric variety by subdividing the cone in the list
of *all* cones of the fan of `v` which corresponds to the
provided ideal `I`. Note that this cone need not be maximal.

By default, we pick "e" as the name of the homogeneous coordinate for
the exceptional divisor. As third optional argument one can supply
a custom variable name.

# Examples
```jldoctest
julia> P3 = projective_space(NormalToricVariety, 3)
Normal toric variety

julia> (x1,x2,x3,x4) = gens(cox_ring(P3))
4-element Vector{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}:
 x1
 x2
 x3
 x4

julia> I = ideal([x2,x3])
Ideal generated by
  x2
  x3

julia> bP3 = domain(blow_up(P3, I))
Normal toric variety

julia> cox_ring(bP3)
Multivariate polynomial ring in 5 variables over QQ graded by
  x1 -> [1 0]
  x2 -> [0 1]
  x3 -> [0 1]
  x4 -> [1 0]
  e -> [1 -1]

julia> I2 = ideal([x2 * x3])
Ideal generated by
  x2*x3

julia> b2P3 = blow_up(P3, I2);

julia> codomain(b2P3) == P3
true
```
"""
function blow_up(v::NormalToricVariety, I::MPolyIdeal; coordinate_name::String = "e")
  cox = cox_ring(v)
  indices = [findfirst(y -> y == x, gens(cox)) for x in gens(I)]
  if all(index -> index !== nothing, indices)
    rs = matrix(ZZ, rays(v))
    new_ray = vec(sum(rs[index, :] for index in indices))
    new_ray = new_ray ./ gcd(new_ray)
    new_variety = normal_toric_variety(star_subdivision(v, new_ray))
    return ToricBlowdownMorphism(v, new_variety, coordinate_name, ideal_sheaf(v, I), new_ray)
  else
    return _generic_blow_up(v, I)
  end
end

function _generic_blow_up(v::Any, I::Any)
  error("Not yet supported")
end

function _generic_blow_up(v::NormalToricVariety, I::MPolyIdeal)
  return blow_up(ideal_sheaf(v, I))
end
