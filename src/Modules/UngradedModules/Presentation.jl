####################

@doc raw"""
    presentation(M::SubquoModule)

Return a free presentation of `M`. 
"""
function presentation(SQ::SubquoModule)
  if is_graded(SQ)
    return _presentation_graded(SQ)
  else
    return _presentation_simple(SQ)
  end

  # Old code left for debugging
  #A+B/B is generated by A and B
  #the relations are A meet B? written wrt to A
  R = base_ring(SQ)
  if is_graded(SQ)
    h_F_SQ = graded_map(SQ, gens(SQ))
    F = domain(h_F_SQ)
  else
    F = FreeMod(R, ngens(SQ.sub))
    h_F_SQ = hom(F, SQ, gens(SQ)) # DO NOT CHANGE THIS LINE, see present_as_cokernel and preimage
  end
  br_name = AbstractAlgebra.find_name(R)
  if br_name === nothing
    br_name = "br"
  end
  set_attribute!(F,  :name => "$br_name^$(ngens(SQ.sub))")
  q = elem_type(F)[]
  if is_generated_by_standard_unit_vectors(SQ.sub)
    if isdefined(SQ, :quo)
      q = [FreeModElem(coordinates(g), F) for g in gens(SQ.quo)]
    end
  else
    if is_graded(SQ)
      s, _ = kernel(graded_map(ambient_free_module(SQ), gens(SQ.sum)))
    else
      s, _ = kernel(hom(FreeMod(R,ngens(SQ.sum)), ambient_free_module(SQ), gens(SQ.sum)))
    end
    #s = syzygy_module(SQ.sum.gens)
    #TODO: wait for Hans to release Modulo(A, B) that does exactly this
    c = collect(s.sub.gens)
    #q = elem_type(F)[]

    for x = c
      b = sparse_row(R)
      #e = zero(SQ.F)
      for (i,v) = x.coords
        if i>ngens(SQ)
          break
        end
        #e += v*repres(gen(SQ, i))
        push!(b.pos, i)
        push!(b.values, v)
      end
      if length(b) == 0
        continue
      end
      push!(q, FreeModElem(b, F))
    end
  end
  for i in 1:length(q)
    if !is_homogeneous(q[i])
      for m in terms(q[i])
      end
    end
  end
  #want R^a -> R^b -> SQ -> 0
  #from Hans:
  # as a complex R^b has index 0
  #              R^a           1
  # so 0 has index -2, hence seed has to be -2
  #TODO sort decoration and fix maps, same decoration should be bundled (to match pretty printing)
  if is_graded(SQ)
    h_G_F = graded_map(F, q)
    G = domain(h_G_F)
  else
    G = FreeMod(R, length(q))
    h_G_F = hom(G, F, q)
  end
  br_name = AbstractAlgebra.find_name(F.R)
  if br_name === nothing
    br_name = "br"
  end
  set_attribute!(G, :name => "$br_name^$(length(q))")
  if is_graded(SQ)
    Z = graded_free_module(F.R, 0)
  else
    Z = FreeMod(F.R, 0)
  end
  set_attribute!(Z, :name => "0")
  h_SQ_Z = hom(SQ, Z, Vector{elem_type(Z)}([zero(Z) for i=1:ngens(SQ)]))
  M = Hecke.ComplexOfMorphisms(ModuleFP, ModuleFPHom[h_G_F, h_F_SQ, h_SQ_Z], check = false, seed = -2)
  set_attribute!(M, :show => Hecke.pres_show)
  return M
end

function _presentation_graded(SQ::SubquoModule)
  R = base_ring(SQ)

  # Prepare to set some names
  br_name = AbstractAlgebra.find_name(R)
  if br_name === nothing
    br_name = "br"
  end

  # Create the free module for the presentation
  #
  # We have to take representatives of the simplified 
  # generators, because otherwise the degrees are not correctly
  # inferred. 
  #
  # At the same time, we can not just throw away zero 
  # generators, because other code relies on the 1:1-correspondence
  # of the generators in a presentation.
  F0_to_SQ = graded_map(SQ, gens(SQ))
  F0 = domain(F0_to_SQ)
  set_attribute!(F0,  :name => "$br_name^$(ngens(SQ.sub))")

  K, inc_K = kernel(F0_to_SQ)
  #F1_to_F0 = graded_map(F0, images_of_generators(inc_K))
  #F1 = domain(F1_to_F0)
  F1 = graded_free_module(R, degree.(images_of_generators(inc_K)))
  F1_to_F0 = hom(F1, F0, images_of_generators(inc_K), check=false)
  set_attribute!(F1, :name => "$br_name^$(ngens(F1))")

  # When there is no kernel, clean things up
  if is_zero(F1)
    F1 = graded_free_module(R, elem_type(grading_group(R))[])
    F1_to_F0 = hom(F1, F0, elem_type(F0)[]; check=false)
  end

  # prepare the end of the presentation
  Z = graded_free_module(R, elem_type(grading_group(R))[])
  SQ_to_Z = hom(SQ, Z, elem_type(Z)[zero(Z) for i in 1:ngens(SQ)]; check=false)

  # compile the presentation complex
  M = Hecke.ComplexOfMorphisms(ModuleFP, ModuleFPHom[F1_to_F0, F0_to_SQ, SQ_to_Z], check = true, seed = -2)
  @assert M[0] === F0::FreeMod
  @assert M[1] === F1::FreeMod
  set_attribute!(M, :show => Hecke.pres_show)
  return M
end

function _presentation_simple(SQ::SubquoModule)
  R = base_ring(SQ)

  # Prepare to set some names
  br_name = AbstractAlgebra.find_name(R)
  if br_name === nothing
    br_name = "br"
  end

  # Create the free module for the presentation
  F0 = FreeMod(R, length(gens(SQ)))
  F0_to_SQ = hom(F0, SQ, gens(SQ); check=false)
  set_attribute!(F0,  :name => "$br_name^$(ngens(SQ.sub))")

  K, inc_K = kernel(F0_to_SQ)
  @assert codomain(inc_K) === F0
  @assert all(x->parent(x) === F0, images_of_generators(inc_K))
  F1 = FreeMod(R, ngens(K))
  F1_to_F0 = hom(F1, F0, images_of_generators(inc_K), check=false)
  set_attribute!(F1, :name => "$br_name^$(ngens(F1))")

  # When there is no kernel, clean things up
  if is_zero(F1)
    F1 = FreeMod(R, 0)
    F1_to_F0 = hom(F1, F0, elem_type(F0)[]; check=false)
  end

  # prepare the end of the presentation
  Z = FreeMod(R, 0)
  SQ_to_Z = hom(SQ, Z, elem_type(Z)[zero(Z) for i in 1:ngens(SQ)]; check=false)

  # compile the presentation complex
  M = Hecke.ComplexOfMorphisms(ModuleFP, ModuleFPHom[F1_to_F0, F0_to_SQ, SQ_to_Z], check = true, seed = -2)
  set_attribute!(M, :show => Hecke.pres_show)
  return M
end

@doc raw"""
    presentation(F::FreeMod)

Return a free presentation of `F`.
"""
function presentation(F::FreeMod)
  if is_graded(F)
    Z = graded_free_module(F.R, 0)
  else
    Z = FreeMod(F.R, 0)
  end
  set_attribute!(Z, :name => "0")
  M = Hecke.ComplexOfMorphisms(ModuleFP, ModuleFPHom[hom(Z, F, Vector{elem_type(F)}()), hom(F, F, gens(F)), hom(F, Z, Vector{elem_type(Z)}([zero(Z) for i=1:ngens(F)]))], check = false, seed = -2)
  set_attribute!(M, :show => Hecke.pres_show)
  return M
end

@doc raw"""
    presentation(M::ModuleFP)

Return a free presentation of `M`.

# Examples
```jldoctest
julia> R, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"]);

julia> A = R[x; y];

julia> B = R[x^2; y^3; z^4];

julia> M = SubquoModule(A, B);

julia> P = presentation(M)
0 <---- M <---- R^2 <---- R^5
```

```jldoctest
julia> Rg, (x, y, z) = graded_polynomial_ring(QQ, ["x", "y", "z"]);

julia> F = graded_free_module(Rg, [1,2,2]);

julia> p = presentation(F)
0 <---- F <---- F <---- 0

julia> p[-2]
Graded free module Rg^0 of rank 0 over Rg

julia> p[-1]
Graded free module Rg^1([-1]) + Rg^2([-2]) of rank 3 over Rg

julia> p[0]
Graded free module Rg^1([-1]) + Rg^2([-2]) of rank 3 over Rg

julia> p[1]
Graded free module Rg^0 of rank 0 over Rg

julia> map(p,-1)
F -> 0
e[1] -> 0
e[2] -> 0
e[3] -> 0
Homogeneous module homomorphism

julia> map(p,0)
F -> F
e[1] -> e[1]
e[2] -> e[2]
e[3] -> e[3]
Homogeneous module homomorphism

julia> map(p,1)
0 -> F
Homogeneous module homomorphism

julia> F = graded_free_module(Rg, 1);

julia> A = Rg[x; y];

julia> B = Rg[x^2; y^3; z^4];

julia> M = SubquoModule(F, A, B);

julia> P = presentation(M)
0 <---- M <---- Rg^2 <---- Rg^5

julia> P[-2]
Graded free module Rg^0 of rank 0 over Rg

julia> P[-1]
Graded subquotient of submodule of F generated by
1 -> x*e[1]
2 -> y*e[1]
by submodule of F generated by
1 -> x^2*e[1]
2 -> y^3*e[1]
3 -> z^4*e[1]

julia> P[0]
Graded free module Rg^2([-1]) of rank 2 over Rg

julia> P[1]
Graded free module Rg^2([-2]) + Rg^1([-3]) + Rg^2([-5]) of rank 5 over Rg

julia> map(P,-1)
M -> 0
x*e[1] -> 0
y*e[1] -> 0
Homogeneous module homomorphism

julia> map(P,0)
Rg^2 -> M
e[1] -> x*e[1]
e[2] -> y*e[1]
Homogeneous module homomorphism

julia> map(P,1)
Rg^5 -> Rg^2
e[1] -> x*e[1]
e[2] -> -y*e[1] + x*e[2]
e[3] -> y^2*e[2]
e[4] -> z^4*e[1]
e[5] -> z^4*e[2]
Homogeneous module homomorphism
```
"""
function presentation(M::ModuleFP)
 error("presentation is not implemented for the given types.")
end

@doc raw"""
    present_as_cokernel(M::SubquoModule, task::Symbol = :none)

Return a subquotient `C` which is isomorphic to `M`, and whose generators are the standard unit vectors of its ambient free module.

Additionally,

- return an isomorphism `M` $\to$ `C` if `task = :with_morphism`,
- return and cache an isomorphism `M` $\to$ `C` if `task = :cache_morphism`,
- do none of the above if `task = :none` (default).

If `task = :only_morphism`, return only an isomorphism.

# Examples
```jldoctest
julia> R, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"]);

julia> A = R[x; y];

julia> B = R[x^2; y^3; z^4];

julia> M = SubquoModule(A, B)
Subquotient of Submodule with 2 generators
1 -> x*e[1]
2 -> y*e[1]
by Submodule with 3 generators
1 -> x^2*e[1]
2 -> y^3*e[1]
3 -> z^4*e[1]

julia> C = present_as_cokernel(M)
Subquotient of Submodule with 2 generators
1 -> e[1]
2 -> e[2]
by Submodule with 5 generators
1 -> x*e[1]
2 -> -y*e[1] + x*e[2]
3 -> y^2*e[2]
4 -> z^4*e[1]
5 -> z^4*e[2]
```

```jldoctest
julia> Rg, (x, y, z) = graded_polynomial_ring(QQ, ["x", "y", "z"]);

julia> F = graded_free_module(Rg, 1);

julia> A = Rg[x; y];

julia> B = Rg[x^2; y^3; z^4];

julia> M = SubquoModule(F, A, B);

julia> present_as_cokernel(M, :with_morphism)
(Graded subquotient of submodule of Rg^2 generated by
1 -> e[1]
2 -> e[2]
by submodule of Rg^2 generated by
1 -> x*e[1]
2 -> -y*e[1] + x*e[2]
3 -> y^2*e[2]
4 -> z^4*e[1]
5 -> z^4*e[2], Graded subquotient of submodule of Rg^2 generated by
1 -> e[1]
2 -> e[2]
by submodule of Rg^2 generated by
1 -> x*e[1]
2 -> -y*e[1] + x*e[2]
3 -> y^2*e[2]
4 -> z^4*e[1]
5 -> z^4*e[2] -> M
e[1] -> x*e[1]
e[2] -> y*e[1]
Homogeneous module homomorphism)
```
"""
function present_as_cokernel(SQ::SubquoModule, task::Symbol = :none)
  chainComplex = presentation(SQ)
  R_b = obj(chainComplex, 0)
  f = map(chainComplex, 1)
  g = map(chainComplex, 0)
  presentation_module = quo_object(R_b, image(f)[1])

  if task == :none
    return presentation_module
  end
  
  # The isomorphism is just the identity matrix
  isomorphism = hom(presentation_module, SQ, Vector{elem_type(SQ)}([g(x) for x in gens(R_b)]))
  inverse_isomorphism = hom(SQ, presentation_module, Vector{elem_type(presentation_module)}([presentation_module[i] for i=1:ngens(SQ)]))
  isomorphism.inverse_isomorphism = inverse_isomorphism

  if task == :cache_morphism
    register_morphism!(isomorphism)
    register_morphism!(inverse_isomorphism)
  end
  task == :only_morphism && return isomorphism
  
  return presentation_module, isomorphism
end

@doc raw"""
    present_as_cokernel(F::FreeMod, task::Symbol = :none)

Represent `F` as the quotient `C` of itself with no relations. This method exists for compatibility reasons with `present_as_cokernel(M::SubQuoModule, task::Symbol = :none)`. 

Additionally,

- return an isomorphism `F` $\to$ `C` if `task = :with_morphism`,
- return and cache an isomorphism `F` $\to$ `C` if `task = :cache_morphism`,
- do none of the above if `task = :none` (default).

If `task = :only_morphism`, return only an isomorphism.

# Examples
```jldoctest
julia> R, (x, y, z) = polynomial_ring(QQ, ["x", "y", "z"]);

julia> F = free_module(R, 2)
Free module of rank 2 over Multivariate polynomial ring in 3 variables over QQ

julia> present_as_cokernel(F)
Submodule with 2 generators
1 -> e[1]
2 -> e[2]
represented as subquotient with no relations.

julia> present_as_cokernel(F, :only_morphism)
Map with following data
Domain:
=======
Free module of rank 2 over Multivariate polynomial ring in 3 variables over QQ
Codomain:
=========
Submodule with 2 generators
1 -> e[1]
2 -> e[2]
represented as subquotient with no relations.
```
"""
function present_as_cokernel(F::FreeMod, task::Symbol = :none)
  presentation_module, isomorphism = quo(F, [zero(F)])
  inverse_isomorphism = hom(presentation_module, F, gens(F))

  if task == :none
    return presentation_module
  end

  if task == :cache_morphism
    register_morphism!(isomorphism)
    register_morphism!(inverse_isomorphism)
  end
  task == :only_morphism && return isomorphism
  
  return presentation_module, isomorphism
end

@doc raw"""
    prune_with_map(M::ModuleFP)

Returns another module `N` and an isomorphism from `N` to `M` such
that `N` is generated by a minimal number of elements.

# Examples
```jldoctest
julia> R, (x, y) = polynomial_ring(QQ, ["x", "y"]);

julia> M = SubquoModule(identity_matrix(R, 2), R[1 x+y])
Subquotient of Submodule with 2 generators
1 -> e[1]
2 -> e[2]
by Submodule with 1 generator
1 -> e[1] + (x + y)*e[2]

julia> N, phi = prune_with_map(M)
(Submodule with 1 generator
1 -> e[1]
represented as subquotient with no relations., Map with following data
Domain:
=======
Submodule with 1 generator
1 -> e[1]
represented as subquotient with no relations.
Codomain:
=========
Subquotient of Submodule with 2 generators
1 -> e[1]
2 -> e[2]
by Submodule with 1 generator
1 -> e[1] + (x + y)*e[2])

julia> phi(first(gens(N)))
e[2]
```
"""
function prune_with_map(M::ModuleFP)
  # TODO: take special care of graded modules 
  # by stripping off the grading and rewrapping it afterwards.
  N, a, b = _alt_simplify(M)
  return N, b
end

function prune_with_map(M::ModuleFP{T}) where {T<:MPolyRingElem{<:FieldElem}} # The case that can be handled by Singular

  # Singular presentation
  pm = presentation(M)
  pres_map = map(pm, 1)
  krnel = SubquoModule(pm[0], pres_map.(gens(pm[1]))) # Create the image of pres_map without the inclusion map
  s_fmod  = Oscar.singular_module(ambient_free_module(krnel))
  s_mod = Singular.Module(base_ring(s_fmod),
                          [s_fmod(repres(g)) for g in gens(krnel)]...)

  # compute minimal presentation
  s_mod_new, mat, p = Singular.prune_with_map_projection(s_mod)
  new_rk = Singular.rank(s_mod_new)

  # find which generators were scratched
  img_inds = [findlast(j -> j == i, p) for i in 1:new_rk]
  @assert all(i -> !isnothing(i), img_inds) "something went wrong when trying to construct the map"
  phi2 = map(pm, 0)
  F2 = domain(phi2)

  # convert s_mod_new to Oscar
  R = base_ring(M)
  if is_graded(M)
    F = graded_free_module(R, degrees_of_generators(F2)[img_inds])
  else
    F = free_module(base_ring(M), new_rk)
  end
  new_krnel_gens = (F).([s_mod_new[i] for i in 1:ngens(s_mod_new)])
  M_new, _ = quo(F, new_krnel_gens)

  # build map
  phi3 = hom(M_new, F2, gens(F2)[img_inds]) 
  phi = compose(phi3, phi2)
  
  return M_new, phi
end

function prune_with_map(F::FreeMod)
  return F, hom(F, F, gens(F))
end
