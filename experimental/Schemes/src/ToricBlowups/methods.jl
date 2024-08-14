@doc raw"""
    total_transform(f::AbsSimpleBlowdownMorphism, II::IdealSheaf)

Computes the total transform of an ideal sheaf along a blowdown morphism.

In particular, this applies in the toric setting. However, note that
currently (October 2023), ideal sheaves are only supported on smooth
toric varieties.

# Examples
```jldoctest
julia> P2 = projective_space(NormalToricVariety, 2)
Normal toric variety

julia> bl = blow_up(P2, [1, 1])
Toric blowdown morphism

julia> S = cox_ring(P2);

julia> x, y, z = gens(S);

julia> I = ideal_sheaf(P2, ideal([x*y]))
Sheaf of ideals
  on normal, smooth toric variety
with restrictions
  1: Ideal (x_1_1*x_2_1)
  2: Ideal (x_2_2)
  3: Ideal (x_1_3)

julia> total_transform(bl, I)
Sheaf of ideals
  on normal toric variety
with restrictions
  1: Ideal (x_1_1*x_2_1^2)
  2: Ideal (x_1_2^2*x_2_2)
  3: Ideal (x_2_3)
  4: Ideal (x_1_4)
```
"""
function total_transform(f::AbsSimpleBlowdownMorphism, II::AbsIdealSheaf)
  return pullback(f, II)
end

function total_transform(f::AbsBlowdownMorphism, II::AbsIdealSheaf)
  return pullback(f, II)
end


########################################################################
# Further functionality
########################################################################

# Construct a graded module over the Cox ring whose sheafification 
# is isomorphic to the reflexive hull of the kaehler differentials.
function _reflexive_differential_module(
    X::NormalToricVariety; check::Bool=true
  )
  psi = _reflexive_differential_map(X)
  W1, inc_W1 = kernel(psi)
  return W1
end

function _reflexive_differential_map(X::NormalToricVariety; check::Bool=true)
  S = cox_ring(X)
  G = grading_group(S)
  @assert G === class_group(X)
  # We follow [CLS] Theorem 8.1.6.
  @check is_simplicial(X) "toric variety must be simplicial"
  @check !has_torusfactor(X) "toric variety must not have torus factors"

  # Build the morphism from the short exact sequence describing Ω¹

  r = ngens(G)
  F = graded_free_module(S, degree.(gens(S)))
  FF = graded_free_module(S, [zero(G) for i in 1:r])
  img_gens = elem_type(FF)[]
  for (i, v) in enumerate(gens(F))
    d = degree(v)
    img = zero(FF)
    for j in 1:r
      img += d[j]*S[i]*FF[j]
    end
    push!(img_gens, img)
  end
  psi = hom(F, FF, img_gens)
  return psi
end

# For a homogeneous ideal I ⊂ S in the Cox ring of X compute a graded S-module
# M whose sheafification is the sheaf of Kaehler differential forms on the 
# subvariety Y = V(I) ⊂ X on the smooth locus of X.
function _reflexive_differential_module(
    X::NormalToricVariety, I::MPolyIdeal; 
    check::Bool=true
  )
  S = cox_ring(X)
  @assert S === base_ring(I)

  W1_X = _reflexive_differential_module(X)
  F = ambient_free_module(W1_X)

  # Compute the natural map from the short exact sequence 
  #
  #   0 → I/I² → i_* i^* W¹ → Ω¹_Y → 0
  #
  # for i : Y = V(I) ↪ X.
  #
  # For the module in the middle we use that the defining 
  # sequence for W¹
  #                       ψ
  #   0 → W¹ → ⊕ ᵨ S[-Dᵨ] → Cl(X) ⊗ S 
  #
  # splits on the right so that ker (ψ ⊗ S/I) indeed represents 
  # the sheaf i_* i^* W¹.
  # 

  G = grading_group(S)
  S1 = graded_free_module(S, [zero(G)])
  II, inc_II = I*S1
  M = cokernel(inc_II)
  pf_pb_W1_X = tensor_product(W1_X, M)

  psi = _reflexive_differential_map(X)
  psi_res = tensor_product(psi, M)

  K, inc_K = kernel(psi_res)

  F = domain(psi_res)
  theta = hom(II, domain(psi_res), 
              [sum(derivative(f, i)*F[i] for i in 1:ngens(F); init=zero(F)) for f in gens(I)])
  theta_lift = hom(II, K, [preimage(inc_K, g) for g in images_of_generators(theta)])
  return cokernel(theta_lift)
end

function tensor_product(
    f::ModuleFPHom{<:ModuleFP, <:ModuleFP, Nothing}, 
    M::ModuleFP;
    domain::ModuleFP = tensor_product(domain(f), M),
    codomain::ModuleFP = tensor_product(codomain(f), M)
  )
  R = base_ring(M)
  @assert R === base_ring(Oscar.domain(f))
  return tensor_product(f, identity_map(M))
end

