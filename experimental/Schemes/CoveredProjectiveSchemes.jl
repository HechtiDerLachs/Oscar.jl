export ProjectiveGlueing

export CoveredProjectiveScheme

export blow_up, empty_covered_projective_scheme

mutable struct ProjectiveGlueing{
                                 GlueingType<:Glueing,
                                 ProjectiveSchemeType<:ProjectiveScheme,
                                 MorphismType<:ProjectiveSchemeMor
                                }
  G::GlueingType # the underlying glueing of the base schemes
  P::ProjectiveSchemeType # the projective scheme over the first patch
  Q::ProjectiveSchemeType # the projective scheme over the second patch
  P_on_U_patches::Vector{MorphismType} # restrictions of these 
  Q_on_V_patches::Vector{MorphismType} # schemes to the patches
  f::Vector{MorphismType} # the glueing maps on the affine
  g::Vector{MorphismType} # patches of the glueing domain 

  ### 
  # Given two relative projective schemes and a glueing 
  #
  #       P           Q
  #     π ↓           ↓ π
  #   G : X ↩ U ≅ V ↪ Y 
  #           ∪   ∪
  #           Uᵢ  Vⱼ
  #
  # together with compatible glueing data 
  #
  #   fᵢ: π⁻¹(Uᵢ) → Q,   gⱼ: π⁻¹(Vⱼ) → P
  #
  # on the affine patches Uᵢ of U (resp. Vⱼ of V), 
  # glue together the projective schemes P and Q
  function ProjectiveGlueing(G::GlueingType, P::T, Q::T, f::Vector{M}, g::Vector{M}; check::Bool=true) where {GlueingType<:Glueing, T<:ProjectiveScheme, M<:ProjectiveSchemeMor}
    (X, Y) = patches(G)
    (U, V) = glueing_domains(G)
    (base_scheme(P) == X && base_scheme(Q) == Y) || error("base glueing is incompatible with the projective schemes")
    P_on_U_patches = Vector{MorphismType}()
    Q_on_V_patches = Vector{MorphismType}()
    
    length(f) == npatches(U) || error("base glueing is incompatible with the projective schemes")
    # for every patch Uᵢ of U we need to set up and store 
    # the inclusion map of π⁻¹(Uᵢ) ↪ P = π⁻¹(X)
    for i in 1:length(f)
      h = f[i]
      base_scheme(domain(h)) == U[i] || error("base glueing is incompatible with morphisms of projective schemes")
      push!(P_on_U_patches, inclusion_map(domain(h), P))
    end
    
    length(g) == npatches(V) || error("base glueing is incompatible with the projective schemes")
    # the same for V
    for j in 1:length(g)
      h = g[j]
      base_scheme(domain(h)) == V[j] || error("base glueing is incompatible with morphisms of projective schemes")
      push!(Q_on_V_patches, inclusion_map(domain(h), Q))
    end

    # in case a check is required, we assure that the maps on the 
    # patches Uᵢ glue together on the overlaps.
    if check
      for i in 1:length(f)-1
        for j = i+1:length(f)
          W = intersect(U[i], U[j])
          PW = fiber_product(W, P)
          h1 = inclusion_map(PW, domain(P_on_U_patches[i]))
          h2 = inclusion_map(PW, domain(P_on_U_patches[j]))
          compose(h1, P_on_U_patches[i]) == compose(h2, P_on_U_patches[j]) || error("maps do not coincide on overlaps")
        end
      end
      # same for V
      for i in 1:length(g)-1
        for j = i+1:length(g)
          W = intersect(V[i], V[j])
          QW = fiber_product(W, Q)
          h1 = inclusion_map(QW, domain(Q_on_V_patches[i]))
          h2 = inclusion_map(QW, domain(Q_on_V_patches[j]))
          compose(h1, Q_on_V_patches[i]) == compose(h2, Q_on_V_patches[j]) || error("maps do not coincide on overlaps")
        end
      end
    end
    return new{GlueingType, T, M}(G, P, Q, P_on_U_patches, Q_on_V_patches, f, g)
  end
end

### Proper schemes π : Z → X over a covered base scheme X
# 
# When {Uᵢ} is an affine covering of X, the datum stored 
# consists of a list of projective schemes 
#
#   Zᵢ ⊂ ℙʳ⁽ⁱ⁾(𝒪(Uᵢ)) → Uᵢ
#
# with varying ambient spaces ℙʳ⁽ⁱ⁾(𝒪(Uᵢ)) and a list of 
# identifications (transitions) 
#
#   Zᵢ ∩ π⁻¹(Uⱼ) ≅ Zⱼ ∩ π⁻¹(Uᵢ)
#
# of projective schemes over Uᵢ∩ Uⱼ for all pairs (i,j).
#
# These structs are designed to accomodate blowups of 
# covered schemes along arbitrary centers, as well as 
# projective bundles. 

mutable struct CoveredProjectiveScheme{
    BaseSchemeType<:CoveredScheme, 
    CoveringType<:Covering,
    SpecType<:Spec,
    ProjectiveSchemeType<:ProjectiveScheme,
    ProjectiveGlueingType<:ProjectiveGlueing,
    BRT, BRET} <: Scheme{BRT, BRET}
  Y::BaseSchemeType # the base scheme
  BC::CoveringType # the reference covering of the base scheme
  patches::Dict{SpecType, ProjectiveSchemeType} # the projective spaces over the affine patches in the base covering
  glueings::Dict{Tuple{SpecType, SpecType}, ProjectiveGlueingType} # the transitions sitting over the affine patches in the glueing domains of the base scheme

  function CoveredProjectiveScheme(
      Y::BaseSchemeType,
      C::CoveringType,
      projective_patches::Dict{SpecType, ProjectiveSchemeType},
      projective_glueings::Dict{Tuple{SpecType, SpecType}, ProjectiveGlueingType};
      check::Bool=true
    ) where {
             BaseSchemeType<:CoveredScheme, 
             CoveringType<:Covering,
             SpecType<:Spec,
             ProjectiveSchemeType<:ProjectiveScheme,
             ProjectiveGlueingType<:ProjectiveGlueing,
            }
    C in coverings(Y) || error("covering not listed")
    for P in values(projective_patches)
      base_scheme(P) in patches(C) || error("base scheme not found in covering")
    end
    for (U, V) in keys(glueings(C))
      (U, V) in keys(projective_glueings) || error("not all projective glueings were provided")
    end
    return new{CoveredSchemeType, CoveringType, SpecType, ProjectiveSchemeType, ProjectiveGlueingType, base_ring_type(SpecType), elem_type(base_ring_type(SpecType))}(Y, C, projective_patches, projective_glueings)
  end
end

function empty_covered_projective_scheme(R::T) where {T<:AbstractAlgebra.Ring}
  Y = empty_covered_scheme(R)
  C = default_covering(Y)
  U = C[1]
  ST = affine_patch_type(Y)
  pp = Dict{affine_patch_type(Y), projective_scheme_type(affine_patch_type(Y))}()
  P = projective_space(U, 0)
  pp[U] = P
  tr = Dict{Tuple{ST, ST}, Vector{morphism_type(pp[U])}}
  tr[(U, U)] = identity_map(P) 
  return CoveredProjectiveScheme(Y, C, pp, tr)
end

# blow up X in the center described by g using these explicit generators.
function blow_up(W::Spec, I::Vector{RingElemType}) where {RingElemType<:MPolyElem}

  # some internal function
  function _add_variables(R::RingType, v::Vector{Symbol}) where {RingType<:MPolyRing}
    ext_R, _ = PolynomialRing(coefficient_ring(R), vcat(symbols(R), v))
    n = length(gens(R))
    phi = AlgebraHomomorphism(R, ext_R, gens(ext_R)[1:n])
    return ext_R, phi, gens(ext_R)[(length(gens(R))+1):length(gens(ext_R))]
  end

  A = OO(W)
  R = base_ring(A)
  #TODO: Check if for all i \in I parent(i) == R

  m = length(I)
  Pw = projective_space(W,m-1)
  S = homogeneous_coordinate_ring(Pw)

  CP = affine_cone(Pw)
  Polyring = base_ring(OO(CP))
  At, embeddingAt, T =  _add_variables(R,[:t])
  t = T[1]

  #	@show vcat([t*embeddingAt(f) for f in I], gens(At)[1:end-1])
  Phi = AlgebraHomomorphism(Polyring, At, vcat([t*embeddingAt(f) for f in I], gens(At)[1:end-1]))
  kernel(Phi)

  Imod = modulus(A)
  IW = ideal(At, [embeddingAt(f) for f in gens(Imod)])
  IWpre = preimage(Phi, IW)
  #SIWpre = ideal(S,[frac_to_homog(Pw,g) for g in gens(IWpre)])
  SIWpre = ideal(S, poly_to_homog(Pw).(gens(IWpre)))


  return subscheme(Pw, SIWpre), [S(A(g)) for g in I]
end


function blow_up(I::IdealSheaf)
  X = scheme(I)
  C = covering(I)
  local_blowups = [blow_up(U, I[U]) for U in patches(C)]
  for (U, V) in keys(glueings(C))
    @show (U, V)
    G = C[U, V]
    UV, _ = glueing_domains(G)
    f, _ = glueing_morphisms(G)
    for i in 1:npatches(UV) 
      W = UV[i]
      @show W
      gensUW = OO(W).(I[U])
      gensVW = pullback(f[i]).(I[V])
      transitionUV = [write_as_linear_combination(g, gensVW) for g in gensUW]
      transitionVU = [write_as_linear_combination(g, gensUW) for g in gensVW]
      @show transitionUV
      @show transitionVU
    end
  end
end




