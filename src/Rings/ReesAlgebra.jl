########################################################################
# Rees algebras of modules 
#
# Following Eisenbud, Huneke, Ulrich: "What is the Rees algebra 
# of a module?"; arXiv:math/0209187v1
########################################################################

@Markdown.doc """
    rees_algebra(f::ModuleFPHom{<:ModuleFP, <:FreeMod}; check::Bool=true)

For a *versal* (†) morphism ``f : M → F`` of a module ``M`` into a free 
module ``F`` this computes the Rees algebra of ``M`` according to [1].

!!!Note: if `check` is set to `true`, the method will check the sufficient
criterion "``fᵀ : F* → M*`` surjective" to verify that ``f`` is versal. 
Since no general criterion is known, this will abort with an error message 
in the non-affirmative case.

[1]: Eisenbud, Huneke, and Ulrich: "What is the Rees algebra of a module?", 
     arXiv:math/0209187v1.

(†) A morphism of ``M`` into a free module ``F`` as above is called 
versal if any other morphism ``g : M → F'`` from ``M`` to another 
free module ``F'`` factors through ``f``.
"""
function rees_algebra(f::ModuleFPHom{<:ModuleFP, <:FreeMod, Nothing};
    check::Bool=true,
    var_names::Vector{String}=["s$i" for i in 0:ngens(domain(f))-1]
  )
  if check
    f_dual = dual(f)
    is_surjective(f_dual) || error("it can not be verified that the map is versal")
  end

  M = domain(f)
  R = base_ring(M)
  F = codomain(f)
  R === base_ring(F) || error("modules must be defined over the same ring")
  P = presentation(M)::ChainComplex
  p = map(P, 0)
  FM = P[0]
  r = rank(FM)
  sym_FM, s = PolynomialRing(R, Symbol.(var_names))
  sym_F, t = PolynomialRing(R, [Symbol("t$i") for i in 1:rank(F)])
  imgs = Vector{elem_type(sym_F)}()
  for v in gens(FM)
    w = coordinates(f(p(v)))
    push!(imgs, sum(w[i]*t[i] for i in 1:length(t)))
  end
  sym_g = hom(sym_FM, sym_F, imgs)
  K = kernel(sym_g)
  rees, _ = quo(sym_FM, K)
  return rees
end

function rees_algebra(M::FreeMod; 
    var_names::Vector{String}=["s$i" for i in 0:ngens(M)-1]
  )
  R = base_ring(M)
  r = rank(M)
  S, s = PolynomialRing(R, Symbol.(var_names))
  #S, _ = grade(S_tmp)
  return S
end

function rees_algebra(M::SubQuo; 
    var_names::Vector{String}=["s$i" for i in 0:ngens(M)-1],
    check::Bool=true
  )
  success, p, sigma = is_projective(M)
  if success
    # The easy case: The Rees algebra is simply a polynomial ring 
    # modulo linear equations in the variables parametrized by the base.
    R = base_ring(M)
    r = ngens(M)
    S_tmp, s = PolynomialRing(R, Symbol.(var_names))
    S, sg = grade(S_tmp)
    A = matrix(p) # The presentation matrix
    I = ideal(S, [sum(A[i, j]*sg[j] for j in 1:length(s)) for i in 1:nrows(A)])
    Q, sq = quo(S, I)
    return Q
  end

  # The complicated case. We construct a versal morphism f : M → F to a 
  # free module along the lines of Proposition 1.3 of [1] (in its published version).
  return rees_algebra(_versal_morphism_to_free_module(M), check=false)
end

### Auxiliary methods needed for the Rees algebras

### The following function is implemented along the lines of Proposition 1.3 of [1] in 
# its published version.
function _versal_morphism_to_free_module(M::SubQuo)
  R = base_ring(M)
  R1 = FreeMod(R, 1)
  M_double_dual, psi = double_dual(M, cod=R1)
  M_dual = domain(element_to_homomorphism(zero(M_double_dual)))
  pres_M_dual = presentation(M_dual)::ChainComplex
  g = map(pres_M_dual, 0) # The projection of a free module onto M_dual
  g_dual = dual(g, cod=R1, codomain_dual=M_double_dual)
  return compose(psi, g_dual)
end

function proj(S::MPolyRing_dec)
  is_standard_graded(S) || error("ring must be standard graded")
  return ProjectiveScheme(S)
end

function proj(Q::MPolyQuo{<:MPolyElem_dec})
  S = base_ring(Q)
  is_standard_graded(S) || error("ring must be standard graded")
  return ProjectiveScheme(Q)
end

#function is_injective(f::ModuleFPHom) 
#  return iszero(kernel(f)[1])
#end
#
#function is_surjective(f::ModuleFPHom)
#  return iszero(cokernel(f))
#end

function is_isomorphism(f::ModuleFPHom)
  return is_injective(f) && is_surjective(f)
end

### Auxiliary deflections for MPolyQuos to make arithmetic work in the Rees algebras

function simplify!(
    a::MPolyQuoElem{AbstractAlgebra.Generic.MPoly{T}}
  ) where {T<:Union{<:MPolyElem, <:MPolyQuoElem, 
                    <:MPolyLocalizedRingElem,
                    <:MPolyQuoLocalizedRingElem}
          }
  return a
end

function iszero(
    a::MPolyQuoElem{AbstractAlgebra.Generic.MPoly{T}}
  ) where {T<:Union{<:MPolyElem, <:MPolyQuoElem, 
                    <:MPolyLocalizedRingElem,
                    <:MPolyQuoLocalizedRingElem}
          }
  phi = flatten(base_ring(parent(a)))
  I = phi(modulus(parent(a)))
  return phi(lift(a)) in I
end

function isone(
    a::MPolyQuoElem{AbstractAlgebra.Generic.MPoly{T}}
  ) where {T<:Union{<:MPolyElem, <:MPolyQuoElem, 
                    <:MPolyLocalizedRingElem,
                    <:MPolyQuoLocalizedRingElem}
          }
  phi = flatten(base_ring(parent(a)))
  I = phi(modulus(parent(a)))
  return phi(lift(a) - one(domain(phi))) in I
end


function ==(a::MPolyQuoElem{AbstractAlgebra.Generic.MPoly{T}},
            b::MPolyQuoElem{AbstractAlgebra.Generic.MPoly{T}}
           ) where {T<:Union{<:MPolyElem, <:MPolyQuoElem, 
                             <:MPolyLocalizedRingElem,
                             <:MPolyQuoLocalizedRingElem}
                   }
  phi = flatten(base_ring(parent(a)))
  I = phi(modulus(parent(a)))
  return phi(lift(a) - lift(b)) in I
end

