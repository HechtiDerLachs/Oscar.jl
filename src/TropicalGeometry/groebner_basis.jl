###
# Computing (tropical) Groebner bases in Oscar
# ============================================
#
# For a definition of tropical Groebner basis see Section 2.4 in:
#   D. Maclagan, B. Sturmfels: Introduction to tropical geometry
# To see how they can be computed using standard bases see:
#   T. Markwig, Y. Ren: Computing tropical varieties over fields with valuation
###



#=======
returns true if f is homogeneous (w.r.t. total degree),
returns false otherwise
=======#
function _is_homogeneous(f::MPolyRingElem)
  leadexpv,tailexpvs = Iterators.peel(AbstractAlgebra.exponent_vectors(f))
  d = sum(leadexpv)
  for tailexpv in tailexpvs
    if d!=sum(tailexpv)
      return false
    end
  end
  return true
end

#=======
returns true if I has homogeneous generators,
returns false otherwise
=======#
function _has_homogeneous_generators(I::MPolyIdeal{K} where {K})
  # todo: replace with function that properly tests whether ideal is homogeneous
  #   this requires interreduction which is not available in Oscar yet
  return all(_is_homogeneous, gens(I))
end



@doc Markdown.doc"""
    groebner_basis(I::Ideal, val::TropicalSemiringMap, w::Vector; complete_reduction::Bool, return_lead::Bool)

Compute a Groebner basis of `I` over a field with valuation `val` with respect
to weight vector `w`, that is a finite generating set of `I` whose initial forms
generate the initial ideal with respect to `w`.

For the definitions of initial form, initial ideal and Groebner basis see
Section 2.4 of [MS15](@cite).

!!! warning
    Groebner bases over fields with valuation are still in an experimental stage.
    `I` must be generated by homogeneous polynomials and `val` must be non-trivial.

# Examples
```jldoctest
julia> R,(x,y) = polynomial_ring(QQ,["x","y"]);

julia> I = ideal([x^3-5*x^2*y,3*y^3-2*x^2*y])
ideal(x^3 - 5*x^2*y, -2*x^2*y + 3*y^3)

julia> val_2 = TropicalSemiringMap(QQ,2);

julia> w = [0,0];

julia> groebner_basis(I,val_2,w)
5-element Vector{QQMPolyRingElem}:
 2*x^2*y - 3*y^3
 x^3 - 5*x^2*y
 x*y^3 - 5*y^4
 y^5
 x^2*y^3 + 69*y^5
```
"""
function groebner_basis(I::MPolyIdeal,val::TropicalSemiringMap,w::Vector{<: Union{Int,Rational{Int}} }; complete_reduction::Bool=false, return_lead::Bool=false)

  @assert Oscar._has_homogeneous_generators(I)

  ###
  # Step 1: Compute a standard basis in the simulation ring
  ###
  vvI = simulate_valuation(I,val)
  w = simulate_valuation(w,val)
  Rtx = base_ring(vvI)
  # todo: replace with groebner_bases in OSCAR once more orderings are supported
  S,_ = Singular.polynomial_ring(singular_coeff_ring(base_ring(Rtx)), map(string, Nemo.symbols(Rtx)), ordering = Singular.ordering_a(w)*Singular.ordering_dp())
  SI = Singular.Ideal(S, [S(g) for g in gens(vvI)])
  vvGB = Singular.gens(Singular.std(SI,complete_reduction=complete_reduction))


  ###
  # Step 2: tighten simulation so that no two monomials of the standard basis
  # elements have the same x-monomial
  ###
  vvGB = [S(tighten_simulation(Rtx(g),val)) for g in vvGB]


  ###
  # Step 3: if complete_reduction = true and val is non-trivial, eliminate
  # tail-monomials contained in the leading ideal in the tropical sense
  #  In the simulation, these monomials corresponds to tail-monomials contained
  #  in the leading ideal up to saturation by t and elimination means
  #  eliminating them after multiplying by a sufficiently high power in t
  ###
  if complete_reduction==true && is_valuation_nontrivial(val)
    sort!(vvGB,lt=_x_monomial_lt) # sort vvGB by their leading x monomial from small to large
    Singular.libSingular.set_option("OPT_INFREDTAIL", true)
    for i in 1:length(vvGB)-1
      for j in i+1:length(vvGB)
        vvGB[j] = Singular.reduce(vvGB[j],Singular.std(Singular.Ideal(S,vvGB[i])))
      end
    end
    Singular.libSingular.set_option("OPT_INFREDTAIL", false)
  end

  GB = desimulate_valuation(ideal(Rtx,vvGB),val)
  if return_lead
    vvLI = Singular.lead(vvGB)
    LI = desimulate_valuation(ideal(Rtx,Singular.gens(vvLI)),val)
    return gens(GB),gens(LI)
  end

  return gens(GB)
end



#=======
returns true if the leading x-monomial of f is less than that of g,
returns false otherwise
=======#
function _x_monomial_lt(f::Singular.spoly,g::Singular.spoly)
  expv_f = copy(Singular.leading_exponent_vector(f))
  expv_g = copy(Singular.leading_exponent_vector(g))
  popfirst!(expv_f)
  popfirst!(expv_g)
  return expv_f<expv_g
end
