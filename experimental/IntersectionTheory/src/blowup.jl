function _parse_symbol(symbol::String, I::UnitRange)
  return ["$symbol[$i]" for i in I]
end
function _parse_symbol(symbol::String, n::Int, I::UnitRange)
  return [symbol*"[$n, $i]" for i in I]
end
######################################
@doc raw"""
      blow_up(i::AbstractVarietyMap; symbol::String="e")

Given an inclusion `i`$ : $ `X` $\rightarrow$ `Y`, say, return the blow-up of `Y` along `X`.

More precisely, return a tuple `(Bl, E, j)`, say, where
- `Bl`, an abstract variety, is the blow-up,
- `E`, an abstract variety, is the exceptional divisor, and
- `j`, a map of abstract varieties, is the inclusion of `E` into `Bl`.

!!! note
    The resulting maps `Bl` $\rightarrow$ `Y` and `E` $\rightarrow$ `X` are obtained entering `structure_map(Bl)` and `structure_map(E)`, respectively.

# Examples

Taken from the sage package Chow by Lehn/Sorger:

```jldoctest
julia> P2xP2 = abstract_projective_space(2, symbol = "k")*abstract_projective_space(2, symbol = "l")
AbstractVariety of dim 4

julia> P8 = abstract_projective_space(8)
AbstractVariety of dim 8

julia> k, l = gens(P2xP2)
2-element Vector{MPolyQuoRingElem{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}}:
 k
 l

julia> Se = map(P2xP2, P8, [k+l])
AbstractVarietyMap from AbstractVariety of dim 4 to AbstractVariety of dim 8

julia> Bl, E, j = blow_up(Se)
(AbstractVariety of dim 8, AbstractVariety of dim 7, AbstractVarietyMap from AbstractVariety of dim 7 to AbstractVariety of dim 8)

julia> betti_numbers(Bl)
9-element Vector{Int64}:
 1
 2
 4
 7
 8
 7
 4
 2
 1

```

# The Steiner problem:

```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> P5 = abstract_projective_space(5, symbol = "H")
AbstractVariety of dim 5

julia> h = gens(P2)[1]
h

julia> H = gens(P5)[1]
H

julia> i = map(P2, P5, [2*h])
AbstractVarietyMap from AbstractVariety of dim 2 to AbstractVariety of dim 5

julia> Bl, E, j = blow_up(i)
(AbstractVariety of dim 5, AbstractVariety of dim 4, AbstractVarietyMap from AbstractVariety of dim 4 to AbstractVariety of dim 5)

julia> e, HBl = gens(chow_ring(Bl))
2-element Vector{MPolyQuoRingElem{MPolyDecRingElem{QQFieldElem, QQMPolyRingElem}}}:
 e
 H

julia> integral((6*HBl-2*e)^5)
3264

```
"""
function blow_up(i::AbstractVarietyMap; symbol::String = "e")
  # use construction via generators and relations as in Eisenbud-Harris, Section 13.6
  #  E ---j---> Bl
  #  |          |
  #  g          f
  #  |          |
  #  Z ---i---> X

  SED = symbol # SED = "e"
  Z, X = i.domain, i.codomain
  AZ, RZ = Z.ring, base_ring(Z.ring)
  AX, RX = X.ring, base_ring(X.ring)

  # we write N for the normal bundle N_{ZX}

  N = -i.T # normal bundle
  rN = rank(N) # codimension of Z in X
  rN <= 0 && error("not a proper subvariety")

  # we construct E as the projective bundle PN of N, see [E-H, p 472]

  E = abstract_projective_bundle(N) 
  AE, RE = E.ring, base_ring(E.ring)
  g = E.struct_map
  ζ = g.O1  # the first Chern class of O_E(1)

  # we set up the generators of ABl

  # we first represent AZ as an AX-module

  gs, PM, sect = present_finite_extension_ring(i.pullback)
  ngs = length(gs)
  # note: gs is a vector of polynomials representing generators for AZ as an AX-module;
  #       write Z(gs[i]) for the class in AZ represented by gs[i];
  #       if e[i] = jₓgˣ(Z(gs[i])), then e[end] is the class of the exceptional divisor in ABl;
  #       here, present_finite_extension_ring needs to return the generators accordingly;
  #       that is, Z(gs[end]) must by the generator 1_{AZ}; note that ζ = -jˣ(e[end]).

  # by E-H, Prop. 13.12, ABl is generated by jₓ(AE) and  fˣ(AX) as a K-algebra;
  # equivalently, as an AX-algebra, ABl is generated by the e[i].
  syms = vcat(push!(_parse_symbol(SED, 1:ngs-1), SED), string.(gens(RX))) # set e = e[end]
  degs = [degree(Int, Z(gs[i])) + 1 for i in 1:ngs]
  degsRX = [Int(degree(gens(RX)[i])[1])  for i = 1:ngens(RX)]
  RBl = graded_polynomial_ring(X.base, syms, vcat(degs, degsRX))[1]
  
  ev, xv = gens(RBl)[1:ngs], gens(RBl)[ngs+1:end]
  RXtoRBl = hom(RX, RBl, xv) # fˣ on polynomial ring level
  jₓgˣ = x -> sum(ev .* RXtoRBl.(sect(x.f))) # AZ --> RBl

  # we set up the relations of ABl

  Rels = elem_type(RBl)[]

  # 1) relations from AX

  if isdefined(AX, :I)
    for r in RXtoRBl.(gens(AX.I)) push!(Rels, r) end
  end

  # 2) relations for AZ as an AX-module

  for r in RXtoRBl.(PM)*ev push!(Rels, r) end

  # 3) relation from AE: ∑ gˣcₖ(N) ⋅ ζᵈ⁻ᵏ = 0, see EH Thm. 9.6

  cN = total_chern_class(N)[0:rN] # cN[k] = c_k ₋₁(N)
  push!(Rels, sum([jₓgˣ(cN[k+1]) * (-ev[end])^(rN-k) for k in 0:rN]))

  # 4) jₓx ⋅ jₓy = -jₓ(x⋅y⋅ζ) # rule for multiplication, EH, Prop. 13.12
  # recall that e[i] = jₓgˣ(Z(gs[i]))

  for j in 1:ngs-1, k in j:ngs-1
    push!(Rels, ev[j] * ev[k] + jₓgˣ(Z(gs[j] * Z(gs[k]))) * (-ev[end]))
  end

  # 5) relation as in the proof of [E-H], Theorem 13.14:
  # RXtoRBliₓx = jₓ(gˣx ⋅ ctop(Q)) where Q is the tautological quotient bundle on E
  # we have ctop(Q) = ∑ gˣcₖ₋₁(N) ⋅ ζᵈ⁻ᵏ, EH p. 477

  for j in 1:ngs
    lhs = RXtoRBl(i.pushforward(Z(gs[j])).f) # this is the crucial step where iₓ is needed
    rhs = sum([jₓgˣ(Z(gs[j]) * cN[k]) * (-ev[end])^(rN-k) for k in 1:rN])
    push!(Rels, lhs - rhs)
  end
 
  Rels = minimal_generating_set(ideal(RBl, Rels)) ### TODO: make this an option?
  ABl, _ = quo(RBl, Rels)
  Bl = abstract_variety(X.dim, ABl)

  # Bl and g being constructed, we set up the morphisms f and j

  # pushforward of f and more

  RBltoRX = hom(RBl, RX, vcat(repeat([RX()], ngs), gens(RX)))
  fₓ = x -> (xf = simplify(x).f;
	     X(RBltoRX(xf));)
  fₓ = map_from_func(fₓ, ABl, AX)
  f = AbstractVarietyMap(Bl, X, Bl.(xv), fₓ)
  Bl.struct_map = f
  if isdefined(X, :point) Bl.point = f.pullback(X.point) end

  # pullback of j
  
  jˣ = vcat([-ζ * g.pullback(Z(xi)) for xi in gs], [g.pullback(i.pullback(f)) for f in gens(AX)])
  
  # pushforward of j: write as a polynomial in ζ, and compute term by term

  REtoRZ = hom(RE, RZ, pushfirst!(gens(RZ), RZ()))
  jₓ = x -> (xf = simplify(x).f;
            ans = RBl();
	    for k in rN-1:-1:0
	      q = div(xf, ζ.f^k)
	      ans += jₓgˣ(Z(REtoRZ(q))) * (-ev[end])^k
	      xf -= q * ζ.f^k
	    end;
	    Bl(ans))
  jₓ = map_from_func(jₓ, AE, AX)
  j = AbstractVarietyMap(E, Bl, jˣ, jₓ)

  # the normal bundle of E in Bl is O(-1)

  j.T = -E.bundles[1]

  # finally, compute the tangent bundle of Bl

  # 0 → Bl.T → RXtoRBl(X.T) → jₓ(Q) → 0 where Q is the tautological quotient bundle

  f.T = -pushforward(j, E.bundles[2])
  Bl.T = pullback(f, X.T) + f.T

# chern(Bl.T) can be readily computed from its Chern character, but the following is faster
  α = sum(sum((binomial(ZZ(rN-j), ZZ(k)) - binomial(ZZ(rN-j), ZZ(k+1))) * ζ^k for k in 0:rN-j) * g.pullback(chern_class(N, j)) for j in 0:rN)
  Bl.T.chern = simplify(f.pullback(total_chern_class(X.T)) + j.pushforward(g.pullback(total_chern_class(Z.T)) * α))
  set_attribute!(E, :projections => [j, g])
  set_attribute!(Bl, :exceptional_divisor => E)
  set_attribute!(Bl, :description => "Blow-Up of $X with center $Z")
  if get_attribute(Z, :alg) == true && get_attribute(X, :alg) == true
    set_attribute!(Bl, :alg => true)
  end
  return Bl, E, j
end


@doc raw"""
    function blow_up_points(X::AbstractVariety, n::Int; symbol::String = "e")

Return the blow-up of `X` at `n` points.

# Examples
```jldoctest
julia> P2 = abstract_projective_space(2)
AbstractVariety of dim 2

julia> Bl = blow_up_points(P2, 1)
AbstractVariety of dim 2

julia> chow_ring(Bl)
Quotient
  of multivariate polynomial ring in 2 variables over QQ graded by
    e -> [1]
    h -> [1]
  by ideal (e*h, e^2 + h^2)

```
"""
function blow_up_points(X::AbstractVariety, n::Int; symbol::String = "e")
  SED = symbol # SED = "e"
  if n == 1
    symbs = [SED]
  else
    symbs = _parse_symbol(SED, 1:n)
  end
  Bl = X
  P = abstract_point(base = X.base)
  for i in 1:n
    Bl = blow_up(map(P, Bl, [zero(P.ring) for j = 1:i]), symbol=symbs[i])[1]
  end
  set_attribute!(Bl, :description => "Blow_Up of $X at $n points")
  Bl.struct_map = map(Bl, X)
  if get_attribute(X, :alg) == true
    set_attribute!(Bl, :alg => true)
  end
  return Bl
end







