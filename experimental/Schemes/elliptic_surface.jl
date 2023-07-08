export elliptic_surface, trivial_lattice, weierstrass_model, weierstrass_chart, algebraic_lattice, zero_section, section, relatively_minimal_model, fiber_components, generic_fiber, reducible_fibers, fibration_type

@doc raw"""
    EllipticSurface{BaseField<:Field, BaseCurveFieldType} <: AbsCoveredScheme{BaseField}

The type of a relatively minimal elliptic surface.

A genus $1$-fibration is a proper map
$\pi \colon X \to C$ to a curve $C$ whose fibers are curves of
(arithmetic) genus $1$.
The fibration is relatively minimal if its fibers do not contain any ``(-1)``-curves.
We call the fibration elliptic if it comes equipped with a section.
This turns the generic fiber of $\pi$ into an elliptic curve $E/k(C)$ where
$k(C)$ is the function field of the curve $C$.
"""
@attributes mutable struct EllipticSurface{BaseField<:Field, BaseCurveFieldType} <: AbsCoveredScheme{BaseField}
  Y::CoveredScheme{BaseField}
  E::EllCrv{BaseCurveFieldType}
  MWL::Vector{EllCrvPt{BaseCurveFieldType}}
  MWLtors::Vector{EllCrvPt{BaseCurveFieldType}}
  Weierstrasschart::AbsSpec
  Weierstrassmodel::CoveredScheme
  inc_Weierstrass
  inc_Y
  bundle_number::Int
  blowup
  blowups
  exceptionals
  ambient_blowups
  ambient_exceptionals

  function EllipticSurface(generic_fiber::EllCrv{F}, bundle_number::Int, mwl_basis::Vector{<:EllCrvPt}) where F
    B = typeof(coefficient_ring(base_ring(base_field(generic_fiber))))
    S = new{B,F}()
    S.E = generic_fiber
    S.MWL = mwl_basis
    S.bundle_number = bundle_number
    set_attribute!(S, :is_irreducible=>true)
    set_attribute!(S, :is_reduced=>true)
    set_attribute!(S, :is_integral=>true)
    return S
  end

end

@doc raw"""
    elliptic_surface(generic_fiber::EllCrv, s::Int, mwl_basis::Vector{<:EllCrvPt}=EllCrvPt[]) -> EllipticSurface

Return the relatively minimal elliptic surface with generic fiber ``E``.
"""
function elliptic_surface(generic_fiber::EllCrv, s::Int, mwl_basis::Vector{<:EllCrvPt}=EllCrvPt[])
  @req all(parent(i)==generic_fiber for i in mwl_basis) "not a vector of points on $(generic_fiber)"
  S = EllipticSurface(generic_fiber, s, mwl_basis)
  return S
end

function underlying_scheme(S::EllipticSurface)
  if isdefined(S,:Y)
    return S.Y
  end
  return relatively_minimal_model(S)[1]
end

@doc raw"""
    generic_fiber(S::EllipticSurface) -> EllCrv

Return the generic fiber as an elliptic curve.
"""
generic_fiber(S::EllipticSurface) = S.E
weierstrass_chart(S::EllipticSurface) = S.Weierstrasschart

@doc raw"""
    algebraic_lattice(X) -> Vector{WeilDivisor}, ZZLat

Return the sublattice of ``Num(X)`` spanned by fiber components
and the sections provided at the construction of ``X``.
"""
@attr function algebraic_lattice(X)
  mwl_basis = X.MWL
  basisTriv, GTriv = trivial_lattice(X)

  # primitive closure of the trivial lattice comes from torsion sections
  tors = [section(X, h) for h in mordell_weil_torsion(X)]
  torsV = ZZMat[]
  for T in tors
    basis, NS = algebraic_lattice(X)
    G = gram_matrix(NS)
    n = length(basis)
    vT = zero_matrix(ZZ, 1, n)
    for i in 1:n
      vT[i] = intersect(basisTriv[i], T)
    end
    push!(torsV, vT*inv(GTriv))
  end


  l = length(mwl_basis)
  r = length(basisTriv)
  sections = [section(X, i) for i in mwl_basis]
  n = l+r
  GA = zero_matrix(ZZ, n, n)
  GA[1:r,1:r] = GTriv
  GA[r+1:n,r+1:n] = -2*identity_matrix(ZZ, l)
  basisA = vcat(basisTriv, sections)
  @vprint :EllipticSurface 2 "computing intersection numbers"
  for i in 1:n
    @vprint :EllipticSurface 2 "\nrow $(i): \n"
    for j in max(i + 1, r + 1):n
      @vprint :EllipticSurface 2 "$(j) "
      GA[i,j] = intersect(basisA[i],basisA[j])
      GA[j,i] = GA[i,j]
    end
  end
  @assert rank(GA) == n "todo: treat torsion sections" # need to adapt mordell_weil then too
  return basisA, integer_lattice(gram=GA)
end

@doc raw"""
    mordell_weil_lattice(S::EllipticSurface) -> Vector{EllCrvPt}, ZZLat

Return the (sublattice) of the Mordell-Weil lattice of ``S``  spanned
by the sections of ``S`` supplied at its construction.
"""
@attr ZZLat function mordell_weil_lattice(S::EllipticSurface)
  NS = algebraic_lattice(S)
  t = length(trivial_lattice(S)[1])
  trivNS = basis_matrix(NS)[1,:t]
  V = ambient_space(NS)
  P = orthogonal_complement(V, trivNS)
  mwl = rescale(lattice(V, basis_matrix(NS)*P, is_basis=false),-1)
  #Todo basis
  return lll(mwl)
end

@doc raw"""
    mordell_weil_torsion(S::EllipticSurface) ->

Return generators for the torsion part of the Mordell-Weil group
of the generic fiber of ``S``.
"""
@attr function mordell_weil_torsion(S::EllipticSurface)
  E = generic_fiber(S)
  O = E([0,1,0])
  N = trivial_lattice(S)
  tors = EllCrvPt[]
  for d in divisors(det(N))
    @vprint :EllipticSurface 2 "computing $(d)-torsion"
    append!(tors, division_points(E, d))
  end
  return tors
end

@doc raw"""

#Examples
```jldoctest

```
"""
function Base.show(io::IOContext, S::EllipticSurface)
  io = pretty(io)
  if get(io, :supercompact, false)
    print(io, "Elliptic surface")
  else
    print(io, "Elliptic surface with generic fiber ", equation(E))
  end
end

@doc raw"""
#Examples
```jldoctest

```
"""
function Base.show(io::IO, ::MIME"text/plain", S::EllipticSurface)
  io = pretty(io)
  println(io, "Elliptic surface")
  println(io, Indent(), "with generic fiber")
  print(io, Indent(), Lowercase(), generic_fiber(S), Dedent())
  if isdefined(S, :X)
    println(io, "")
    print(io, "with relative minimal model ", Lowercase(), S.Y)
  end
  print(io, Dedent())
end

@doc raw"""
    weierstrass_model(X::EllipticSurface) -> CoveredScheme, CoveredClosedEmbedding

Return the weierstrass model ``S`` of ``X`` and the inclusion

\[S \subseteq \mathbb{P}( \mathcal{O}_{\mathbb{P}^1}(-2s) \oplus \mathcal{O}_{\mathbb{P}^1}(-3s) \oplus \mathcal{O}_{\mathbb{P}^1})\]
"""
function weierstrass_model(X::EllipticSurface)
  if isdefined(X, :Weierstrassmodel)
    return X.Weierstrassmodel, X.inc_Weierstrass
  end

  s = X.bundle_number
  E = generic_fiber(X)

  kt = base_ring(base_field(E))
  k = coefficient_ring(kt)
  delta = factor(discriminant(E), kt).fac
  reducible_singular_fibers = [p for p in keys(delta) if delta[p]>1]

  IP1 = projective_space(k, 1)
  c = standard_covering(IP1)
  # rename the variables on the affine charts
  # to a more readable version
  OO(c[1]).S = [:t]
  OO(c[2]).S = [:s]


  O0 = twisting_sheaf(IP1, 0)
  O4 = twisting_sheaf(IP1, -2*s)
  O6 = twisting_sheaf(IP1, -3*s)

  bundleE = direct_sum([O0, O4, O6])

  P_proj = projectivization(bundleE, var_names=["z", "x", "y"])
  P = covered_scheme(P_proj)

  # Create the singular Weierstrass model S of the elliptic K3 surface X
  a = a_invars(E)
  U = affine_charts(P)[1]  # the standard Weierstrass chart
  (x, y, t) = gens(OO(U))
  @assert all(denominator(i)==1 for i in a)
  a = [numerator(a)(t) for a in a]
  (a1,a2,a3,a4,a6) = a
  ft = y^2  + a1*x*y + a3*y - (x^3 + a2*x^2 + a4*x+a6)
  I = IdealSheaf(P, U, [ft])

  inc_S = CoveredClosedEmbedding(P, I)
  Scov = domain(inc_S)  # The ADE singular elliptic K3 surface
  X.Weierstrasschart = Scov[1][1]

  X.Weierstrassmodel = Scov
  X.inc_Weierstrass = inc_S

  set_attribute!(Scov, :is_irreducible=>true)
  set_attribute!(Scov, :is_reduced=>true)
  set_attribute!(Scov, :is_integral=>true)
  return Scov, inc_S
end

@doc raw"""
    _separate_singularities!(X::EllipticSurface) -> Covering

Create a covering of the ambient projective bundle $P$
of the Weierstrass model $S$ of $X$ such that each chart
(of $X$) contains at most one singular point of $S$.
Append this covering to the list of coverings of $X$ and return it.
"""
function _separate_singularities!(X::EllipticSurface)
  S, inc_S = weierstrass_model(X)
  P = codomain(inc_S)

  I_sing = ideal_sheaf_of_singular_locus(S)
  I_sing_P = radical(pushforward(inc_S)(I_sing))

  # Refine the covering over the reducible singular fibers
  # to make sure that there is only a single singular point in each chart
  refined_charts = AbsSpec[]
  U = P[1][1]  # the weierstrass_chart
  IsingU = I_sing_P(U)
  if isone(IsingU)
    push!(refined_charts, U)
  else
    # there is at most one singularity in every fiber
    # project the singular locus to an affine chart of P1
    disc = gens(eliminate(IsingU, coordinates(U)[1:2]))[1]
    redfib = [f[1] for f in factor(disc)]
    if length(redfib)==1
      push!(refined_charts, U)
    else
      for i in 1:length(redfib)
        r = copy(redfib)
        deleteat!(r, i)
        push!(refined_charts, PrincipalOpenSubset(U, r))
      end
    end
  end

  # Create a chart which contains the fiber over s=0
  # and no other reducible singular fibers
  # these are visible in the charts that we have already
  # i.e. we add the fiber at s=0 and remove all other singular fibers
  V = P[1][4]
  IsingV = I_sing_P(V)
  if isone(IsingV)
    push!(refined_charts, V)
  else
    # reducible singular fibers
    disc = gens(eliminate(IsingV, coordinates(V)[1:2]))[1]
    (x,y,s) = coordinates(V)
    b, d = divides(disc, s)
    if b
      disc = d
    end
    redfib = [f[1] for f in factor(disc)]
    if length(redfib)> 0
      push!(refined_charts, PrincipalOpenSubset(V, redfib))
    else
      push!(refined_charts, V)
    end
  end

  # no extra singularities in the X = 1 chart
  # therefore we just exclude all the singularities visible here
  for W in [P[1][2],P[1][5]]
    local Ising = I_sing_P(W)
    if isone(Ising)
      push!(refined_charts, W)
      continue
    end
     (z,y,s_or_t) = coordinates(W)
    # reducible singular fibers
    local disc = gens(eliminate(Ising, [z, s_or_t]))[1]
    local redfib = collect(keys(factor(disc).fac))
    push!(refined_charts, PrincipalOpenSubset(W, redfib))
  end

  # no extra singularities on the the zero section
  # This is the Y = 1 chart
  # therefore we just exclude all the singularities visible here
  for W in [P[1][3],P[1][6]]
    local Ising = I_sing_P(W)
    if isone(Ising)
      push!(refined_charts, W)
      continue
    end
    local (z,x,s_or_t) = coordinates(W)
    # reducible singular fibers
    local disc = gens(eliminate(Ising, [x, s_or_t]))[1]
    local redfib = collect(keys(factor(disc).fac))
    push!(refined_charts, PrincipalOpenSubset(W, redfib))
  end


  Cref = Covering(refined_charts)
  inherit_glueings!(Cref, P[1])
  push!(P.coverings, Cref)
  # Now we have an extra covering where each chart just contains a single singularity

  @assert scheme(I_sing) === S
  @assert scheme(I_sing_P) === P
  return Cref
end

@doc raw"""
    relatively_minimal_model(E::EllipticSurface) -> CoveredScheme, SchemeMor

Return the relatively minimal model $X \to C$ and the contraction
$\Psi \colon X \to S$ to its weierstrass model $S$.
"""
function relatively_minimal_model(E::EllipticSurface)
  if isdefined(E, :blowups)
    return E.Y, E.blowup
  end
  S, inc_S = weierstrass_model(E)
  Crefined = _separate_singularities!(E)
  # Blow up singular points (one at a time) until smooth
  # and compute the strict transforms of the `divisors`
  # collect the exceptional divisors
  # blowup ambient spaces: X0 → X   ⊂
  # blowup pi: (K3 = Y0)  → (S singular weierstrass model)
  #
  # initialization for the while loop
  X0 = codomain(inc_S)
  Y0 = S
  inc_Y0 = inc_S

  exceptionals = []
  varnames = [:a,:b,:c,:d,:e,:f,:g,:h,:i,:j,:k,:l,:m,:n,:o,:p,:q,:r,:u,:v,:w]
  projectionsX = []
  projectionsY = []
  count = 0

  @vprint :EllipticSurface 2 "Blowing up Weierstrass model\n"
  @vprint :EllipticSurface 2 "in $(Crefined)\n"
  while true
    count = count+1
    @vprint :EllipticSurface 1 "blowup number: $(count)\n"
    @vprint :EllipticSurface 2 "computing singular locus\n"
    I_sing_Y0 = ideal_sheaf_of_singular_locus(Y0)
    @vprint :EllipticSurface 2 "decomposing singular locus\n"
    I_sing_Y0 = maximal_associated_points(I_sing_Y0)
    I_sing_X0 = pushforward(inc_Y0).(I_sing_Y0)
    @vprint :EllipticSurface 1 "number of singular points: $(length(I_sing_Y0))\n"
    if length(I_sing_Y0)==0
      # stop if smooth
      break
    end
    # make sure there is only one singular point per chart
    if count == 1
      cov = Crefined
    else
      cov0 = simplified_covering(X0)
      cov1 = _separate_disjoint_components(I_sing_X0, covering=cov0)
      cov = _one_patch_per_component(cov1, I_sing_X0)
      push!(X0.coverings, cov)
      #inc_Y0 = inc_Y0a
    end
    # take the first singular point and blow it up
    J = radical(I_sing_X0[1])
    pr_X1 = blow_up(J, covering=cov, var_name=varnames[1+mod(count, length(varnames))])
    X1 = domain(pr_X1)
    @vprint :EllipticSurface 1 "$(X1)\n"
    E1 = exceptional_divisor(pr_X1)

    @vprint :EllipticSurface 2 "computing strict transforms\n"
    # compute the exceptional divisors
    exceptionals = [strict_transform(pr_X1, e) for e in exceptionals]
    # move the divisors coming originally from S up to the next chart
    push!(exceptionals, E1)

    Y1, inc_Y1, pr_Y1 = strict_transform(pr_X1, inc_Y0)

    push!(projectionsX, pr_X1)
    push!(projectionsY, pr_Y1)
    simplify!(Y1)

    # set up for the next iteration
    Y0 = Y1
    inc_Y0 = inc_Y1
    X0 = X1
  end
  E.Y = Y0
  E.blowups = projectionsY
  E.ambient_blowups = projectionsX
  E.ambient_exceptionals = exceptionals
  piY = reduce(*, reverse(projectionsY))
  E.blowup = piY
  E.inc_Y = inc_Y0

  set_attribute!(Y0, :is_irreducible=>true)
  set_attribute!(Y0, :is_reduced=>true)
  set_attribute!(Y0, :is_integral=>true)
  return Y0, piY
end

#  global divisors0 = [strict_transform(pr_X1, e) for e in divisors0]
#exceptionals_res = [pullback(inc_Y0)(e) for e in exceptionals]
@doc raw"""
    _trivial_lattice(S::EllipticSurface)

Internal function. Output:
basis of the trivial lattice, gram matrix, fiber_components
"""
@attr function _trivial_lattice(S::EllipticSurface)
  #=
  inc_Y = S.inc_Y
  X = codomain(inc_Y)
  exceptionals_res = [pullback(inc_Y0)(e) for e in exceptionals]
  ExWeil = WeilDivisor.(exceptional_res)
  tmp = []
  ExWeil = reduce(append!, [components(i) for i in ExWeil], init= tmp)
  =#
  W = weierstrass_model(S)
  d = numerator(discriminant(generic_fiber(S)))
  kt = parent(d)
  k = coefficient_ring(kt)
  r = [k.(roots(i[1])) for i in factor(d) if i[2]>=2]
  sing = reduce(append!,r, init=[])
  f = []
  f = [[k.([i,1]), fiber_components(S,[i,k(1)])] for  i in sing]
  if degree(d) <= 12*S.bundle_number - 2
    pt = k.([1, 0])
    push!(f, [pt, fiber_components(S, pt)])
  end
  O = zero_section(S)

  F = weil_divisor(ideal_sheaf(irreducible_fiber(S)), check=false)
  basisT = [F, O]
  @assert S.bundle_number == 2

  grams = [ZZ[0 1;1 -2]]
  # TODO: the -2 self intersection is probably some K3 artefact
  fiber_componentsS = []
  for (pt, ft) in f
    @vprint :EllipticSurface 2 "normalizing fiber: over $pt \n"
    Ft0 = standardize_fiber(S, ft)
    @vprint :EllipticSurface 2 "$(Ft0[1]) \n"
    append!(basisT , Ft0[3][2:end])
    push!(grams,Ft0[4][2:end,2:end])
    push!(fiber_componentsS, vcat([pt], collect(Ft0)))
  end
  G = block_diagonal_matrix(grams)
  # make way for some more pretty printing
  for (pt,root_type,_,comp) in fiber_componentsS
    for (i,I) in enumerate(comp)
      name = string(root_type[1], root_type[2])
      set_attribute!(components(I)[1], :name, string("Component ", name, "_", i-1," of fiber over ", Tuple(pt)))
    end
  end
  return basisT, G, fiber_componentsS
end

@doc raw"""
    trivial_lattice(X::EllipticSurface) -> Vector{WeilDivisor}, ZZMatrix

Return a basis for the trivial lattice as well as its gram matrix.

The trivial lattice is the lattice spanned by fiber components and
the zero section of $X$.
"""
function trivial_lattice(X::EllipticSurface)
  T = _trivial_lattice(X)[1:2]
  return T
end

@doc raw"""
    reducible_fibers(S::EllipticSurface)

Return the reducible fibers of $S$.

The output format is the following:
A list [F1, ..., Fn] where each entry Fi represents a reducible fiber.

The list $F$ has the following entries:
- A point $P \in \mathbb{P}^{1}$ such that $F = \pi^{-1}(P)$;
- The ADE-type of the fiber;
- The fiber $F$ as a Weil divisor, including its multiplicities;
- The irreducible components of the fiber. The first component intersects the zero section;
- Their intersection matrix.
"""
function reducible_fibers(S::EllipticSurface)
  return _trivial_lattice(S)[3]
end

isone(I::IdealSheaf) = isone(I, space(I)[1])

function isone(I::IdealSheaf, C::Covering)
  return all(isone(I(U)) for U in C)
end

@doc raw"""
    standardize_fiber(S::EllipticSurface, f::Vector{<:WeilDivisor})

Internal method. Used to prepare for [`reducible_fibers`](@ref).
`f` must be the list of the components of the reducible fiber `F`.
"""
function standardize_fiber(S::EllipticSurface, f::Vector{<:WeilDivisor})
  @req all(is_prime(i) for i in f) "not a vector of prime divisors"
  f = copy(f)
  O = components(zero_section(S))[1]
  for (i,D) in enumerate(f)
    if !isone(O+components(D)[1])
      global f0 = D
      deleteat!(f,i)
      break
    end
  end
  r = length(f)
  G = -2*identity_matrix(ZZ, r)
  @vprint :EllipticSurface 2 "computing intersections:"
  for i in 1:r
    @vprint :EllipticSurface 3 "\nrow $(i): \n"
    for j in 1:i-1
      @vprint :EllipticSurface 4 "$(j) "
      # we know the intersections are 0 or 1
      if isone(components(f[i])[1]+components(f[j])[1])
        G[i,j] = 0
      else
        G[i,j] = 1
      end
      G[j,i] = G[i,j]
    end
  end
  L = integer_lattice(gram=G)
  rt,_ = root_lattice_recognition(L)
  @assert length(rt)==1
  rt = rt[1]
  R = root_lattice(rt[1], rt[2])
  b, I = is_isomorphic_with_permutation(G, -gram_matrix(R))
  @assert b
  gensF = vcat([f0], f[I])
  Gext, v = extended_ade(rt[1],rt[2])
  Fdiv = sum(v[i]*gensF[i] for i in 1:length(gensF))
  return rt, Fdiv, gensF, Gext
end

@doc raw"""
    fiber_cartier(S::EllipticSurface, P::Vector = ZZ.([0,1])) -> EffectiveCartierDivisor

Return the fiber of $\pi\colon X \to C$ as a Cartier divisor.
"""
function fiber_cartier(S::EllipticSurface, P::Vector = ZZ.([0,1]))
  S0,_ = weierstrass_model(S)
  _ = relatively_minimal_model(S) # cache stuff
  D = IdDict{AbsSpec, RingElem}()
  k = base_ring(S0)
  P = k.(P)

  if P[1]!=0 && P[2]!=0
    t0 = P[1] * inv(P[2])
    for i in 1:3
      U = S0[1][i]
      (_,_,t) = coordinates(U)
      D[U] = t-t0
    end
    s0 = inv(t0)
    for i in 4:6
      U = S0[1][i]
      (_,_,s) = coordinates(U)
      D[U] = s - s0
    end
  elseif P[1] != 0
    # it is the fiber at [1:0]
    for i in 4:6
      U = S0[1][i]
      (_,_,s) = coordinates(U)
      D[U] = s
    end
    for i in 1:3
      U = S0[1][i]
      (_,_,t) = coordinates(U)
      D[U] = one(parent(t))
    end
  elseif P[2] != 0
    # the fiber at [0:1]
    for i in 1:3
      U = S0[1][i]
      (_,_,t) = coordinates(U)
      D[U] = t
    end
    for i in 4:6
      U = S0[1][i]
      (_,_,s) = coordinates(U)
      D[U] = one(parent(s))
    end
  else
    error("[0,0] is not a point in projective space")
  end
  F = EffectiveCartierDivisor(S0, D, trivializing_covering=S0[1])
  return pullback(S.blowup)(F)
end

@doc raw"""
    fiber_components(S::EllipticSurface, P) -> Vector{<:WeilDivisor}

Return the fiber components of the fiber over the point $P \in C$.
"""
function fiber_components(S::EllipticSurface, P)
  @vprint :EllipticSurface 2 "computing fiber components over $(P)\n"
  F = fiber_cartier(S, P)
  @vprint :EllipticSurface 2 "decomposing fiber   "
  comp = maximal_associated_points(ideal_sheaf(F))
  @vprint :EllipticSurface 2 "done decomposing fiber\n"
  return [weil_divisor(c, check=false) for c in comp]
end

@doc raw"""
    irreducible_fiber(S::EllipticSurface) -> EffectiveCartierDivisor

Return an irreducible fiber as a cartier divisor.
"""
function irreducible_fiber(S::EllipticSurface)
  W = weierstrass_model(S)
  d = numerator(discriminant(generic_fiber(S)))
  kt = parent(d)
  k = coefficient_ring(kt)
  r = [k.(roots(i[1])) for i in factor(d) if i[2]>=2]
  sing = reduce(append!,r, init=[])

  if degree(d) >= 12*S.bundle_number - 1  # irreducible at infinity?
    pt = k.([1, 0])
  else
    if is_finite(k)
      found = false
      for i in k
        if !(i in sing)  # true if the fiber over [i,1] is irreducible
          pt = k.([i,1])
          found = true
          break
        end
      end
      found || error("there is no irreducible fiber defined over the base field")
    else
      i = k(0)
      while true
        i = i+1
        if !(i in sing)
          pt = k.([i,1])
          break
        end
      end
    end
  end
  # F = fiber_components(S,pt) this does not terminate .... so we have to build it by hand
  # @assert length(F) == 1
  F = fiber_cartier(S, pt)
  return F
end

@doc raw"""
    section(X::EllipticSurface, P::EllCrvPt)

Given a rational point $P\in E(C)$ of the generic fiber $E/C$ of $\pi\colon X \to C$,
return its closure in $X$ as a `WeilDivisor`.
"""
function section(X::EllipticSurface, P::EllCrvPt)
  @vprint :EllipticSurface 3 "Computing a section from a point on the generic fiber\n"
  S0,incS0 = weierstrass_model(X)
  X0 = codomain(incS0)
  if P[3] == 0
    # zero section
    V = X0[1][3]
    (z,x,t) = coordinates(V)
    PX = IdealSheaf(X0, V, [x,z])
  else
    U = X0[1][1]
    (x,y,t) = coordinates(U)
    b = P
    PX = ideal_sheaf(X0,U,[OO(U)(i) for i in [x*denominator(b[1])(t)-numerator(b[1])(t),y*denominator(b[2])(t)-numerator(b[2])(t)]])
  end
  for f in X.ambient_blowups
    PX = strict_transform(f , PX)
  end
  PY = pullback(X.inc_Y, PX)
  set_attribute!(PY, :name, string("section: (",P[1]," : ",P[2]," : ",P[3],")"))
  return WeilDivisor(PY, check=false)
end

@doc raw"""
    zero_section(S::EllipticSurface) -> WeilDivisor

Return the zero section of the relatively minimal elliptic
fibration \pi\colon X \to C$.
"""
@attr zero_section(S::EllipticSurface) = section(S, generic_fiber(S)([0,1,0]))

@doc raw"""
    is_isomorphic_with_map(G1::Graph, G2::Graph) -> Bool, Vector{Int}

Return an isomorphism from `G1` to `G2` given in terms of a
vector of integers.
"""
function is_isomorphic_with_map(G1::Graph, G2::Graph)
  f12 = Polymake.graph.find_node_permutation(G1.pm_graph, G2.pm_graph)
  if isnothing(f12)
    return false, Vector{Int}()
  end
  return true, Polymake.to_one_based_indexing(f12)
end

@doc raw"""
    graph(G::MatElem)

Return the undirected graph defined by the square matrix `G = (g_{ij})_{ij}`.

Two nodes $i,j \in {1, \dots n\}$ with $i>j$ are joined by an edge
if and only if $g_{ij} == 1$.
"""
function graph(G::MatElem)
  n = nrows(G)
  g = Graph{Undirected}(n)
  for i in 1:n
    ## small hack to single out the fiber
    #if G[i,i]==0
    #  add_edge!(g,i,i)
    #end
    for j in 1:i-1
      if G[i,j] == 1
        add_edge!(g,i,j)
      end
    end
  end
  return g
end

@doc raw"""
    is_isomorphic_with_permutation(A1::MatElem, A2::MatElem) -> Bool, Vector{Int}

Return a permutation ``T`` with ``A1[T,T] == A2`` and whether it exists.
"""
function is_isomorphic_with_permutation(A1::MatElem, A2::MatElem)
  b, T = is_isomorphic_with_map(graph(A1),graph(A2))
  @assert b || A1[T,T] == A2
  return b, T
end

################################################################################
#
# Some linear systems on elliptic surfaces
#
################################################################################

"""
    _prop217(E::EllCrv, P::EllCrvPt, k)

Compute a basis for the linear system
|O + P + kF|
on the  minimal elliptic (K3) surface defined by E.
Here F is the class of a fiber O the zero section
and P any non-torsion section.

```jldoctest
julia> kt,t = polynomial_ring(GF(29),:t);

julia> ktfield = fraction_field(kt);

julia> bk = [((17*t^4 + 23*t^3 + 18*t^2 + 2*t + 6, 8*t^5 + 2*t^4 + 6*t^3 + 25*t^2 + 24*t + 5 )),
             ((17*t^6 + 3*t^5 + 16*t^4 + 4*t^3 + 13*t^2 + 6*t + 5)//(t^2 + 12*t + 7), (4*t^8 + 19*t^7 + 14*t^6 + 18*t^5 + 27*t^4 + 13*t^3 + 9*t^2 + 14*t + 12)//(t^3 + 18*t^2 + 21*t + 13) ),
             ((17*t^6 + 10*t^5 + 24*t^4 + 15*t^3 + 22*t^2 + 27*t + 5)//(t^2 + 16*t + 6), (20*t^8 + 24*t^7 + 22*t^6 + 12*t^5 + 21*t^4 + 21*t^3 + 9*t^2 + 21*t + 12)//(t^3 + 24*t^2 + 18*t + 19) ),
             ((17*t^8 + 21*t^7 + 20*t^5 + 24*t^4 + 21*t^3 + 4*t^2 + 9*t + 13)//(t^4 + 17*t^3 + 12*t^2 + 28*t + 28), (23*t^11 + 25*t^10 + 8*t^9 + 7*t^8 + 28*t^7 + 16*t^6 + 7*t^5 + 23*t^4 + 9*t^3 + 27*t^2 + 13*t + 13)//(t^6 + 11*t^5 + 14*t^4 + 13*t^3 + 6*t^2 + 18*t + 12) )];

julia> E = EllipticCurve(ktfield,[3*t^8+24*t^7+22*t^6+15*t^5+28*t^4+20*t^3+16*t^2+26*t+16, 24*t^12+27*t^11+28*t^10+8*t^9+6*t^8+16*t^7+2*t^6+10*t^5+3*t^4+22*t^3+27*t^2+10*t+3]);

julia> bk = [E(collect(i)) for i in bk];

julia> prop217(E,bk[2],2)
5-element Vector{Any}:
 (t^2 + 12*t + 7, 0)
 (t^3 + 8*t + 3, 0)
 (t^4 + 23*t + 2, 0)
 (25*t + 22, 1)
 (12*t + 28, t)

julia> prop217(E,bk[1],1)
2-element Vector{Any}:
 (1, 0)
 (t, 0)
```
"""
function _prop217(E::EllCrv, P::EllCrvPt, k)
  @req !iszero(P[3]) "P must not be torsion" # seems like we cannot check this
  xn = numerator(P[1])
  xd = denominator(P[1])
  yn = numerator(P[2])
  yd = denominator(P[2])
  OP = divexact(max(degree(xd), degree(xn) - 4), 2)
  dega = k + 2*OP
  degb = k + 2*OP - 2 - divexact(degree(xd), 2) #?
  base = base_field(E)
  Bt = base_ring(base)
  B = coefficient_ring(Bt)

  R,ab = polynomial_ring(base,vcat([Symbol(:a,i) for i in 0:dega],[Symbol(:b,i) for i in 0:degb]),cached=false)
  Rt, t1 = polynomial_ring(R,:t)
  a = reduce(+,(ab[i+1]*t1^i for i in 0:dega), init=zero(Rt))
  b = reduce(+,(ab[2+dega+j]*t1^j for j in 0:degb), init=zero(Rt))
  c = a*xn(t1) - b*yn(t1)
  r = mod(c, xd(t1))
  # setup the linear equations for coefficients of r to vanish
  # and for the degree of c to be bounded above by
  # k + 2*OP + 4 + degree(xd)
  eq1 = collect(coefficients(r))
  eq2 = [coeff(c,i) for i in (k + 2*OP + 4 + degree(xd) + 1):degree(c)]
  eqns = vcat(eq1, eq2)

  # collect the equations as a matrix
  cc = [[coeff(j, abi) for abi in ab] for j in eqns]
  M = matrix(B, length(eqns), length(ab), reduce(vcat,cc, init=elem_type(base)[]))
  # @assert M == matrix(base, cc) # does not work if length(eqns)==0
  kerdim, K = kernel(M)
  result = Tuple{elem_type(Bt),elem_type(Bt)}[]
  t = gen(Bt)
  for j in 1:kerdim
    aa = reduce(+, (K[i+1,j]*t^i for i in 0:dega), init=zero(Bt))
    bb = reduce(+, (K[dega+i+2,j]*t^i for i in 0:degb), init=zero(Bt))
    push!(result, (aa, bb))
  end
  # confirm the computation
  @assert kerdim == 2*k + OP # prediced by Riemann-Roch
  for (a,b) in result
    @assert mod(a*xn - b*yn, xd) == 0
    @assert degree(a) <= k + 2*OP
    @assert degree(b) <= k + 2*OP - 2 - 1//2*degree(xd)
    @assert degree(a*xn - b*yn) <= k + 2*OP + 4 + degree(xd)
  end
  return result
end

@doc raw"""
    linear_system(X::EllipticSurface, P::EllCrvPt, k::Int64) -> LinearSystem

Compute the linear system ``|O + P + k F|`` on the elliptic surface ``X``.
Here ``F`` is the class of the fiber over ``[0:1]``, ``O`` the zero section
and ``P`` any section given as a point on the generic fiber.
"""
function linear_system(X::EllipticSurface, P::EllCrvPt, k::Int64)
  X.bundle_number == 2 || error("linear system implemented only for elliptic K3s")
  FS = function_field(weierstrass_model(X)[1])
  U = weierstrass_chart(X)
  (x,y,t) = ambient_coordinates(U)

  sections = elem_type(FS)[]
  if iszero(P[3])
    append!(sections, [FS(t)^(i-k) for i in 0:k])
    append!(sections, [FS(t)^(i-k)*FS(x) for i in 0:k-4])
  elseif iszero((2*P)[3])
    error("not implemented for 2-torsion sections")
  else
    xn = numerator(P[1])
    xd = denominator(P[1])
    yn = numerator(P[2])
    yd = denominator(P[2])

    I = ambient_closure_ideal(U)
    IP = ideal([x*xd(t)-xn(t),y*yd(t)-yn(t)])
    issubset(I, IP) || error("P does not define a point on the Weierstrasschart")

    @assert gcd(xn, xd)==1
    @assert gcd(yn, yd)==1
    ab = _prop217(generic_fiber(X), P, k)
    d = divexact(yd, xd)(t)
    den = t^k*(x*xd(t) - xn(t))
    for (a,b) in ab
      c = divexact(b*yn - a*xn, xd)
      num = a(t)*x+b(t)*d*y + c(t)
      push!(sections, FS(num//den))
    end
  end
  return sections
  sectionsX = pullback(X.blowup).(sections)
  return sectionX
end

"""
  elliptic_parameter(X::EllipticSurface, F::ZZMat) -> LinearSystem

Return the complete linear system ``|F|``.

Here `F` must be given with respect to the basis of
`algebraic_lattice(X)` and be an isotropic nef divisor.
"""
function elliptic_parameter(X::EllipticSurface, F::ZZMatrix)
  NS = algebraic_lattice(X)
  @req F*gram_matrix(NS)*transpose(F) "not an isotropic divisor"
  @req is_nef(X, F) "F is not net"
  error("not implemented")



  X.bundle_number
  E = generic_fiber(X)

  L = linear_system(X, E([0,1,0]), 4)

  (x,y,t) = ambient_coordinates(weierstrass_chart(X3))

  L = [i*function_field(S)(t^2,t-1) for i in L]

  LonX3 = linear_system(pullback(piS).(L2), D2, check=false);

  LsubF2, Tmat = subsystem(L2onX3, F2);

  LsubF2onS = [sum(Tmat[i,j]*L[j] for j in 1:ncols(Tmat)) for i in 1:nrows(Tmat)]

  @assert length(L2subF2onS)==2

  u2 = LsubF2onS[2]//LsubF2onS[1]
end



@doc raw"""

"""
function extended_ade(ADE::Symbol, n::Int)
  R = change_base_ring(ZZ,gram_matrix(root_lattice(ADE,n)))
  G = block_diagonal_matrix([ZZ[2;],R])
  if ADE == :E && n == 8
    G[1,n] = -1
    G[n,1] = -1
  end
  if ADE == :E && n == 7
    G[1,2] = -1
    G[2,1] = -1
  end
  if ADE == :E && n == 6
    G[1,n+1] = -1
    G[n+1,1] = -1
  end
  if ADE == :A && n > 0
    G[1,2] = -1
    G[2,1] = -1
    G[1,n+1] = -1
    G[n+1,1] = -1
  end
  if ADE == :A && n ==1 0
    G[1,2]= -2
    G[2,1] = -2
  end
  if ADE == :D
    G[1,n] = -1
    G[n,1] = -1
  end
  @assert rank(G) == n
  return -G, left_kernel(G)[2]
end

function basis_representation(X::EllipticSurface, D::WeilDivisor)
  basis, NS = algebraic_lattice(X)
  G = gram_matrix(NS)
  n = length(basis)
  v = zeros(fmpz, )
  for i in 1:n
    v[i] = intersect(basis[i],D)
  end
  return v*inv(G)
end

################################################################################
#
# patches for Oscar
#
################################################################################


# Disable simplification for the usage of (decorated) quotient rings within the
# schemes framework (speedup of ~2).
function simplify(f::MPolyQuoRingElem{<:Union{<:MPolyRingElem, MPolyQuoLocRingElem,
                                              <:MPolyQuoRingElem, MPolyLocRingElem}}
  )
  return f
end