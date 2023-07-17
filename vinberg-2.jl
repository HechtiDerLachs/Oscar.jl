include("test/AlgebraicGeometry/Schemes/fibration_hop.jl")

#kk = GF(29)
kk = QQ
Qt, t = polynomial_ring(kk, :t)

Qtf = fraction_field(Qt)

E = EllipticCurve(Qtf, [0,0,0,0,t^5*(t-1)^2])

R = rescale(root_lattice([(:E, 8), (:E, 8), (:A, 2)]), -1);

U = integer_lattice(gram=ZZ[0 1; 1 -2]);

NS, _ = direct_sum([U, R]);

e = matrix(ZZ,1,20,ones(Int,20));e[1,1]=51;

ample = e*inv(gram_matrix(NS));

fibers = [
 QQ[1   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0   0;],
 QQ[4   2   -4   -7   -10   -8   -6   -4   -2   -5   -2   -4   -6   -5   -4   -3   -2   -3   -1   -1;],
 QQ[4   2   -4   -7   -10   -8   -6   -4   -2   -5   -4   -7   -10   -8   -6   -4   -2   -5   0   0;],
 QQ[6   3   -5   -10   -15   -12   -9   -6   -3   -8   -5   -10   -15   -12   -9   -6   -3   -8   -1   -1;],
 QQ[10   5   -8   -16   -24   -20   -15   -10   -5   -12   -7   -14   -21   -17   -13   -9   -5   -11   -3   -2;],
 QQ[6   3   -4   -8   -12   -10   -8   -6   -3   -6   -4   -8   -12   -10   -8   -6   -3   -6   -2   -1;]]

X3 = elliptic_surface(E, 2);

S = weierstrass_model(X3)[1];

X3cov, piS = relatively_minimal_model(X3);

basisNSX3, _, NSX3 = algebraic_lattice(X3);

b, I = Oscar.is_isomorphic_with_permutation(gram_matrix(NS), gram_matrix(NSX3))

@assert gram_matrix(NSX3) == gram_matrix(NS)[I,I]

u2 = Oscar.elliptic_parameter(X3, vec(collect(fibers[2]))[I])

kkt2, t2 = polynomial_ring(kk, "t2"); kkt2f = fraction_field(kkt2)

P, (x2,y2) = polynomial_ring(kkt2, ["x2","y2"]); Pf = fraction_field(P)

(x,y,t) = ambient_coordinates(weierstrass_chart(X3))

n = numerator(u2); d = evaluate(denominator(u2), P.([0,0,x2]));

a = evaluate(n, P.([0,0,x2]))//d

b  = evaluate(div(n, x), P.([0,0,x2]))//d

eqn1 = gen(Oscar.ambient_closure_ideal(weierstrass_chart(X3)),1)

phi1 = hom(parent(x), Pf,Pf.([Pf(t2)//b, y2, x2]))

eqn2 = numerator(phi1(eqn1))

g, phi2 = normalize_quartic(eqn2)

phi2 = extend_domain(phi2, fraction_field(domain(phi2)))

(x,y) = gens(parent(g))

(a,b) = transform_to_weierstrass(g,x,y,base_ring(parent(g)).([0,0]));

phi3 = hom(parent(a),parent(a), [a,b])

phi = phi1*phi2*phi3

g2 = numerator(evaluate(g,gens(parent(g)), [a,b]))

E2 = elliptic_curve(g2, x, y)
#Elliptic curve with equation
#y^2 = x^3 - t2^3*x^2 + t2^3*x
# P2 = (t2^3 : t2^3 : 1)
t2 = gen(base_field(E2))

P2 = E2([t2^3,t2^3]) # the lattice data suggested that the A2 fiber gives two sections

X2 = elliptic_surface(E2, 2, [P2])

### Bis hier!!!

algebraic_lattice(X2)

# we copy paste phi
(x, y, t2) = ambient_coordinates(weierstrass_chart(X2))
imgs = [ (-t2*x + t2)//x^3, (x*y - y)//x^5, 1//x]

S3, inc3 = weierstrass_model(X3)
S2, inc2 = weierstrass_model(X2)
_,pi3 = relatively_minimal_model(X3)
_,pi2 = relatively_minimal_model(X2)
# pi3: X3 ---> S3
# pi2: X2 ---> S2
# phi: S2 ---> S3 [ (-t2*x + t2)//x^3, (x*y - y)//x^5, 1//x]
U2 = weierstrass_chart(X2)
U3 = weierstrass_chart(X3)

Oscar.RationalMap(S2,S3, U2, U3, imgs)

V3 = S3[1][1] # The surface in the Weierstrass chart
pi3_cov = covering_morphism(pi3)
cov = codomain(pi3_cov)
V3sub = first([V for V in patches(cov) if ambient_scheme(V)===V3])
pi3_loc = first(oscar.maps_with_given_codomain(pi3, V3sub))

x = gens(ambient_coordinate_ring(domain(pi3_loc)))
set_attribute!(X3, :is_irreducible, true)
X3_res = domain(pi3)
x = function_field(X3_res).(x)

V2 = S2[1][1] # The surface in the Weierstrass chart
pi2_cov = covering_morphism(pi2)
cov = codomain(pi2_cov)
#V2sub = first([V for V in patches(cov) if ambient_scheme(V)===V2])
V2sub = V2
pi2_loc = first(oscar.maps_with_given_codomain(pi2, V2sub))

y = gens(ambient_coordinate_ring(domain(pi2_loc)))
set_attribute!(X2, :is_irreducible, true)
X2_res = domain(pi2)
y = function_field(X2_res).(y)

blowups2 = X2.ambient_blowups
p2 = first(blowups2)
set_attribute!(domain(projection(p2)), :is_irreducible, true)
img_gens2 = gens(ambient_coordinate_ring(U2))
Fdown = function_field(codomain(p2))
img_gens2 = Fdown.(img_gens2)
for p in blowups2
  set_attribute!(codomain(projection(p)), :is_irreducible, true)
  set_attribute!(domain(projection(p)), :is_irreducible, true)
  Fdown = function_field(codomain(projection(p)))
  @show Fdown === function_field(codomain(projection(p)))
  Fup = function_field(domain(projection(p)))
  @show Fdown === parent(first(img_gens2))
  img_gens2 = [pullback(p, a) for a in img_gens2]
  @show img_gens2
  @show parent(first(img_gens2)) === Fup
end

ambient_res2 = domain(last(blowups2))
W2_sub = domain(pi2_loc)
coord2 = function_field(ambient_res2).(gens(ambient_coordinate_ring(W2_sub)))

for p in reverse(blowups2)
  set_attribute!(codomain(projection(p)), :is_irreducible, true)
  set_attribute!(domain(projection(p)), :is_irreducible, true)
  Fdown = function_field(codomain(projection(p)))
  @show Fdown === function_field(codomain(projection(p)))
  Fup = function_field(domain(projection(p)))
  @show Fup === parent(first(coord2))
  coord2 = [pushforward(p, a) for a in coord2]
  @show coord2
  @show parent(first(coord2)) === Fdown
end

U2_ambient = codomain(inc2[U2])
coord2 = [a[U2_ambient] for a in coord2]
pb_coord2 = [evaluate(a, coord2) for a in imgs]



blowups3 = X3.ambient_blowups
p3 = first(blowups3)
set_attribute!(domain(projection(p3)), :is_irreducible, true)
img_gens3 = gens(ambient_coordinate_ring(U3))
Fdown = function_field(codomain(p3))
img_gens3 = Fdown.(img_gens3)
for p in blowups3
  set_attribute!(codomain(projection(p)), :is_irreducible, true)
  set_attribute!(domain(projection(p)), :is_irreducible, true)
  Fdown = function_field(codomain(projection(p)))
  @show Fdown === function_field(codomain(projection(p)))
  Fup = function_field(domain(projection(p)))
  @show Fdown === parent(first(img_gens3))
  img_gens3 = [pullback(p, a) for a in img_gens3]
  @show img_gens3
  @show parent(first(img_gens3)) === Fup
end

ambient_res3 = domain(last(blowups3))
W3_sub = domain(pi3_loc)
set_attribute!(ambient_res3, :is_irreducible, true)
coord3 = function_field(ambient_res3).(gens(ambient_coordinate_ring(W3_sub)))

for p in reverse(blowups3)
  set_attribute!(codomain(projection(p)), :is_irreducible, true)
  set_attribute!(domain(projection(p)), :is_irreducible, true)
  Fdown = function_field(codomain(projection(p)))
  @show Fdown === function_field(codomain(projection(p)))
  Fup = function_field(domain(projection(p)))
  @show Fup === parent(first(coord3))
  coord3 = [pushforward(p, a) for a in coord3]
  @show coord3
  @show parent(first(coord3)) === Fdown
end

U3_ambient = codomain(inc3[U3])
coord3 = [a[U3_ambient] for a in coord3]
# The pullback of the coordinates of the chart W3_sub through the rational map down to the 
# Weierstrass model of X2.
#pb_coord3 = [evaluate(a, coord3) for a in imgs]
pb_coord3 = [evaluate(a, imgs) for a in coord3]

blowups2 = X2.ambient_blowups
p2 = first(blowups2)
set_attribute!(domain(projection(p2)), :is_irreducible, true)
img_gens2 = gens(ambient_coordinate_ring(U2))
Fdown = function_field(codomain(p2))
img_gens2 = Fdown.(pb_coord3)
for p in blowups2
  set_attribute!(codomain(projection(p)), :is_irreducible, true)
  set_attribute!(domain(projection(p)), :is_irreducible, true)
  Fdown = function_field(codomain(projection(p)))
  @show Fdown === function_field(codomain(projection(p)))
  Fup = function_field(domain(projection(p)))
  @show Fdown === parent(first(img_gens2))
  img_gens2 = [pullback(p, a) for a in img_gens2]
  @show img_gens2
  @show parent(first(img_gens2)) === Fup
end

X2_res = domain(pi2)
X3_res = domain(pi3)
set_attribute!(X2_res, :is_irreducible, true)
set_attribute!(X3_res, :is_irreducible, true)
F2 = function_field(X2_res)
F3 = function_field(X3_res)
coord3_res = F3.(gens(ambient_coordinate_ring(W3_sub)))
W3_res = first([a for a in patches(default_covering(X3_res)) if ambient_coordinate_ring(a) === ambient_coordinate_ring(W3_sub)])
W2_res = first([a for a in patches(default_covering(X2_res)) if ambient_coordinate_ring(a) === ambient_coordinate_ring(W2_sub)])
WW = first([a for a in patches(oscar.simplified_covering(ambient_res2)) if ambient_coordinate_ring(a) === ambient_coordinate_ring(W2_sub)])
WW_orig = oscar.original(WW)
W2_amb = first([a for a in patches(default_covering(ambient_res2)) if ambient_coordinate_ring(a) === ambient_coordinate_ring(WW_orig)])
ff, gg = oscar.identification_maps(WW)

frac_list = [a[WW_orig] for a in img_gens2]
frac_list = [fraction(pullback(ff)(numerator(a)))//fraction(pullback(ff)(denominator(a))) for a in frac_list]
psi = oscar.RationalMap(X2_res, X3_res, W2_res, W3_res, frac_list)
set_attribute!(psi, :is_isomorphism, true)
#oscar.realize_on_patch(psi, W2_res)

#realiz = oscar.realize_maximally_on_open_subset(psi, W2_res, W3_res)
divisors3, _ = algebraic_lattice(X3)
D = WeilDivisor[]
for dd in divisors3
  push!(D, pullback(psi, dd))
end

# Task psi =  pi3^-1 \circ phi \circ pi2 is an isomorphism X2 -> X3
# pull back all divisors from algebraic_lattice(X3)[1] to X2 via psi
# and compute their basis representation.
# (equivalently you can pushforward all in algebraic_lattice(X2)
# and compute their basis representation

