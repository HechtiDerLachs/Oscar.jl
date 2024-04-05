@testset "Rational maps" begin
  IP3 = projective_space(QQ, [:x, :y, :z, :w])
  S = homogeneous_coordinate_ring(IP3)
  (x, y, z, w) = gens(S)
  I = ideal(S, x*w - y*z)
  X_proj = subscheme(IP3, I)
  X = covered_scheme(X_proj)

  P1 = projective_space(QQ, 1)
  IP1 = covered_scheme(P1)
  U = X[1][4]
  V = IP1[1][2]
  (x, y, z) = gens(ambient_coordinate_ring(U))
  Phi = morphism_from_rational_functions(X, IP1, U, V, [x//y])

  @test domain(Phi) === X 
  @test codomain(Phi) === IP1

  Oscar.realize_on_patch(Phi, U)
  Oscar.realize_on_patch(Phi, X[1][1])
  Oscar.realize_on_patch(Phi, X[1][2])
  Oscar.realize_on_patch(Phi, X[1][3])
  Oscar.realize(Phi)
end

@testset "preimages for polynomial maps" begin
  R, (x, y) = QQ[:x, :y]
  I = ideal(R, [x-y])
  A, _ = quo(R, I)
  phi1 = hom(R, A, gens(A))
  @test phi1(preimage(phi1, A(y))) == A(x)
  
  phi2 = hom(R, A, [u^2 for u in gens(A)])
  @test_throws ErrorException preimage(phi2, A(x))
  @test phi2(preimage(phi2, A(x^2))) == A(x*y)

  U = powers_of_element(x-1)
  R_loc, _ = localization(R, U)
  A_loc, _ = localization(A, U)

  phi3 = hom(R, A_loc, gens(A_loc))
  @test A(preimage(phi3, A_loc((y-1)*x//(x-1)))) == A(y)

  phi4 = hom(R, R_loc, gens(R_loc))
  @test preimage(phi4, R_loc(x)) == x

  P, (_, _, u) = QQ[:x, :y, :u]
  J = ideal(P, 1 - prod(gens(P)))
  Q, _ = quo(P, J)

  S = powers_of_element(x*y)
  RS, _ = localization(R, S)
  phi5 = hom(RS, Q, gens(Q)[1:2])
  @test preimage(phi5, Q(u)) == RS(1//(x*y))

  AS, _ = localization(A, S)
  Q2, _ = quo(Q, ideal(Q, [Q[1]-Q[2]]))
  phi6 = hom(AS, Q2, gens(Q2)[1:2])
  @test preimage(phi6, Q2[1]) == AS[2]
end

@testset "The standard Cremona transformation" begin
  IP2_proj = projective_space(QQ, [:x, :y, :z])
  IP2 = covered_scheme(IP2_proj)
  S = homogeneous_coordinate_ring(IP2_proj)
  (x, y, z) = gens(S)
  I1 = ideal(S, [x, y])
  I2 = ideal(S, [x, z])
  I3 = ideal(S, [y, z])
  I = I1*I2*I3
  II = simplify!(IdealSheaf(IP2_proj, I))
  bl = blow_up(II)
  X = domain(projection(bl))
  set_attribute!(X, :is_irreducible, true)
  V = first(affine_charts(IP2))
  U = first(affine_charts(X))
  pr_cov = covering_morphism(projection(bl))
  U_simp = first(patches(Oscar.simplified_covering(X)))
  pb_y, pb_z = pullback(pr_cov[U]).(gens(OO(V)))
  Phi = Oscar.MorphismFromRationalFunctions(X, X, U, U, [inv(fraction(pb_y)), fraction(pb_z)//fraction(pb_y), fraction(pb_z)])
  Oscar.realize_on_patch(Phi, U)

  Hx = IdealSheaf(IP2_proj, ideal(S, x))
  Hy = IdealSheaf(IP2_proj, ideal(S, y))
  Hz = IdealSheaf(IP2_proj, ideal(S, z))

  pr = projection(bl)
  pbHx = strict_transform(bl, Hx)
  pbHy = strict_transform(bl, Hy)
  pbHz = strict_transform(bl, Hz)

  E = Oscar.irreducible_decomposition(weil_divisor(exceptional_divisor(bl)))

  H = weil_divisor.([pbHx, pbHy, pbHz])
  E1, E2, E3 = weil_divisor.(components(E))
  set_attribute!(Phi, :is_isomorphism, true)
  pbE1 = pushforward(Phi)(E1)
  @test any(x->x==pbE1, H)
  pbE2 = pushforward(Phi)(E2)
  @test any(x->x==pbE2, H)
  pbE3 = pushforward(Phi)(E3)
  @test any(x->x==pbE3, H)

  # Test the different versions of realization and their compatibility
  realizations = []
  for U in affine_charts(X)
    realizations = vcat(realizations, Oscar.realize_on_patch(Phi, U))
  end

  new_patches = [domain(phi) for phi in realizations]
  new_cod = unique!([codomain(phi) for phi in realizations])
  dom_cov = Covering(new_patches)
  cod_cov = Covering(new_cod)

  Oscar.inherit_gluings!(dom_cov, default_covering(X))
  Oscar.inherit_gluings!(cod_cov, default_covering(X))
  mor_dict = IdDict{AbsAffineScheme, AbsAffineSchemeMor}()
  for phi in realizations
    mor_dict[domain(phi)] = phi
  end

  # Call with check=true implitictly
  phi_cov = CoveringMorphism(dom_cov, cod_cov, mor_dict)

  realizations = []
  for U in affine_charts(X)
    for V in affine_charts(X) 
      realizations = vcat(realizations, Oscar.realize_maximally_on_open_subset(Phi, U, V))
    end
  end


  new_patches = [domain(phi) for phi in realizations]
  new_cod = unique!([codomain(phi) for phi in realizations])
  dom_cov = Covering(new_patches)
  cod_cov = Covering(new_cod)

  Oscar.inherit_gluings!(dom_cov, default_covering(X))
  Oscar.inherit_gluings!(cod_cov, default_covering(X))
  mor_dict = IdDict{AbsAffineScheme, AbsAffineSchemeMor}()
  for phi in realizations
    mor_dict[domain(phi)] = phi
  end
  # Call with check=true implitictly
  phi_cov = CoveringMorphism(dom_cov, cod_cov, mor_dict)
end
