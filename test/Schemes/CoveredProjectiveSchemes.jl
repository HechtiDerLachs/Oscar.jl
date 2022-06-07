@testset "Projective glueings" begin
  P = projective_space(QQ, 1)
  PC = as_covered_scheme(P)
  C = default_covering(PC)
  U = C[1]
  V = C[2]
  G = C[1, 2]
  WU, WV = glueing_domains(G)
  PWU = projective_space(OO(WU), 2, var_name="u")
  PU = projective_space(ambient(WU), 2, var_name="u")
  PWV = projective_space(OO(WV), 2, var_name="v")
  PV = projective_space(ambient(WV), 2, var_name="v")
  SPWU = homog_poly_ring(PWU)
  SPWV = homog_poly_ring(PWV)
  f, g = glueing_morphisms(G)
  phi = ProjectiveSchemeMor(PWU, PWV, hom(SPWV, SPWU, pullback(f), gens(SPWU)))
  psi = ProjectiveSchemeMor(PWV, PWU, hom(SPWU, SPWV, pullback(g), gens(SPWV)))
  phiC = map_on_affine_cones(phi)
  psiC = map_on_affine_cones(psi)
  @test compose(psiC, phiC) == identity_map(affine_cone(PWV))
  @test compose(phiC, psiC) == identity_map(affine_cone(PWU))

  PG = ProjectiveGlueing(G, 
                         ProjectiveSchemeMor(PWU, PU, 
                                             hom(homog_poly_ring(PU), 
                                                 homog_poly_ring(PWU), 
                                                 OO(WU), 
                                                 gens(homog_poly_ring(PWU))
                                                )
                                            ),
                         ProjectiveSchemeMor(PWV, PV, 
                                             hom(homog_poly_ring(PV), 
                                                 homog_poly_ring(PWV), 
                                                 OO(WV), 
                                                 gens(homog_poly_ring(PWV))
                                                )
                                            ),
                         phi,
                         psi
                        );
end

