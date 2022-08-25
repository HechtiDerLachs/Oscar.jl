#R, x = PolynomialRing(QQ, ["x$i$j" for i in 1:3 for j in i:3])
#M = R[x[1] x[2] x[3]; x[2] x[4] x[5]; x[3] x[5] x[6]]
#E = QQ.([1, 0, 0, 1, 0, 1])
#G = AffineMatrixGroup(M, ideal(R, [x[2], x[3]]), E)

G = special_linear_group(2, QQ)
rho = canonical_representation(G)
rep = induced_representation_on_symmetric_power(G, 2)

O = omega_process(G)
nullcone_ideal(rep)
@show "blubb"
reynolds_operator_from_omega_process(rep)

