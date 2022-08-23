#R, x = PolynomialRing(QQ, ["x$i$j" for i in 1:3 for j in i:3])
#M = R[x[1] x[2] x[3]; x[2] x[4] x[5]; x[3] x[5] x[6]]
#E = QQ.([1, 0, 0, 1, 0, 1])
#G = AffineMatrixGroup(M, ideal(R, [x[2], x[3]]), E)

R, x = QQ["x₁", "x₂"]
S, y = QQ["y₁", "y₂"]
X = Spec(R)
Y = Spec(S)
f = SpecMor(X, Y, [x[1]^2, x[2]^3])
P = subscheme(Y, [y[1]-4, y[2]-9])
inc = inclusion_map(P, Y)
lift_map(inc, f)
