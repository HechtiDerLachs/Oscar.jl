export AffineMatrixGroup
using Infiltrator

@attributes mutable struct AffineMatrixGroup{BRT, BRET, 
                                       SpecType<:AbsAffineGroupScheme, 
                                       MatrixType<:MatrixElem
                                      } <: AbsAffineGroupScheme{BRT, BRET}
  G::SpecType # the underlying group scheme
  M::MatrixType# the coordinate matrix
  
  function AffineMatrixGroup(M::MatrixElem{T}, I::MPolyIdeal{T}, e::Vector{BRET}; 
      check::Bool=true
    ) where {T<:MPolyElem, BRET<:FieldElem}

    R = base_ring(M)
    m = ncols(M)
    m == nrows(M) || error("coordinate matrix is not square")
    R == base_ring(I) || error("matrix and ideal are not defined over the same ring")
    kk = coefficient_ring(R)
    all(x->(parent(x) == kk), e) || error("coordinates of the neutral element do not belong to the correct field")

    f = det(M)
    X = Spec(R, I, MPolyPowersOfElement(R, [f]))
    XxX, p1, p2 = product(X, X, change_var_names_to=["y", "z"])

    pb_diag = hom(OO(XxX), OO(X), vcat(gens(R), gens(R)))
    diag = SpecMor(X, XxX, pb_diag)

    pb_i1 = hom(OO(XxX), OO(X), vcat(gens(R), R.(e)))
    i1 = SpecMor(X, XxX, pb_i1)

    pb_i2 = hom(OO(XxX), OO(X), vcat(R.(e), gens(R)))
    i2 = SpecMor(X, XxX, pb_i2)

    S, _ = PolynomialRing(kk, ["a$i$j" for i in 1:m for j in 1:m])
    Mat = Spec(S)

    A = map_entries(pullback(p1), M)
    B = map_entries(pullback(p2), M)
    C = A*B
    pb_pre_prod = hom(OO(Mat), OO(XxX), [C[i,j] for i in 1:m for j in 1:m])
    pre_prod = SpecMor(XxX, Mat, pb_pre_prod)

    pb_inc = hom(OO(Mat), OO(X), [M[i,j] for i in 1:m for j in 1:m])
    inc = SpecMor(X, Mat, pb_inc)

    prod_map = lift_map(pre_prod, inc)

    ### assemble the multiplication map.
    # This requires setting up some help ring to represent the 
    # multiplication of two matrices in the sub-algebra determined 
    # by M.
    help_ring, _ = PolynomialRing(kk, vcat(symbols(base_ring(OO(XxX))),
                                        Symbol.(["a$i$j" for i in 1:m for j in 1:m]), 
                                        symbols(R))
                              )
    x = gens(help_ring)[1:ngens(R)]
    y = gens(help_ring)[ngens(R)+1: 2*ngens(R)]
    a = gens(help_ring)[2*ngens(R)+1: 2*ngens(R)+m^2]
    z = gens(help_ring)[2*ngens(R)+m^2+1:end]
    pb1 = hom(R, help_ring, x)
    pb2 = hom(R, help_ring, y)
    pb3 = hom(R, help_ring, z)
    Gamma = ideal(help_ring, [c-pb3(M[i,j]) for (c, (i,j)) in zip(a, [(i,j) for i in 1:m for j in 1:m])])
    A = map_entries(pb1, M)
    B = map_entries(pb2, M)
    C = A*B
    D = zero(C)
    for i in 1:m
      for j in 1:m
        D[i, j] = a[(i-1)*m+j]
      end
    end
    Gamma = Gamma + ideal(help_ring, minors(D-C, 1))
    o = degrevlex(vcat(x, y))*degrevlex(a)*degrevlex(z)
    gb = groebner_basis(Gamma, ordering=o)
    @infiltrate
    #return new{typeof(kk), elem_type(kk), typeof(X), typeof(M)}(
  end
end
