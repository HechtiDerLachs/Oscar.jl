export AffineGroupRepresentation

export affine_group_scheme, reynolds_operator, set_reynolds_operator!

export canonical_representation, induced_representation_on_symmetric_power

export omega_process, nullcone_ideal, reynolds_operator_from_omega_process

@attributes mutable struct AffineGroupRepresentation{BRT<:Ring, BRET<:RingElem, 
                                                     GroupType<:AbsAffineGroupScheme, 
                                                     MatrixType<:MatrixElem
                                                    }
  G::GroupType
  M::MatrixType
  S::MPolyRing # the polynomial ring for the vector space
  R::Union{Hecke.Map, Nothing}

  function AffineGroupRepresentation(
      G::AbsAffineGroupScheme, M::MatrixElem; 
      reynolds_operator::Union{Hecke.Map, Nothing}=nothing,
      var_names::Vector{String}=["v$i" for i in 1:nrows(M)],
      check::Bool=true
    )
    R = base_ring(M)
    kk = ground_field(G)
    Mconv = map_entries(OO(G), M) # will complain if matrix is not compatible
    S, _ = PolynomialRing(kk, var_names)


    if check
      # check compatibility of group law with matrix multiplication, etc.
    end

    return new{typeof(kk), elem_type(kk), typeof(G), typeof(Mconv)}(G, Mconv, S, reynolds_operator)
  end
end

affine_group_scheme(rho::AffineGroupRepresentation) = rho.G
coordinate_matrix(rho::AffineGroupRepresentation) = rho.M
reynolds_operator(rho::AffineGroupRepresentation) = rho.R
vector_space_poly_ring(rho::AffineGroupRepresentation) = rho.S

function set_reynolds_operator!(rho::AffineGroupScheme, R::Hecke.Map)
  rho.R = R
  return rho
end

function (rho::AffineGroupRepresentation{<:Any, <:Any, <:AffineMatrixGroup, <:Any})(A::MatrixElem)
  a = coordinates(affine_group_scheme(rho), A)
  return map_entries(f->(evaluate(f, a)), G.M)
end

canonical_representation(G::AffineMatrixGroup) = AffineGroupRepresentation(G, coordinate_matrix(G))

function _linear_index_in_all_monomials(x::MPolyElem)
  d = total_degree(x)
  R = parent(x)
  length(coefficients(x)) == 1 || error("polynomial must be monomial")
  isone(first(coefficients(x))) || error("polynomial must be monomial")
  mons = Oscar.all_monomials(R, d)
  for (i, y) in zip(1:length(mons), mons)
    x == y && return i
  end
  error("monomial could not be found")
end

### Note: It would be nice if the user was given more control on the order 
# in which the monomials appear in the symmetric power of the original vector 
# space. By now, this is determined by the iterator Oscar.all_monomials, 
# but the whole construction should eventually be replaced by calls to 
# a function like `symmetric_power(V::VectorSpace)` and related mappings.
function induced_representation_on_symmetric_power(G::AffineMatrixGroup, p::Int)
  M = coordinate_matrix(G)
  m = ncols(M)
  kk = ground_field(G)
  S, v = PolynomialRing(kk, ["v$i" for i in 1:m])
  mons = Oscar.all_monomials(S, p)
  n = length(mons)
  
  R = base_ring(M)
  RS, _ = PolynomialRing(R, symbols(S))
  StoRS = hom(S, RS, gens(RS))

  MRS = map_entries(RS, M)
  V = MatrixSpace(RS, 1, m)([StoRS(v) for v in gens(S)])
  C = V*MRS
  D = [C[1, i] for i in 1:ncols(C)]

  A = zero(MatrixSpace(R, n, n)) # the matrix for the induced representation
  for y in mons
    p = evaluate(y, D)
    for (c, z) in zip(coefficients(p), monomials(p))
      A[_linear_index_in_all_monomials(y), _linear_index_in_all_monomials(z)] = c
    end
  end

  return AffineGroupRepresentation(G, A)
end

### 
# This function takes a multivariate polynomial ∑ₐ cₐ ⋅ xᵃ 
# and turns it into the differential operator 
#
#   D = ∑ₐ cₐ ⋅ (∂/∂ x₁)ᵃ¹ ⋯ (∂/∂ xₙ)ᵃⁿ
#
# where a = (a₁,…,aₙ) is a multiindex.
function as_constant_differential_operator(f::MPolyElem)
  R = parent(f)
  function p(g::MPolyElem)
    parent(g) == R || error("element belongs to the wrong ring")
    result = zero(g)
    for (c, e) in zip(coefficients(f), exponent_vectors(f))
      h = copy(g)
      for i in 1:ngens(R)
        for j in 1:e[i]
          h = derivative(h, i)
          iszero(h) && continue
        end
        iszero(h) && continue
      end
      result = result + c*h
    end
    return result
  end
  return MapFromFunc(p, R, R)
end

function omega_process(G::AffineMatrixGroup)
  return as_constant_differential_operator(det(coordinate_matrix(G)))
end

@attr MPolyIdeal function nullcone_ideal(
    rho::AffineGroupRepresentation{<:Any, <:Any, <:AffineGroupType, <:Any}
  ) where {
           AffineGroupType <: AffineMatrixGroup
          }

  # Prepare the coordinate matrix for Derksen's algorithm; 
  # it needs to be defined over an honest affine algebra.
  A = coordinate_matrix(rho)
  OOG = base_ring(A)
  R, I, f, phi, theta = as_affine_algebra(OOG)
  Q, pr = quo(R, I)
  OOGtoQ = hom(OOG, Q, gens(Q)[2:end], check=false)
  QtoOOG = hom(Q, OOG, vcat([inv(OOG(f))], gens(OOG)), check=false)
  A_lift = map_entries(x->lift(OOGtoQ(x)), A)

  # This code now follows [Derksen: Computation of Invariants 
  # for Reductive Groups, Advances in Mathematics 141, pp. 366--384,
  # 1999], Section 5.
  m = ncols(A)
  kk = coefficient_ring(R)
  Rext, _ = PolynomialRing(kk, vcat(symbols(R), Symbol.(["u$i" for i in 1:m]), Symbol.(["v$i" for i in 1:m])))
  z = gens(Rext)[1:ngens(R)]
  x = gens(Rext)[ngens(R)+1:ngens(R)+m]
  y = gens(Rext)[ngens(R)+m+1:ngens(R)+2*m]
  RtoRext = hom(R, Rext, z)
  M = map_entries(RtoRext, A_lift)
  X = MatrixSpace(Rext, 1, m)(x)
  Y = MatrixSpace(Rext, 1, m)(y)
  J = ideal(Rext, minors(Y - X*M, 1))
  J = J + ideal(Rext, RtoRext.(gens(I)))

  K = eliminate(J, z)
  
  S = vector_space_poly_ring(rho)
  v_ext = vcat([zero(S) for i in 1:ngens(R)], gens(S), [zero(S) for i in 1:m])
  return ideal(S, (x->(evaluate(x, v_ext))).(gens(K)))
end

function reynolds_operator_from_omega_process(
    rho::AffineGroupRepresentation{<:Any, <:Any, <:AffineGroupType, <:Any}
  ) where {
           AffineGroupType <: AffineMatrixGroup
          }
  G = affine_group_scheme(rho)
  A = coordinate_matrix(rho)
  M = coordinate_matrix(G)
  all(x->(isone(lifted_denominator(x))), A) || error("reynolds operator from omega process not implemented for non-polynomial representations")
  A_lift = map_entries(x->(lifted_numerator(x)), A)

  R = base_ring(M)
  m = ncols(M)
  kk = coefficient_ring(R)
  n = ncols(A_lift)
  S = vector_space_poly_ring(rho)
  RS, _ = PolynomialRing(kk, vcat(["t_$(i)_$(j)" for i in 1:m for j in 1:m], ["v$i" for i in 1:n]))
  t = gens(RS)[1:m^2]
  v = gens(RS)[m^2+1:end]
  RtoRS = hom(R, RS, t)
  T = map_entries(RtoRS, A_lift)
  V = MatrixSpace(RS, 1, n)(v)
  W = V*T
  w = [W[1, i] for i in 1:ncols(W)]
  det_T = det(T)
  Omega_t = as_constant_differential_operator(det(T))

  StoRS = hom(S, RS, v)

  function I_func(p::Int, q::Int, f::MPolyElem)
    parent(f) == S || error("polynomial does not belong to the correct ring")
    p > q && return zero(RS)
    h = det_T^q*evaluate(f, [W[1, i] for i in 1:ncols(W)])
    for i in 1:p
      h = Omega_t(h)
    end
    return h
  end

  function I_func(g::Int, f::MPolyElem) 
    return evaluate(I_func(g, 0, f), vcat([zero(S) for i in 1:ngens(R)], gens(S)))
  end
  @infiltrate

  o = lex(t)*lex(v)

  function reynolds(f::MPolyElem)
    parent(f) == S || error("polynomial does not belong to the correct ring")
    
  end

end
