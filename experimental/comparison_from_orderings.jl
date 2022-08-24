export leading_term_from_ordering, leading_coefficient_from_ordering, leading_exponent_vector_from_ordering, lt_from_ordering

function leading_term_from_ordering(o::MonomialOrdering)
  R = base_ring(o)
  S = singular_poly_ring(R, o)
  function func(f::MPolyElem)
    Sf = S(f)
    lt_f = Singular.leading_term(Sf)
    return R(lt_f)
  end
  return func
end

function leading_coefficient_from_ordering(o::MonomialOrdering)
  lt = leading_term_from_ordering(o)
  function func(f::MPolyElem)
    return first(coefficients(lt(f)))
  end
  return func
end

function leading_exponent_vector_from_ordering(o::MonomialOrdering)
  R = base_ring(o)
  S = singular_poly_ring(R, o)
  function func(f::MPolyElem)
    Sf = S(f)
    return Singular.leading_exponent_vector(Sf)
  end
  return func
end

function lt_from_ordering(o::MonomialOrdering)
  R = base_ring(o)
  S = singular_poly_ring(R, o)
  function func(f::MPolyElem, g::MPolyElem)
    Sf = S(f)
    Sg = S(g)
    return Sf < Sg
  end
  return func
end


