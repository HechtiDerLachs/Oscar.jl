export AbsAffineGroupScheme
export multiplication_map, product_over_ground_field, inverse_map, first_inclusion, second_inclusion, diagonal_embedding, first_projection, second_projection

abstract type AbsAffineGroupScheme{BRT, BRET} <: AbsSpec{BRT, BRET} end

@Markdown.doc """
    multiplication_map(G::AbsAffineGroupScheme)

Returns a morphism of affine schemes `G × G → G` 
where `G × G` is the `product_over_ground_field` of `G`.
"""
function multiplication_map(G::AbsAffineGroupScheme)
  return multiplication_map(underlying_group_scheme(G))
end

@Markdown.doc """
    product_over_ground_field(G::AbsAffineGroupScheme)

Returns the fiber product `G × G` over the ground field 𝕜 of `G`, 
together with its two canonical projections. 
"""
function product_over_ground_field(G::AbsAffineGroupScheme)
  return product_over_ground_field(underlying_group_scheme(G))
end

@Markdown.doc """
    first_projection(G::AbsAffineGroupScheme)

For a group scheme ``G`` this returns the projection ``G × G → G, (g, h) ↦ g`` 
where ``G×G`` is the `product_over_ground_field` of ``G``.
"""
function first_projection(G::AbsAffineGroupScheme)
  return first_projection(underlying_group_scheme(G))
end

@Markdown.doc """
    second_projection(G::AbsAffineGroupScheme)

For a group scheme ``G`` this returns the projection ``G × G → G, (g, h) ↦ h`` 
where ``G×G`` is the `product_over_ground_field` of ``G``.
"""
function second_projection(G::AbsAffineGroupScheme)
  return second_projection(underlying_group_scheme(G))
end

@Markdown.doc """
   inverse_map(G::AbsAffineGroupScheme)

Returns the map `G → G` assigning to each point ``g ∈ G`` its inverse 
``g⁻¹`` with respect to the group law on ``G``.
"""
function inverse_map(G::AbsAffineGroupScheme)
  return inverse_map(underlying_group_scheme(G))
end

@Markdown.doc """
    first_inclusion(G::AbsAffineGroupScheme)

For a group ``G`` with neutral element ``e ∈ G`` this returns the morphism 
``G → G × G, g ↦ (g, e)`` where ``G × G`` is the `product_over_ground_field` of ``G``.
"""
function first_inclusion(G::AbsAffineGroupScheme)
  return first_inclusion(underlying_group_scheme(G))
end

@Markdown.doc """
    second_inclusion(G::AbsAffineGroupScheme)

For a group ``G`` with neutral element ``e ∈ G`` this returns the morphism 
``G → G × G, g ↦ (e, g)`` where ``G × G`` is the `product_over_ground_field` of ``G``.
"""
function second_inclusion(G::AbsAffineGroupScheme)
  return second_inclusion(underlying_group_scheme(G))
end

@Markdown.doc """
    diagonal_embedding(G::AbsAffineGroupScheme)

For a group ``G`` this returns the morphism ``G → G × G, g ↦ (g, g)`` 
where ``G × G`` is the `product_over_ground_field` of ``G``.
"""
function diagonal_embedding(G::AbsAffineGroupScheme)
  return diagonal_embedding(underlying_group_scheme(G))
end

function underlying_group_scheme(G::AbsAffineGroupScheme)
  error("function `underlying_group_scheme` not implemented for schemes of type $(typeof(G))")
end


@attributes mutable struct AffineGroupScheme{BRT, BRET} <: AbsAffineGroupScheme{BRT, BRET}
  X::Spec
  product_over_ground_field::AbsSpec
  diagonal_embedding::SpecMor
  first_projection::SpecMor
  second_projection::SpecMor
  first_inclusion::SpecMor
  second_inclusion::SpecMor
  multiplication_map::SpecMor
  inverse_map::SpecMor
  neutral_element::Vector{BRET}

  function AffineGroupScheme(
      X::AbsSpec, XxX::AbsSpec, 
      diag::SpecMor,
      p1::SpecMor, p2::SpecMor, 
      i1::SpecMor, i2::SpecMor, 
      mult_map::SpecMor, inv::SpecMor, 
      neutral_element::Vector{T};
      check::Bool=true
    ) where {T<:FieldElem}
    typeof(ground_field(X)) === BRT || error("scheme is not defined over a field of the correct type")
    elem_type(ground_field(X)) === BRET || error("scheme is not defined over a field of the correct type")
    all(x->(parent(x) == ground_field(X)), neutral_element) || error("coordinates of the neutral element do not belong to the correct field")
    domain(p1) == XxX || error("domain of first projection not compatible")
    domain(p2) == XxX || error("domain of second projection not compatible")
    codomain(p1) == X || error("codomain of first projection not compatible")
    codomain(p2) == X || error("codomain of second projection not compatible")
    domain(diag) == X || error("domain of diagonal embedding is not compatible")
    codomain(diag) == XxX || error("codomain of diagonal embedding is not compatible")
    domain(i1) == X || error("domain of first inclusion not compatible")
    domain(i2) == X || error("domain of second inclusion not compatible")
    codomain(i1) == XxX || error("codomain of first inclusion not compatible")
    codomain(i2) == XxX || error("codomain of second inclusion not compatible")
    domain(inv) == codomain(inv) == X || error("domain or codomain of the inverse map is not compatible")

    if check
      is_identity_map(compose(i1, p1)) || error("composition of the first inclusion and projection is not the identity")
      is_identity_map(compose(i2, p2)) || error("composition of the second inclusion and projection is not the identity")
      is_isomorphism(inv) || error("the inverse map is not an isomorphism")
      is_identity_map(compose(inv, inv)) || error("the composition of the inverse map with itself is not the identity")
      is_identity_map(compose(diag, p2)) || error("composition of the diagonal embedding and the second projection is not the identity")
      is_identity_map(compose(diag, p1)) || error("composition of the diagonal embedding and the first projection is not the identity")
      is_identity_map(compose(i1, mult_map)) || error("composition of the first inclusion and the multiplication map is not the identity")
      is_identity_map(compose(i2, mult_map)) || error("composition of the second inclusion and the multiplication map is not the identity")
      # TODO: Add some further checks about the neutral element.
    end

    return new{base_ring_type(X), elem_type(base_ring_type(X))}(X, XxX, diag, p1, p2, i1, i2, mult_map, inv, neutral_element)
  end
end

product_over_ground_field(G::AffineGroupScheme) = G.product_over_ground_field
diagonal_embedding(G::AffineGroupScheme) = G.diagonal_embedding
first_projection(G::AffineGroupScheme) = G.first_projection
second_projection(G::AffineGroupScheme) = G.second_projection
first_inclusion(G::AffineGroupScheme) = G.first_inclusion
second_inclusion(G::AffineGroupScheme) = G.second_inclusion
multiplication_map(G::AffineGroupScheme) = G.multiplication_map
inverse_map(G::AffineGroupScheme) = G.inverse_map
neutral_element(G::AffineGroupScheme) = G.neutral_element
