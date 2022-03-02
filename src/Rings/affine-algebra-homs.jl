export AlgebraHomomorphism, codomain, compose, domain, hom,
       IdentityAlgebraHomomorphism, kernel, preimage, AlgHom
        

###############################################################################
#
#   IdentityAlgebraHomomorphism
#
###############################################################################

struct IdAlgHom{T} <: AbstractAlgebra.Map{Ring, Ring,
         AbstractAlgebra.IdentityMap, IdAlgHom} where T <: Union{AbstractAlgebra.Ring, AbstractAlgebra.Field}

   domain::Union{MPolyRing, MPolyQuo}
   image::Vector{U} where U <: Union{MPolyElem, MPolyQuoElem}
   salghom::Singular.SIdAlgHom
   kernel::Union{MPolyIdeal, MPolyQuoIdeal}

   function IdAlgHom{T}(R::U) where U <: Union{MPolyRing{T}, MPolyQuo{T}} where T
      V = gens(R)
      Sx = Oscar.singular_ring(R)
      ty = typeof(base_ring(Sx))
      z = new(R, V, Singular.IdentityAlgebraHomomorphism(Sx), ideal(R, [zero(R)]))
      return z
   end
end

function IdentityAlgebraHomomorphism(R::U) where U <: Union{MPolyRing{T}, MPolyQuo{T}} where T
   return IdAlgHom{T}(R)
end

###############################################################################
#
#   I/O for Identity Algebra Homomorphisms
#
###############################################################################

function show(io::IO, M::Map(IdAlgHom))
   println(io, "Identity algebra homomorphism with")
   println(io, "")
   println(io, "domain: ", domain(M))
   println(io, "")
   println(io, "defining equations: ", M.image)
end

###############################################################################
#
#   Basic Operations with Identity Algebra Homomorphisms
#
###############################################################################

function map_poly(f::Map(IdAlgHom), p::U) where U <: Union{MPolyElem, MPolyQuoElem}
   @assert parent(p) == domain(f)
   return p
end

function (f::IdAlgHom)(p::U) where U <: Union{MPolyElem, MPolyQuoElem}
   return map_poly(f, p)
end

###############################################################################
#
#   Preimage and Kernel for Identity Algebra Homomorphisms
#
###############################################################################

function preimage(f::Map(IdAlgHom), I::U) where U <: Union{MPolyIdeal, MPolyQuoIdeal}
   @assert base_ring(I) == domain(f)
   return I
end

function kernel(f::Map(IdAlgHom))
   return f.kernel
end

###############################################################################
#
#   AlgebraHomomorphism
#
###############################################################################

mutable struct AlgHom{T} <: AbstractAlgebra.Map{Ring, Ring,
         AbstractAlgebra.SetMap, AlgHom} where T <: Union{AbstractAlgebra.Ring, AbstractAlgebra.Field}
   domain::Union{MPolyRing, MPolyQuo}
   codomain::Union{MPolyRing, MPolyQuo}
   image::Vector{U} where U <: Union{MPolyElem, MPolyQuoElem}
   map::MapFromFunc
   salghom::Singular.SAlgHom
   kernel::Union{MPolyIdeal, MPolyQuoIdeal}
   groebner_data::Tuple  # Stores data for groebner computation:
                       # Given F: K[y]/J --> K[x]/I, y_i |-> f_i,
                       # we store T = K[x, y] ,
                       # the canonical inclusion inc: K[x] --> T,
                       # the canonical projection pr: T --> K[x]/I,
                       # groebner_data for a dp(x)*dp(y) product ordering:
                       # the ideal generated by I and f_i-y_i in T with its respective groebner data
                       # and the data D of the division with remainder of the x_i w.r.t G.
   groebner_data_lex::Tuple # Stores data for groebner computation:
                       # Given F: K[y]/J --> K[x]/I, y_i |-> f_i,
                       # we store T = K[x, y] ,
                       # the canonical inclusion inc: K[x] --> T,
                       # the canonical projection pr: T --> K[x]/I,
                       # groebner_data for dp(x)*lex(y) product ordering:
                       # the ideal generated by I and f_i-y_i in T with its respective groebner data
                       # and the data D of the division with remainder of the x_i w.r.t G.

   function AlgHom{T}(D::MPolyRing{T}, C::W, V::Vector{X}) where {T, S <: MPolyElem{T},
   W <: Union{MPolyRing{T}, MPolyQuo{S}},
   X <: Union{S, MPolyQuoElem{S}}}
      
      if typeof(C) <: MPolyRing_dec
         all(ishomogeneous, V) || error("Array needs to contain homogeneous elements")
      end

      Dx = singular_ring(D)
      Cx = singular_ring(C)
      
      z = new(D, C, V, MapFromFunc(x->evaluate(x, V), D, C), Singular.AlgebraHomomorphism(Dx, Cx, Cx.(V)))
      return z
   end

   function AlgHom{T}(D::MPolyQuo{S}, C::W, V::Vector{X}) where {T, S <: MPolyElem{T},
   W <: Union{MPolyRing{T}, MPolyQuo{S}},
   X <: Union{S, MPolyQuoElem{S}}}

      if typeof(C) <: MPolyRing_dec
         all(ishomogeneous, V) || error("Array needs to contain homogeneous elements")
      end

      Dx = singular_ring(D)
      Cx = singular_ring(C)
      z = new(D, C, V, MapFromFunc(x->evaluate(x, V), base_ring(D), C), Singular.AlgebraHomomorphism(Dx, Cx, Cx.(V)))
      return z
   end

   function AlgHom{T}(D::MPolyRing_dec{T, MPolyRing{T}}, C::W, V::Vector{X}) where {T, S <: MPolyElem{T},
   W <: Union{MPolyRing{T}, MPolyQuo{S}},
   X <: Union{S, MPolyQuoElem{S}}}

      if typeof(C) <: MPolyRing_dec
         all(ishomogeneous, V) || error("Array needs to contain homogeneous elements")
      end

      Dx = singular_ring(D)
      Cx = singular_ring(C)
      z = new(D, C, V, MapFromFunc(x->evaluate(x, V), D.R, C), Singular.AlgebraHomomorphism(Dx, Cx, Cx.(V)))
      return z
   end
end

###############################################################################
#
#   I/O for Algebra Homomorphisms
#
###############################################################################

function show(io::IO, M::Map(AlgHom))
   println(io, "Algebra homomorphism with")
   println(io, "")
   println(io, "domain: ", domain(M))
   println(io, "")
   println(io, "codomain: ", codomain(M))
   println(io, "")
   println(io, "defining images of generators: ", M.image)
end

###############################################################################
#
#   Algebra Homomorphism constructor
#
###############################################################################

@doc Markdown.doc"""
    AlgebraHomomorphism(D::U, C::W, V::Vector{X}) where 
    {T, S <: MPolyElem{T},
    U <: Union{MPolyRing{T}, MPolyQuo{S}},
    W <: Union{MPolyRing{T}, MPolyQuo{S}},
    X <: Union{S, MPolyQuoElem{S}}}
   
Create the algebra homomorphism $D \rightarrow C$ defined by sending the $i$th generator of $D$ to the $i$th element of $V$. 
Allow types `MPolyRing` and `MPolyQuo` for $C$ and $D$ as well as entries of type `MPolyElem` and `MPolyQuoElem` for `X`.
Alternatively, use `hom(D::U, C::W, V::Vector{X})`.

# Examples
```jldoctest
julia> D, (t,) = PolynomialRing(QQ, ["t"])
(Multivariate Polynomial Ring in t over Rational Field, fmpq_mpoly[t])

julia> R, (x, y) = PolynomialRing(QQ, ["x", "y"])
(Multivariate Polynomial Ring in x, y over Rational Field, fmpq_mpoly[x, y])

julia> C, p = quo(R,  ideal(R, [x*y-1]))
(Quotient of Multivariate Polynomial Ring in x, y over Rational Field by ideal(x*y - 1), Map from
Multivariate Polynomial Ring in x, y over Rational Field to Quotient of Multivariate Polynomial Ring in x, y over Rational Field by ideal(x*y - 1) defined by a julia-function with inverse)

julia> V = [p(y)]
1-element Vector{MPolyQuoElem{fmpq_mpoly}}:
 y

julia> P = hom(D, C, V)
Map with following data
Domain:
=======
Multivariate Polynomial Ring in t over Rational Field
Codomain:
=========
Quotient of Multivariate Polynomial Ring in x, y over Rational Field by ideal(x*y - 1)
```
"""
function AlgebraHomomorphism(D::U, C::W, V::Vector{X}) where 
    {T, S <: MPolyElem{T},
    U <: Union{MPolyRing{T}, MPolyQuo{S}},
    W <: Union{MPolyRing{T}, MPolyQuo{S}},
    X <: Union{S, MPolyQuoElem{S}}}
   n = length(V)
   @assert n == ngens(D)
   return AlgHom{T}(D, C, copy(V))
end

#hom(D::U, C::W, V::Vector{X}) where {T, S <: MPolyElem{T},
#   U <: Union{MPolyRing{T}, MPolyQuo{S}}, W <: Union{MPolyRing{T}, MPolyQuo{S}},
#   X <: Union{S, MPolyQuoElem{S}}} = AlgebraHomomorphism(D, C, V)

###############################################################################
#
#   Basic Operations with Algebra Homomorphisms
#
###############################################################################

function map_poly(F::Map(AlgHom), p::MPolyElem)
   @assert parent(p) == domain(F)
   return F.map(p)
end

function map_poly(F::Map(AlgHom), p::Union{MPolyQuoElem, MPolyElem_dec})
   @assert parent(p) == domain(F)
   return F.map(p.f)
end

function (F::AlgHom)(p::U) where U <: Union{MPolyElem, MPolyQuoElem}
   return map_poly(F, p)
end

function domain(F::AlgHom)
   return F.domain
end

function codomain(F::AlgHom)
   return F.codomain
end

###############################################################################
#
#   Composition of Algebra Homomorphisms
#
###############################################################################

@doc Markdown.doc"""
    compose(F::AlgHom{T}, G::AlgHom{T}) where T

Return the algebra homomorphism $H = G\circ F: \text{domain}(F) \rightarrow \text{codomain}(G)$.
"""
function compose(F::AlgHom{T}, G::AlgHom{T}) where T
   check_composable(F, G)
   D = domain(F)
   C = codomain(G)
   V = G.(F.image)
   return AlgHom{T}(D, C, V)
end

###############################################################################
#
#   Preimage and Kernel for Algebra Homomorphisms
#
###############################################################################

@doc Markdown.doc"""
    preimage(F::AlgHom, I::U) where U <: Union{MPolyIdeal, MPolyQuoIdeal}

Return the preimage of the ideal `I` under the algebra homomorphism `F`.
"""
function preimage(F::AlgHom, I::U) where U <: Union{MPolyIdeal, MPolyQuoIdeal}

   @assert base_ring(I) == codomain(F)
   D = domain(F)
   C = codomain(F)
   Cx = codomain(F.salghom)
   V = gens(I)
   Ix = Singular.Ideal(Cx, Cx.(V))
   prIx = Singular.preimage(F.salghom, Ix)
   return ideal(D, D.(gens(prIx)))
end

@doc Markdown.doc"""
    kernel(F::AlgHom)

Return the kernel of `F`.
"""
function kernel(F::AlgHom)
   isdefined(F, :kernel) && return F.kernel
   C = codomain(F)
   F.kernel = preimage(F, ideal(C, [zero(C)]))
   return F.kernel
end
