  # Advice for the programmer

  ## How to implement my custom double complex?
The implementation for Double complexes is generically lazy. We provide 
a concrete type which takes care of handling the user's requests 
to entries and morphisms and their caching: `DoubleComplexOfMorphisms`. 

In order to work properly, any `DoubleComplex` `D` needs to be able to produce
entries `D[i, j]` for legitimate indices `(i, j)` and the morphisms between 
these on request. To this end, the internal constructor of `DoubleComplex` 
requires the programmer to pass on certain "factories". For the production 
of the entries `D[i, j]`, these must be concrete instances of 
```julia 
    abstract type ChainFactory{ChainType} end
```
For this type the call syntax must be overwritten as follows:
```julia
    function (fac::ChainFactory{ChainType})(D::AbsDoubleComplexOfMorphisms, i::Int, j::Int)::ChainType where {ChainType}
```
This will be called by the internals of `DoubleComplex` whenever production of the `(i, j)`-th 
entry is requested. The first argument will then always be the concrete double complex `D` itself, 
so that the factory has access to all information that has already been computed when trying 
to compute the entry for `(i, j)`. Beware not to produce infinite feedback loops when implementing this!

Let's see this in an example. Suppose we want to implement the "zero double complex of modules" 
over a multivariate polynomial ring `R`, i.e. the unbounded double complex which consists 
entirely of zero modules and the trivial homomorphisms between them. Then the factory would be 
```julia
mutable struct ZeroModuleFactory{ChainType} <: ChainFactory{ChainType}
  R::MPolyRing
  
  function ZeroModuleFactory(R::MPolyRing)
    return new{ModuleFP{elem_type(R)}}(R)
  end
end

function (fac::ZeroModuleFactory)(D::AbsDoubleComplexOfMorphisms, i::Int, j::Int)
  return FreeMod(fac.R, 0)
end
```

The horizontal and vertical morphisms also need their factories. Similar to the above, these 
need to be concrete instances of 
```julia
    abstract type ChainMorphismFactory{MorphismType} end
```
and the programmer must overwrite 
```julia
    function (fac::ChainMorphismFactory{MorphismType})(dc::AbsDoubleComplexOfMorphisms, i::Int, j::Int)::MorphismType where {MorphismType}
```
In the above example we would implement
```julia
mutable struct VerticalZeroMaps{MorphismType} <: ChainMorphismFactory{MorphismType}
  R::MPolyRing

  function VerticalZeroMaps(R::MPolyRing)
    return new{ModuleFPHom}(R)
  end
end

mutable struct HorizontalZeroMaps{MorphismType} <: ChainMorphismFactory{MorphismType}
  R::MPolyRing

  function HorizontalZeroMaps(R::MPolyRing)
    return new{ModuleFPHom}(R)
  end
end
```
Then we would overwrite the call syntax as follows.
```julia
function (fac::VerticalZeroMaps)(D::AbsDoubleComplexOfMorphisms, i::Int, j::Int)
   dom = D[i, j]
   inc = (vertical_typ(D) == :chain ? -1 : 1)
   cod = D[i, j + inc]
   return hom(dom, cod, elem_type(cod)[])
end

function (fac::HorizontalZeroMaps)(D::AbsDoubleComplexOfMorphisms, i::Int, j::Int)
   dom = D[i, j]
   inc = (horizontal_typ(D) == :chain ? -1 : 1)
   cod = D[i + inc, j]
   return hom(dom, cod, elem_type(cod)[])
end
```

In order to finally create our zero double complex we implement the constructor as 
follows.
```julia
function zero_double_complex(R::MPolyRing)
  entry_fac = ZeroModuleFactory(R)
  vert_map_fac = VerticalZeroMaps(R)
  horz_map_fac = HorizontalZeroMaps(R)
  
  result = DoubleComplexOfMorphisms(entry_fac, horz_map_fac, vert_map_fac, horizontal_typ=:chain, vertical_typ=:chain)
  return result
end
```
Note that any concrete complex `Z` created by `zero_double_complex` is unbounded in every direction. 
In particular, `has_upper_bound(Z)` etc. will 
return `false` and `upper_bound(Z)` will throw an error. At the same time 
`extends_right(Z)` and friends will return `true`, indicating that indeed any request `Z[i, j]` is 
legitimate and will produce a reasonable and cached result.
See the source code of the internal 
constructor of `DoubleComplex` for how to alter these settings.

Another example for an implementation of a double complex can be 
found in `experimental/DoubleComplexes/test/double_complex_interface.jl`. 
There we write an implementation to turn a bounded simple 
`ComplexOfMorphisms` for modules over polynomial rings `C` 
into a bounded `DoubleComplexOfMorphisms` `D` which knows how to extend itself 
with zeroes to the left and to the right, but is concentrated in the zeroeth row.


## How to make use of the generic functionality?

For double complexes we have some generic functionality available, e.g. 
`total_complex(D::AbsDoubleComplexOfMorphisms{ChainType, MorphismType})`. 
This generic functionality assumes certain methods to be implemented for the 
`ChainType` and the `MorphismType` of the double complex `D`. For instance, 
it must be possible to compose two morphisms of type `<:MorphismType` and 
get a new object of type `<:MorphismType`. Sometimes, the required functionality 
is not streamlined throughout OSCAR (and there is little hope to achieve this).
One example for this are direct sums: For finitely generated modules, the 
function takes a special keyword argument `task` to indicate whether the inclusion 
and projection maps should also be returned, while for `TorQuadModule`s, this keyword argument 
is not even available. To potentially accomodate all these different types in our 
double complexes, the generic code uses an internal method
```@docs
    _direct_sum(u::Vector{T}) where {T}
```
If forming a total complex does not work for your custom implementation of a double 
complex, check whether this might be due to a missing implementation of this method or others.
    