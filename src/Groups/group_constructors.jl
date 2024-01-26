################################################################################
#
#  Some basic constructors
#
################################################################################

_gap_filter(::Type{PermGroup}) = GAP.Globals.IsPermGroup
_gap_filter(::Type{PcGroup}) = GAP.Globals.IsPcGroupOrPcpGroup
_gap_filter(::Type{FPGroup}) = GAP.Globals.IsSubgroupFpGroup

# TODO: matrix group handling usually is more complex: there usually
# is another extra argument then to specify the base field
# `_gap_filter(::Type{MatrixGroup})` is on the file `matrices/MatGrp.jl`

"""
    symmetric_group(n::Int)

Return the full symmetric group on the set `{1, 2, ..., n}`.

# Examples
```jldoctest
julia> G = symmetric_group(5)
Sym(5)

julia> order(G)
120

```
"""
function symmetric_group(n::Int)
  @req n >= 1 "n must be a positive integer"
  return PermGroup(GAP.Globals.SymmetricGroup(n)::GapObj)
end

"""
    is_natural_symmetric_group(G::GAPGroup)

Return `true` if `G` is a permutation group acting as the symmetric group
on its moved points, and `false` otherwise.
"""
@gapattribute is_natural_symmetric_group(G::GAPGroup) = GAP.Globals.IsNaturalSymmetricGroup(G.X)::Bool

"""
    is_isomorphic_to_symmetric_group(G::GAPGroup)

Return `true` if `G` is isomorphic to a symmetric group,
and `false` otherwise.
"""
@gapattribute is_isomorphic_to_symmetric_group(G::GAPGroup) = GAP.Globals.IsSymmetricGroup(G.X)::Bool

"""
    alternating_group(n::Int)

Return the full alternating group on the set `{1, 2, ..., n}`..

# Examples
```jldoctest
julia> G = alternating_group(5)
Alt(5)

julia> order(G)
60

```
"""
function alternating_group(n::Int)
  @req n >= 1 "n must be a positive integer"
  return PermGroup(GAP.Globals.AlternatingGroup(n)::GapObj)
end

"""
    is_natural_alternating_group(G::GAPGroup)

Return `true` if `G` is a permutation group acting as the alternating group
on its moved points, and `false` otherwise.
"""
@gapattribute is_natural_alternating_group(G::GAPGroup) = GAP.Globals.IsNaturalAlternatingGroup(G.X)::Bool

"""
    is_isomorphic_to_alternating_group(G::GAPGroup)

Return `true` if `G` is isomorphic to an alternating group,
and `false` otherwise.
"""
@gapattribute is_isomorphic_to_alternating_group(G::GAPGroup) = GAP.Globals.IsAlternatingGroup(G.X)::Bool

"""
    cyclic_group(::Type{T} = PcGroup, n::IntegerUnion)
    cyclic_group(::Type{T} = PcGroup, n::PosInf)

Return the cyclic group of order `n`, as an instance of type `T`.

# Examples
```jldoctest
julia> G = cyclic_group(5)
Pc group of order 5

julia> G = cyclic_group(PermGroup, 5)
Permutation group of degree 5 and order 5

julia> G = cyclic_group(PosInf())
Pc group of infinite order

```
"""
cyclic_group(n::Union{IntegerUnion,PosInf}) = cyclic_group(PcGroup, n)

function cyclic_group(::Type{T}, n::Union{IntegerUnion,PosInf}) where T <: GAPGroup
  @req n > 0 "n must be a positive integer or infinity"
  return T(GAP.Globals.CyclicGroup(_gap_filter(T), GAP.Obj(n))::GapObj)
end

function cyclic_group(::Type{PcGroup}, n::Union{IntegerUnion,PosInf})
  if is_infinite(n)
    return PcGroup(GAP.Globals.AbelianPcpGroup(1, GAP.GapObj([])))
  elseif n > 0
    return PcGroup(GAP.Globals.CyclicGroup(GAP.Globals.IsPcGroup, GAP.Obj(n))::GapObj)
  end
  throw(ArgumentError("n must be a positive even integer or infinity"))
end

"""
    is_cyclic(G::GAPGroup)

Return `true` if `G` is cyclic,
i.e., if `G` can be generated by one element.
"""
@gapattribute is_cyclic(G::GAPGroup) = GAP.Globals.IsCyclic(G.X)::Bool

"""
    cyclic_generator(G::GAPGroup)

Return an element of `G` that generates `G` if `G` is cyclic,
and throw an error otherwise.

# Examples
```jldoctest
julia> g = permutation_group(5, [cperm(1:3), cperm(4:5)])
Permutation group of degree 5

julia> cyclic_generator(g)
(1,2,3)(4,5)
```
"""
function cyclic_generator(G::GAPGroup)
  @req is_cyclic(G) "the group is not cyclic"
  ngens(G) == 1 && return gen(G,1)
  is_finite(G) && order(G) == 1 && return one(G)
  return group_element(G, GAPWrap.MinimalGeneratingSet(G.X)[1])
end

# already defined in Hecke
#=
function abelian_group(v::Vector{Int})
  for i = 1:length(v)
    iszero(v[i]) && error("Cannot represent an infinite group as a polycyclic group")
  end
  v1 = GAP.Obj(v)
  return PcGroup(GAP.Globals.AbelianGroup(v1))
end
=#

@doc raw"""
    abelian_group(::Type{T}, v::Vector{Int}) where T <: Group -> PcGroup

Return the direct product of cyclic groups of the orders
`v[1]`, `v[2]`, $\ldots$, `v[n]`, as an instance of `T`.
Here, `T` must be one of `PermGroup`, `FPGroup`, or `PcGroup`.

!!! warning
    The type need to be specified in the input of the function `abelian_group`,
    otherwise a group of type `GrpAbFinGen` is returned,
    which is not a GAP group type.
    In future versions of Oscar, this may change.
"""
function abelian_group(::Type{T}, v::Vector{S}) where T <: GAPGroup where S <: IntegerUnion
  vgap = GAP.Obj(v, recursive=true)
  return T(GAP.Globals.AbelianGroup(_gap_filter(T), vgap)::GapObj)
end

# Delegating to the GAP constructor via `_gap_filter` does not work here.
function abelian_group(::Type{PcGroup}, v::Vector{T}) where T <: IntegerUnion
  if 0 in v
    return PcGroup(GAP.Globals.AbelianPcpGroup(length(v), GAP.GapObj(v, recursive=true)))
  else
    return PcGroup(GAP.Globals.AbelianGroup(GAP.Globals.IsPcGroup, GAP.GapObj(v, recursive=true)))
  end
end

@doc raw"""
    is_abelian(G::Group)

Return `true` if `G` is abelian (commutative),
that is, $x*y = y*x$ holds for all elements $x, y$ in `G`.
"""
@gapattribute is_abelian(G::GAPGroup) = GAP.Globals.IsAbelian(G.X)::Bool

@doc raw"""
    is_elementary_abelian(G::Group)

Return `true` if `G` is a abelian (see [`is_abelian`](@ref))
and if there is a prime `p` such that the order of each element in `G`
divides `p`.

# Examples
```jldoctest
julia> g = alternating_group(5);

julia> is_elementary_abelian(sylow_subgroup(g, 2)[1])
true

julia> g = alternating_group(6);

julia> is_elementary_abelian(sylow_subgroup(g, 2)[1])
false
```
"""
@gapattribute is_elementary_abelian(G::GAPGroup) = GAP.Globals.IsElementaryAbelian(G.X)::Bool

function mathieu_group(n::Int)
  @req 9 <= n <= 12 || 21 <= n <= 24 "n must be a 9-12 or 21-24"
  return PermGroup(GAP.Globals.MathieuGroup(n), n)
end


################################################################################
#
#  Projective groups obtained from classical groups
#
################################################################################

@doc raw"""
    projective_general_linear_group(n::Int, q::Int)

Return the factor group of [`general_linear_group`](@ref),
called with the same parameters,
by its scalar matrices.
The group is represented as a permutation group.

# Examples
```jldoctest
julia> g = projective_general_linear_group(2, 3)
Permutation group of degree 4 and order 24

julia> order(g)
24
```
"""
function projective_general_linear_group(n::Int, q::Int)
   @req is_prime_power_with_data(q)[1] "The field size must be a prime power"
   return PermGroup(GAP.Globals.PGL(n, q))
end


@doc raw"""
    projective_special_linear_group(n::Int, q::Int)

Return the factor group of [`special_linear_group`](@ref),
called with the same parameters,
by its scalar matrices.
The group is represented as a permutation group.

# Examples
```jldoctest
julia> g = projective_special_linear_group(2, 3)
Permutation group of degree 4 and order 12

julia> order(g)
12
```
"""
function projective_special_linear_group(n::Int, q::Int)
   @req is_prime_power_with_data(q)[1] "The field size must be a prime power"
   return PermGroup(GAP.Globals.PSL(n, q))
end


@doc raw"""
    projective_symplectic_group(n::Int, q::Int)

Return the factor group of [`symplectic_group`](@ref),
called with the same parameters,
by its scalar matrices.
The group is represented as a permutation group.

# Examples
```jldoctest
julia> g = projective_symplectic_group(2, 3)
Permutation group of degree 4 and order 12

julia> order(g)
12
```
"""
function projective_symplectic_group(n::Int, q::Int)
   @req is_prime_power_with_data(q)[1] "The field size must be a prime power"
   @req iseven(n) "The dimension must be even"
   return PermGroup(GAP.Globals.PSp(n, q))
end


@doc raw"""
    projective_unitary_group(n::Int, q::Int)

Return the factor group of [`unitary_group`](@ref),
called with the same parameters,
by its scalar matrices.
The group is represented as a permutation group.

# Examples
```jldoctest
julia> g = projective_unitary_group(2, 3)
Permutation group of degree 10 and order 24

julia> order(g)
24
```
"""
function projective_unitary_group(n::Int, q::Int)
   @req is_prime_power_with_data(q)[1] "The field size must be a prime power"
   return PermGroup(GAP.Globals.PGU(n, q))
end


@doc raw"""
    projective_special_unitary_group(n::Int, q::Int)

Return the factor group of [`special_unitary_group`](@ref),
called with the same parameters,
by its scalar matrices.
The group is represented as a permutation group.

# Examples
```jldoctest
julia> g = projective_special_unitary_group(2, 3)
Permutation group of degree 10 and order 12

julia> order(g)
12
```
"""
function projective_special_unitary_group(n::Int, q::Int)
   @req is_prime_power_with_data(q)[1] "The field size must be a prime power"
   return PermGroup(GAP.Globals.PSU(n, q))
end


"""
    projective_orthogonal_group(e::Int, n::Int, q::Int)

Return the factor group of [`orthogonal_group`](@ref),
called with the same parameters,
by its scalar matrices.

As for `orthogonal_group`, `e` can be omitted if `n` is odd.

# Examples
```jldoctest
julia> g = projective_orthogonal_group(1, 4, 3);  order(g)
576

julia> g = projective_orthogonal_group(3, 3);  order(g)
24
```
"""
function projective_orthogonal_group(e::Int, n::Int, q::Int)
   @req is_prime_power_with_data(q)[1] "The field size must be a prime power"
   if e == 1 || e == -1
      @req iseven(n) "The dimension must be even"
   elseif e == 0
      @req isodd(n) "The dimension must be odd"
   else
      throw(ArgumentError("Invalid description of projective orthogonal group"))
   end
   return PermGroup(GAP.Globals.PGO(e, n, q))
end

projective_orthogonal_group(n::Int, q::Int) = projective_orthogonal_group(0, n, q)


"""
    projective_special_orthogonal_group(e::Int, n::Int, q::Int)

Return the factor group of [`special_orthogonal_group`](@ref),
called with the same parameters,
by its scalar matrices.

As for `special_orthogonal_group`, `e` can be omitted if `n` is odd.

# Examples
```jldoctest
julia> g = projective_special_orthogonal_group(1, 4, 3);  order(g)
288

julia> g = projective_special_orthogonal_group(3, 3);  order(g)
24
```
"""
function projective_special_orthogonal_group(e::Int, n::Int, q::Int)
   @req is_prime_power_with_data(q)[1] "The field size must be a prime power"
   if e == 1 || e == -1
      @req iseven(n) "The dimension must be even"
   elseif e == 0
      @req isodd(n) "The dimension must be odd"
   else
      throw(ArgumentError("Invalid description of projective special orthogonal group"))
   end
   return PermGroup(GAP.Globals.PSO(e, n, q))
end

projective_special_orthogonal_group(n::Int, q::Int) = projective_special_orthogonal_group(0, n, q)


"""
    projective_omega_group(e::Int, n::Int, q::Int)

Return the factor group of [`omega_group`](@ref),
called with the same parameters,
by its scalar matrices.

As for `omega_group`, `e` can be omitted if `n` is odd.

# Examples
```jldoctest
julia> g = projective_omega_group(1, 4, 3);  order(g)
144

julia> g = projective_omega_group(3, 3);  order(g)
12
```
"""
function projective_omega_group(e::Int, n::Int, q::Int)
   @req is_prime_power_with_data(q)[1] "The field size must be a prime power"
   if e == 1 || e == -1
      @req iseven(n) "The dimension must be even"
   elseif e == 0
      @req isodd(n) "The dimension must be odd"
   else
      throw(ArgumentError("Invalid description of projective orthogonal group"))
   end
   return PermGroup(GAP.Globals.POmega(e, n, q))
end

projective_omega_group(n::Int, q::Int) = projective_omega_group(0, n, q)


################################################################################
#
# begin FpGroups
#
################################################################################

"""
    free_group(n::Int, s::VarName = :f; eltype::Symbol = :letter) -> FPGroup
    free_group(L::Vector{<:VarName}) -> FPGroup
    free_group(L::VarName...) -> FPGroup

The first form returns the free group of rank `n`, where the generators are
printed as `s1`, `s2`, ..., the default being `f1`, `f2`, ...
If `eltype` has the value `:syllable` then each element in the free group is
internally represented by a vector of syllables,
whereas a representation by a vector of integers is chosen in the default case
of `eltype == :letter`.

The second form, if `L` has length `n`, returns the free group of rank `n`,
where the `i`-th generator is printed as `L[i]`.

The third form, if there are `n` arguments `L...`,
returns the free group of rank `n`,
where the `i`-th generator is printed as `L[i]`.

!!! warning "Note"
    Variables named like the group generators are *not* created by this function.
"""
function free_group(n::Int, s::VarName = :f; eltype::Symbol = :letter)
   @req n >= 0 "n must be a non-negative integer"
   if eltype == :syllable
     G = FPGroup(GAP.Globals.FreeGroup(n, GAP.GapObj(s); FreeGroupFamilyType = GapObj("syllable"))::GapObj)
   else
     G = FPGroup(GAP.Globals.FreeGroup(n, GAP.GapObj(s))::GapObj)
   end
   GAP.Globals.SetRankOfFreeGroup(G.X, n)
   return G
end

function free_group(L::Vector{<:VarName})
   J = GAP.GapObj(L, recursive = true)
   G = FPGroup(GAP.Globals.FreeGroup(J)::GapObj)
   GAP.Globals.SetRankOfFreeGroup(G.X, length(J))
   return G
end

function free_group(L::VarName...)
   J = GAP.GapObj(L, recursive = true)
   G = FPGroup(GAP.Globals.FreeGroup(J)::GapObj)
   GAP.Globals.SetRankOfFreeGroup(G.X, length(J))
   return G
end

# FIXME: a function `free_abelian_group` with the same signature is
# already being defined by Hecke
#function free_abelian_group(n::Int)
#  return FPGroup(GAPWrap.FreeAbelianGroup(n))
#end

function free_abelian_group(::Type{FPGroup}, n::Int)
 return FPGroup(GAPWrap.FreeAbelianGroup(n)::GapObj)
end


# for the definition of group modulo relations, see the quo function in the sub.jl section

function free_group(G::FPGroup)
   return FPGroup(GAPWrap.FreeGroupOfFpGroup(G.X)::GapObj)
end

################################################################################
#
# end FpGroups
#
################################################################################

"""
    dihedral_group(::Type{T} = PcGroup, n::Union{IntegerUnion,PosInf})

Return the dihedral group of order `n`, as an instance of `T`,
where `T` is in {`PcGroup`,`PermGroup`,`FPGroup`}.

!!! warning

    There are two competing conventions for interpreting the argument `n`:
    In the one we use, the returned group has order `n`, and thus `n` must
    always be even.
    In the other, `n` indicates that the group describes the symmetry of an
    `n`-gon, and thus the group has order `2n`.

# Examples
```jldoctest
julia> dihedral_group(6)
Pc group of order 6

julia> dihedral_group(PermGroup, 6)
Permutation group of degree 3

julia> dihedral_group(PosInf())
Pc group of infinite order

julia> dihedral_group(7)
ERROR: ArgumentError: n must be a positive even integer or infinity
```
"""
dihedral_group(n::Union{IntegerUnion,PosInf}) = dihedral_group(PcGroup, n)

function dihedral_group(::Type{T}, n::Union{IntegerUnion,PosInf}) where T <: GAPGroup
  @req is_infinite(n) || (iseven(n) && n > 0) "n must be a positive even integer or infinity"
  return T(GAP.Globals.DihedralGroup(_gap_filter(T), GAP.Obj(n))::GapObj)
end

# Delegating to the GAP constructor via `_gap_filter` does not work here.
function dihedral_group(::Type{PcGroup}, n::Union{IntegerUnion,PosInf})
  if is_infinite(n)
    return PcGroup(GAP.Globals.DihedralPcpGroup(0))
  elseif iseven(n) && n > 0
    return PcGroup(GAP.Globals.DihedralGroup(GAP.Globals.IsPcGroup, GAP.Obj(n))::GapObj)
  end
  throw(ArgumentError("n must be a positive even integer or infinity"))
end

@doc raw"""
    is_dihedral_group(G::GAPGroup)

Return `true` if `G` is isomorphic to a dihedral group,
and `false` otherwise.

# Examples
```jldoctest
julia> is_dihedral_group(small_group(8,3))
true

julia> is_dihedral_group(small_group(8,4))
false

```
"""
@gapattribute is_dihedral_group(G::GAPGroup) = GAP.Globals.IsDihedralGroup(G.X)::Bool

"""
    quaternion_group(::Type{T} = PcGroup, n::IntegerUnion)

Return the (generalized) quaternion group of order `n`,
as an instance of `T`,
where `n` is a power of 2 and `T` is in {`PcGroup`,`PermGroup`,`FPGroup`}.

# Examples
```jldoctest
julia> g = quaternion_group(8)
Pc group of order 8

julia> quaternion_group(PermGroup, 8)
Permutation group of degree 8

julia> g = quaternion_group(FPGroup, 8)
Finitely presented group of order 8

julia> relators(g)
3-element Vector{FPGroupElem}:
 r^2*s^-2
 s^4
 r^-1*s*r*s

```
"""
quaternion_group(n::IntegerUnion) = quaternion_group(PcGroup, n)

function quaternion_group(::Type{T}, n::IntegerUnion) where T <: GAPGroup
  # FIXME: resolve naming: dicyclic vs (generalized) quaternion: only the
  # former should be for any n divisible by 4; the latter only for powers of 2.
  # see also debate on the GAP side (https://github.com/gap-system/gap/issues/2725)
  @assert iszero(mod(n, 4))
  return T(GAP.Globals.QuaternionGroup(_gap_filter(T), n)::GapObj)
end

# Delegating to the GAP constructor via `_gap_filter` does not work here.
function quaternion_group(::Type{PcGroup}, n::IntegerUnion)
  @assert iszero(mod(n, 4))
  return PcGroup(GAP.Globals.QuaternionGroup(GAP.Globals.IsPcGroup, n)::GapObj)
end

@doc raw"""
    is_quaternion_group(G::GAPGroup)

Return `true` if `G` is isomorphic to a (generalized) quaternion group
of order $2^{k+1}, k \geq 2$, and `false` otherwise.

# Examples
```jldoctest
julia> is_quaternion_group(small_group(8, 3))
false

julia> is_quaternion_group(small_group(8, 4))
true

```
"""
@gapattribute is_quaternion_group(G::GAPGroup) = GAP.Globals.IsQuaternionGroup(G.X)::Bool
