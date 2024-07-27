# A heap based implementation of sparse row vectors for elements
# which are big in the sense that copying them around in memory 
# for sorting is expensive.
include("Types.jl")

content(n::HeapNode) = n.content
index(n::HeapNode) = n.index
has_left_child(n::HeapNode) = (n.left !== nothing)
has_right_child(n::HeapNode) = (n.right !== nothing)
is_leaf(n::HeapNode) = !has_left_child(n) && !has_right_child(n)
left_child(n::HeapNode{T}) where {T} = n.left::HeapNode{T}
right_child(n::HeapNode{T}) where {T} = n.right::HeapNode{T}

tree_size(n::HeapNode) = (is_leaf(n) ? 1 : 1 + tree_size(n.left) + tree_size(n.right))
tree_size(n::Nothing) = 0

function ancestry_depth(n::HeapNode)
  !has_left_child(n) && !has_right_child(n) && return 0
  n1 = n2 = 0
  has_left_child(n) && (n1 = ancestry_depth(left_child(n)))
  has_right_child(n) && (n2 = ancestry_depth(right_child(n)))
  return maximum([n1, n2]) + 1
end

# TODO: Overwrite hashing!
function ==(a::HeapNode, b::HeapNode)
  return index(a) == index(b) && content(a) == content(b)
end

function _heap_leq(a::HeapNode, b::HeapNode)
  index(a) < index(b) && return true
  index(a) > index(b) && return false
  return _heap_leq(content(a), content(b))
end

### to be overwritten for specified `elem_type`s
function _heap_leq(a::Any, b::Any)
  return true
end

function _heap_leq(a::HeapNode, b::Nothing)
  return true
end

function _heap_leq(a::Nothing, b::HeapNode)
  return false
end

function _heap_leq(a::Nothing, b::Nothing)
  return true
end

function show(io::IO, n::HeapNode; cofactor=1)
  show_recursive(io, n)
end

function show_recursive(io::IO, n::HeapNode; indent::Int=0, cofactor=1)
  new_cof = n.cofactor === nothing ? cofactor : cofactor*n.cofactor
  offset = prod(" " for i in 1:indent; init = "")
  println(offset*"$(index(n)) -> $(new_cof*content(n))")
  has_left_child(n) && show_recursive(io, left_child(n), indent=indent+1, cofactor=new_cof)
  has_right_child(n) && show_recursive(io, right_child(n), indent=indent+1, cofactor=new_cof)
end

base_ring(v::HeapSRow) = v.entry_parent

function index_cache(v::HeapSRow{T}) where {T}
  if !isdefined(v, :index_cache)
    v.index_cache = Dict{Int, T}()
  end
  return v.index_cache
end

function HeapSRow(R::NCRing, list::Vector{Pair{Int, T}}) where {T}
  return HeapSRow(R, [(a, b) for (a, b) in list])
end

function HeapSRow(v::SRow{T}) where {T}
  result = HeapSRow(base_ring(v))
  result.top_is_consolidated = false
  open = HeapNode{T}[]
  
  side = false
  for (i, c) in v
    n = HeapNode(i, c)
    if result.top === nothing 
      result.top = n
      push!(open, n)
      continue
    end
    if !side
      first(open).left = n
      push!(open, n)
      side = true
    else
      popfirst!(open).right = n
      push!(open, n)
      side = false
    end
  end
  return result
end

function HeapSRow(R::NCRing, list::Vector{Tuple{Int, T}}) where {T}
  result = HeapSRow(R)
  isempty(list) && return result
  if isone(length(list))
    i, c = first(list)
    result.top = HeapNode(i, c)
    return result
  end

  n = length(list)
  h = div(n, 2)
  result = HeapSRow(R, list[1:h]) + HeapSRow(R, list[h+1:end])
  return result
end

function pivot(v::HeapSRow)
  consolidate_top!(v)
  isempty(v) && return 1, zero(base_ring(v))
  return index(top_node(v)), content(top_node(v))
end

+(v::HeapSRow, w::HeapSRow) = add!(copy(v), copy(w))

function add!(v::HeapSRow{T}, w::HeapSRow{T}) where {T}
  @assert base_ring(v) === base_ring(w)
  R = base_ring(v)
  isempty(v) && return w
  isempty(w) && return v
  nt = merge!(top_node(v), top_node(w))
  return HeapSRow(R, nt)
end
  


function addmul!(v::HeapSRow{T}, w::HeapSRow{T}, a::T) where {T}
  return add!(v, mul!(a, w))
  @assert base_ring(v) === base_ring(w)
  R = base_ring(v)
  isempty(v) && return w
  isempty(w) && return v

  if !v.top_is_consolidated || !w.top_is_consolidated
    res_tree = merge!(v.top, scale_cofactor!(w.top, a))
    return HeapSRow(base_ring(v), res_tree)
  end

  # the top can be assumed to be consolidated
  # we aim to preserve this property
  i1, c1 = pivot(v)
  i2, c2 = pivot(w)
  n1 = top_node(v)
  n2 = top_node(w)

  left_tree = merge!(n1.left, n1.right)
  #scale_cofactor!(left_tree, n1.cofactor) # superfluous after consolidation
  right_tree = merge!(n2.left, n2.right)
  #scale_cofactor!(right_tree, n2.cofactor)
  scale_cofactor!(right_tree, a)

  if i1 == i2
    c = c1 + a*c2
    if iszero(c)
      res_tree = merge!(left_tree, right_tree)
      v.top = nothing
      w.top = nothing
      return HeapSRow(base_ring(v), res_tree)
    else
      n = HeapNode(i1, c)
      if _heap_leq(n, left_tree) && _heap_leq(n, right_tree)
        n.left = left_tree
        n.right = right_tree
        v.top = nothing
        w.top = nothing
        return HeapSRow(base_ring(v), n; top_is_consolidated = true)
      else
        res_tree = merge!(merge!(left_tree, right_tree), n)
        v.top = nothing
        w.top = nothing
        return HeapSRow(base_ring(v), res_tree)
      end
    end
  end

  # build a consolidated head node for the second summand
  m = HeapNode(i2, a*c2)
  if _heap_leq(n1, m) && haskey(index_cache(w), i1) && iszero(a*index_cache(w)[i1])
    res_top = HeapNode(i1, c1)
    res_top.left = left_tree
    res_top.right = merge!(right_tree, HeapNode(i2, a*c2))
    return HeapSRow(base_ring(v), res_top, top_is_consolidated=true)
  elseif _heap_leq(m, n1) && haskey(index_cache(v), i2) && iszero(index_cache(v)[i2])
    res_top = m
    res_top.left = merge!(left_tree, HeapNode(i1, c1))
    res_top.right = right_tree
    return HeapSRow(base_ring(v), res_top, top_is_consolidated=true)
  end

  # in all cases which have not yet been caught there is little
  # we can say about consolidation
  res_top = merge!(merge!(left_tree, n1), merge!(right_tree, m))
  return HeapSRow(base_ring(v), res_top)
end

function copy(v::HeapSRow)
  isempty(v) && return HeapSRow(base_ring(v))
  n = top_node(v)
  nn = copy_tree(n)
  return HeapSRow(base_ring(v), nn)
end

function copy_tree(n::HeapNode)
  result = HeapNode(index(n), content(n), cofactor=n.cofactor)
  result.left = copy_tree(n.left)
  result.right = copy_tree(n.right)
  return result
end

copy_tree(n::Nothing) = nothing

function *(a::T, v::HeapSRow{T}) where {T}
  return mul!(a, copy(v))
end

function mul!(a::T, v::HeapSRow{T}) where {T}
  isempty(v) && return v
  iszero(a) && return HeapSRow(base_ring(v))
  isone(a) && return v
  # try to preserve consolidation
  if v.top_is_consolidated
    v.top.content *= a
    scale_cofactor!(v.top.left, a)
    scale_cofactor!(v.top.right, a)
  else
    scale_cofactor!(v.top, a)
  end
  # clear the cache
  v.index_cache = Dict{Int, T}()
  return v
end

*(a, v::HeapSRow) = base_ring(v)(a)*v
mul!(a, v::HeapSRow) = mul!(base_ring(v)(a), v)

mult_content_rec_left!(a, n::Nothing) = nothing

function mult_content_rec_left!(a::T, n::HeapNode{T}) where {T}
  iszero(a) && return nothing
  isone(a) && return n
  n.content *= a
  mult_content_rec_left!(a, n.left)
  mult_content_rec_left!(a, n.right)
  is_zero(n.content) && return merge!(n.left, n.right)
  return n
end

-(v::HeapSRow, w::HeapSRow) = addmul!(copy(v), copy(w), -one(base_ring(w)))
-(w::HeapSRow) = -one(base_ring(w))*w

# Remove all entries `i` from `v`, sum them up and return a pair `(c, w)` consisting of the sum `c` and the remainder `w`.
function pop_index!(v::HeapSRow, i::Int)
  R = base_ring(v)
  isempty(v) && return zero(R), v
  c, n = pop_index!(top_node(v), i)
  return c, HeapSRow(R, n)
end

function pop_index!(n::HeapNode{T}, i::Int) where {T}
  # early abort: if the index of the node is bigger than i
  # then everything that follows will also have greater index
  index(n) > i && return zero(content(n)), n
  if index(n) == i
    result = content(n)
    a, left = pop_index!(n.left, i)
    b, right = pop_index!(n.right, i)
    rem = merge!(left, right)
    result += a
    result += b
    n.cofactor !== nothing && (result *= n.cofactor)
    return result, scale_cofactor!(rem, n.cofactor)
  end

  a, rem_left = pop_index!(n.left, i)
  b, rem_right = pop_index!(n.right, i)
  result = a + b
  n.cofactor !== nothing && (result *= n.cofactor)
  n.left = rem_left
  n.right = rem_right
  return result, n
end

function pop_index!(n::Nothing, i::Int)
  return 0, nothing
end

function scale_cofactor!(n::HeapNode{T}, a::T) where T
  if n.cofactor === nothing 
    n.cofactor = a
  else
    n.cofactor *= a
  end
  return n
end

scale_cofactor!(n::Nothing, a::Any) = nothing
scale_cofactor!(n::HeapNode, a::Nothing) = n

function consolidate_top!(v::HeapSRow)
  v.top_is_consolidated && return v
  isempty(v) && return v
  n = top_node(v)
  i = index(n)
  cof = n.cofactor
  if n.cofactor !== nothing 
    n.content *= n.cofactor
    n.cofactor = nothing
    scale_cofactor!(n.left, cof)
    scale_cofactor!(n.right, cof)
  end
  a, left = pop_index!(n.left, i)
  b, right = pop_index!(n.right, i)
  n.content += a + b
  n.left = left
  n.right = right

  if iszero(n.content)
    v.top = merge!(n.left, n.right)
    return consolidate_top!(v)
  end

  v.top_is_consolidated = true
  return v
end


top_node(v::HeapSRow{T}) where {T} = v.top::HeapNode{T}
isempty(v::HeapSRow) = v.top === nothing

function is_consolidated(v::HeapSRow) 
  v.is_consolidated && return true
  if is_empty(v)
    v.is_consolidated = true
    return true
  end

  n = top_node(v)
  result, _ = _has_duplicate(n, Int[])
  if !result
    v.result = true
    return true
  end
  return false
end

function getindex(v::HeapSRow{T}, i::Int) where {T}
  is_empty(v) && return zero(base_ring(v))
  haskey(index_cache(v), i) && return index_cache(v)[i]
  n = top_node(v)
  v.top_is_consolidated && index(n) == i && return content(n)
  c, rem = pop_index!(n, i)
  index_cache(v)[i] = c
  if iszero(c)
    v.top = rem
  else
    v.top = merge!(rem, HeapNode(i, c))
  end
  return c
end

function merge!(a::HeapNode{T}, b::HeapNode{T}) where {T}
  if _heap_leq(a, b)
    # a is the new top
    a.left = merge!(a.left, a.right)
    scale_cofactor!(a.left, a.cofactor)
    if a.cofactor!==nothing
      a.content *= a.cofactor
      a.cofactor = nothing
    end
    a.right = b
    return a
  else
    b.left = merge!(b.left, b.right)
    scale_cofactor!(b.left, b.cofactor)
    if b.cofactor!==nothing
      b.content *= b.cofactor
      b.cofactor = nothing
    end
    b.right = a
    return b
  end
end

function merge!(a::HeapNode, b::Nothing)
  return a
end

function merge!(a::Nothing, b::HeapNode)
  return b
end

function merge!(a::Nothing, b::Nothing)
  return nothing
end

function has_index(v::HeapSRow{T}, i::Int) where {T}
  isempty(v) && return false
  return _has_index(top_node(v), i)
end

function _has_index(n::HeapNode, i::Int)
  index(n) == i && return true
  has_left_child(n) && _has_index(left_child(n), i) && return true
  has_right_child(n) && _has_index(right_child(n), i) && return true
  return false
end

function all_indices(v::HeapSRow)
  isempty(v) && return Int[]
  return all_indices(top_node(v))
end

function all_indices(n::HeapNode)
  is_leaf(n) && return [index(n)]
  return vcat([index(n)], all_indices(n.left), all_indices(n.right))
end

all_indices(n::Nothing) = Int[]

function as_dictionary(v::HeapSRow)
  result = Dict{Int, elem_type(base_ring(v))}()
  isempty(v) && return result
  result = as_dictionary(top_node(v), result)
  v.index_cache = result
  return result
end

as_dictionary(n::Nothing, result::Dict{Int, T}, c::Any=nothing) where {T} = result

function as_dictionary(n::HeapNode{T}, result::Dict{Int, T}, cofactor::Nothing=nothing) where {T}
  new_cof = n.cofactor === nothing ? one(content(n)) : n.cofactor
  i = index(n)
  if i in keys(result)
    result[i] = result[i] + new_cof * content(n)
  else
    result[i] = new_cof * content(n)
  end
  as_dictionary(n.left, result, n.cofactor)
  as_dictionary(n.right, result, n.cofactor)
  return result
end

function as_dictionary(n::HeapNode{T}, result::Dict{Int, T}, cofactor::T) where {T}
  new_cof = n.cofactor === nothing ? cofactor : n.cofactor*cofactor
  i = index(n)
  if i in keys(result)
    result[i] = result[i] + new_cof * content(n)
  else
    result[i] = new_cof * content(n)
  end
  as_dictionary(n.left, result, new_cof)
  as_dictionary(n.right, result, new_cof)
  return result
end

function iszero(v::HeapSRow)
  isempty(v) && return true
  return all(iszero(c) for c in values(as_dictionary(v)))
end

function ==(v::HeapSRow{T}, w::HeapSRow{T}) where {T}
  isempty(v) && return iszero(w)
  isempty(w) && return iszero(v)
  pivot(v) == pivot(w) || return false

  d1 = as_dictionary(v)
  d2 = as_dictionary(w)
  for (k, c) in d1
    if !(k in keys(d2))
      iszero(c) || return false
      continue
    end
    c == d2[k] || return false
    delete!(d2, k)
  end
  return all(iszero(c) for c in values(d2))
end

