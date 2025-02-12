mutable struct MatrixTreeNode{MatrixType}
  A::MatrixType
  least_complex_entries::Vector
  explored_complexities::Vector
  loc_nodes::Vector{<:MatrixTreeNode}
  loc_results::Vector{<:Vector{<:Tuple{<:Ideal, Int}}}
  quo_nodes::Vector{<:MatrixTreeNode}
  quo_results::Vector{<:Vector{<:Tuple{<:Ideal, Int}}}

  function MatrixTreeNode(A::Union{<:MatrixElem, <:SMat})
    return new{typeof(A)}(A)
  end
end

struct ComplexityExploration{MatrixType} <: ParallelTask
  A::MatrixType
  depth::Int
  width::Int
  
  function ComplexityExploration(A::Union{<:MatrixElem, <:SMat}, depth::Int, width::Int)
    return new{typeof(A)}(A, depth, width)
  end
end

struct PrepareModulus{RingType} <: ParallelTask
  R::RingType

  function PrepareModulus(R::Ring)
    return new{typeof(R)}(R)
  end
end

struct ComputeLeaf{MatrixType} <: ParallelTask
  A::MatrixType

  function ComputeLeaf(A::MatrixElem)
    return new{typeof(A)}(A)
  end
end

struct GatherResults{T1, T2, T3} <: ParallelTask
  a::T1
  loc_list::T2
  quo_list::T3

  function GatherResults(a::RingElem, 
      loc_list::Vector,
      quo_list::Vector
    )
    return new{typeof(a), typeof(loc_list), typeof(quo_list)}(a, loc_list, quo_list)
  end
end

struct HasLocallyConstantRank{MatrixType} <: ParallelTask
  A::MatrixType
  i::Int
  j::Int
  type::Symbol
  depth::Int
  width::Int
  
  function HasLocallyConstantRank(A::Union{<:MatrixElem, <:SMat}, 
      i::Int, j::Int, type::Symbol, depth::Int, width::Int)
    return new{typeof(A)}(A, i, j, type, depth, width)
  end
end

mutable struct GeometricGaussNode{MatrixType}
  A::MatrixType
  state::Symbol
  least_complex_entries::Vector
  children::Dict{Tuple{Int, Int, Symbol}, GeometricGaussNode}
  result::Union{Future, Vector}

  function GeometricGaussNode(A::Union{<:MatrixElem, <:SMat})
    return new{typeof(A)}(A, :unexplored)
  end
end


