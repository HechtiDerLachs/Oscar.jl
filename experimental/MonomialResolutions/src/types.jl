mutable struct BinVec
  entries::Vector{Tuple{Int, Int}}

  function BinVec()
    return new(Vector{Tuple{Int, Int}}())
  end

  function BinVec(pos::Int, mon::Int)
    return new([(pos, mon)])
  end
  
  function BinVec(list::Vector{Tuple{Int, Int}}; sort::Bool=true)
    sort && return new(sort!(list; by=first))
    return new(list)
  end
end

