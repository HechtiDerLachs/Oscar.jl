mutable struct BinVec
  entries::Vector{Tuple{UInt, UInt}}

  function BinVec()
    return new(Vector{Tuple{UInt, UInt}}())
  end

  function BinVec(pos::UInt, mon::UInt)
    return new([(pos, mon)])
  end
  
  function BinVec(list::Vector{Tuple{UInt, UInt}}; sort::Bool=true)
    sort && return new(sort!(list; by=first))
    return new(list)
  end
end

