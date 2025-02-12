# Internal methods to estimate the complexity of choosing an 
# entry as pivot.
_complexity(c::FieldElem) = is_zero(c) ? -1 : 1
_complexity(f::MPolyRingElem) = is_zero(f) ? -1 : length(f) + total_degree(f)
_complexity(f::MPolyQuoRingElem) = _complexity(lift(f))
_complexity(f::MPolyLocRingElem) = _complexity(numerator(f)) + _complexity(denominator(f))
_complexity(f::MPolyQuoLocRingElem) = _complexity(lifted_numerator(f)) + _complexity(lifted_denominator(f))

_min_complexity(A::MatrixElem) = is_zero(A) ? -1 : minimum(_complexity(A[i, j]) for i in 1:nrows(A) for j in 1:ncols(A))
_min_complexity(A::SMat) = is_zero(A) ? -1 : minimum(minimum([_complexity(a) for (_, a) in A[i]]) for i in 1:nrows(A))

_max_complexity(A::MatrixElem) = is_zero(A) ? 0 : maximum(_complexity(A[i, j]) for i in 1:nrows(A) for j in 1:ncols(A))
_max_complexity(A::SMat) = is_zero(A) ? 0 : maximum(maximum([_complexity(a) for (_, a) in A[i]]) for i in 1:nrows(A))


# Return a list of tuples `(i, j, a, c)` with `(i, j)` the indices of an entry `a`
# and `c` its `_complexity`. The list is ordered with first entry's `c` 
# of least value among all entries in the matrix. The list is guaranteed 
# to contain all entries of least `_complexity`, but its total length 
# depends on the input and can not be estimated a priori. 
function _find_entries_with_least_complexity(A::MatrixElem; minimum::Int=-1)
  R = base_ring(A)
  result = Vector{Tuple{Int, Int, elem_type(R), Int}}()
  is_zero(A) && return result
  for i in 1:nrows(A)
    for j in 1:ncols(A)
      c = A[i, j]
      is_zero(c) && continue
      comp = _complexity(c)
      if comp <= minimum || minimum < 0
        push!(result, (i, j, c, comp))
        if comp < minimum || minimum < 0
          minimum = comp
        end
      end
    end
  end
  return reverse(result)
end

function _find_entries_with_least_complexity(A::SMat; minimum::Int=-1)
  R = base_ring(A)
  result = Vector{Tuple{Int, Int, elem_type(R), Int}}()
  is_zero(A) && return result
  for i in 1:nrows(A)
    for (j, c) in A[i]
      comp = _complexity(c)
      if comp <= minimum || minimum < 0
        push!(result, (i, j, c, comp))
        if comp < minimum || minimum < 0
          minimum = comp
        end
      end
    end
  end
  return reverse(result)
end

### getters for MatrixTreeNode
matrix(n::MatrixTreeNode) = n.A
matrix(N::GeometricGaussNode) = N.A

# Return a list with triples `(i, j, c)` with entries of minimal `_complexity` 
# in the `matrix` of `n`. 
function least_complex_entries(n::MatrixTreeNode; minimum::Int=-1)
  if !isdefined(n, :least_complex_entries)
    n.least_complex_entries = _find_entries_with_least_complexity(matrix(n); minimum)
  end
  return n.least_complex_entries
end

function least_complex_entry(N::GeometricGaussNode)
  !isdefined(N, :least_complex_entries) && least_complex_entries(N)
  is_empty(N.least_complex_entries) && return nothing
  return first(N.least_complex_entries)
end

function least_complex_entries(N::GeometricGaussNode; minimum::Int=-1)
  if !isdefined(N, :least_complex_entries)
    N.least_complex_entries = _find_entries_with_least_complexity(matrix(N); minimum)
  end
  return N.least_complex_entries
end



function least_complex_entry(n::MatrixTreeNode)
  least_complex_entries(n) # fill the cache
  is_empty(n.least_complex_entries) && return (0, 0, zero(base_ring(n.A)), -1)
  return first(least_complex_entries(n))
end

# Create the nodes for the localizations for the entries with the least complexity.
function loc_nodes(n::MatrixTreeNode; width::Int=2)
  max_width = minimum([length(least_complex_entries(n)), width])
  if !isdefined(n, :loc_nodes)
    n.loc_nodes = Vector{MatrixTreeNode}()
  end
  if length(n.loc_nodes) < width
    A = matrix(n)
    R = base_ring(A)
    for (i, j, c, comp) in least_complex_entries(n)[length(n.loc_nodes)+1:max_width]
      is_zero(c) && break
      res = _apply!([(i, j, :loc)], A)
      push!(n.loc_nodes, MatrixTreeNode(res))
    end
  end
  return n.loc_nodes[1:max_width]
end

function quo_nodes(n::MatrixTreeNode; width::Int=2)
  max_width = minimum([length(least_complex_entries(n)), width])
  if !isdefined(n, :quo_nodes)
    n.quo_nodes = Vector{MatrixTreeNode}()
  end
  if length(n.quo_nodes) < width
    A = matrix(n)
    R = base_ring(A)
    for (i, j, c, comp) in least_complex_entries(n)[length(n.quo_nodes)+1:max_width]
      is_zero(c) && break
      res = _apply!([(i, j, :quo)], A)
      push!(n.quo_nodes, MatrixTreeNode(res))
    end
  end
  return n.quo_nodes[1:max_width]
end

function getindex(N::GeometricGaussNode, t::Tuple)
  return N[t...]
end

function getindex(N::GeometricGaussNode, i::Int, j::Int, type::Symbol)
  0 < i <= nrows(matrix(N)) || error("row index out of bounds")
  0 < j <= ncols(matrix(N)) || error("column index out of bounds")
  if !isdefined(N, :children)
    N.children = Dict{Tuple{Int, Int, Symbol}, GeometricGaussNode}()
  end
  return get!(N.children, (i, j, type)) do
    B = _apply!([(i, j, type)], matrix(N))
    GeometricGaussNode(B)
  end
end

function getindex(N::GeometricGaussNode, prog::Vector)
  is_empty(prog) && return N
  return (N[last(prog)])[prog[1:end-1]]
end

function collect_leaves(N::GeometricGaussNode; depth::Int=0)
  #println(prod(" " for _ in 1:depth; init="") * "size: $(size(matrix(N))), is_zero: $(is_zero(matrix(N)))")
  is_zero(matrix(N)) && return [Vector{Tuple{Int, Int, Symbol}}()]
  i, j, _ = first(least_complex_entries(N))
  #println(prod(" " for _ in 1:depth; init="") * "($i, $j)")
  #println(prod(" " for _ in 1:depth; init="") * "loc...")
  loc = [push!(prog, (i, j, :loc)) for prog in collect_leaves(N[i, j, :loc]; depth=depth+1)]
  #println(prod(" " for _ in 1:depth; init="") * "$(loc)")
  #println(prod(" " for _ in 1:depth; init="") * "quo...")
  quo = [push!(prog, (i, j, :quo)) for prog in collect_leaves(N[i, j, :quo]; depth=depth+1)]
  #println(prod(" " for _ in 1:depth; init="") * "$(quo)")
  #println(prod(" " for _ in 1:depth; init="") * "done.")
  return vcat(loc, quo)
end

# Return a pair `(prog, task)` where `task` is a `Symbol` which is either
#   * `:wait` if all tasks below `N` are pending
#   * `:prepare_modulus` if the modulus of some `base_ring` for this node 
#     or one below it has not yet been prepared
#   * `:gather_results` if the results of the children are ready and waiting 
#     to be assembled
#   * `:done` if every task associated to this node or below has been achieved.
#
#   Then `prog` is a linear program leading to the node to which the task is 
#   associated. 
function get_next_task(N::GeometricGaussNode; depth::Int=0)
  #println(prod(" " for _ in 1:depth; init="") * "$(status(N))")
  status(N) == :done && return Tuple{Int, Int, Symbol}[], :done

  A = matrix(N)
  R = base_ring(A)
  if status(N) == :unexplored
    # Check whether we need to do a GB computation on the workers
    if !_has_prepared_modulus(R)
      set_status!(N, :modulus_preparation)
      return Tuple{Int, Int, Symbol}[], :prepare_modulus
    end
    set_status!(N, :modulus_prepared)
  end

  if status(N) == :modulus_prepared
    # If the modulus is prepared, do the reduction on the matrix here.
    # Overhead for sending is probably bigger than reduction on the main process.
    if is_zero(A)
      N.result = [(ideal(R, elem_type(R)[]), 0)]
      set_status!(N, :done)
      return Tuple{Int, Int, Symbol}[], :done
    end
    set_status!(N, :explore_children)
  end

  if status(N) == :explore_children
    # If the matrix is not zero, check for the child nodes
    i, j, _ = least_complex_entry(N)
    loc = N[i, j, :loc]
    loc_prog, loc_task = get_next_task(loc; depth=depth+1)
    #println(prod(" " for _ in 1:depth; init="") * "loc_task: $(loc_task)")
    if !(loc_task == :wait || loc_task == :done)
      return push!(loc_prog, (i, j, :loc)), loc_task
    end
    quo = N[i, j, :quo]
    quo_prog, quo_task = get_next_task(quo; depth=depth+1)
    if !(quo_task == :wait || quo_task == :done)
      return push!(quo_prog, (i, j, :quo)), quo_task
    end
    #println(prod(" " for _ in 1:depth; init="") * "quo_task: $(quo_task)")
    if loc_task == :done && quo_task == :done
      set_status!(N, :result_gathering)
      return Tuple{Int, Int, Symbol}[], :gather_results
    end
    return Tuple{Int, Int, Symbol}[], :wait
    (loc_task == :wait || loc_task == :done) && return push!(quo_prog, (i, j, :quo)), quo_task
    return push!(loc_prog, (i, j, :loc)), loc_task
  end

  status(N) == :result_gathering || status(N) == :modulus_preparation || error("status not recognized")
  return Tuple{Int, Int, Symbol}[], :wait
end

status(N::GeometricGaussNode) = N.state
function set_status!(N::GeometricGaussNode, stat::Symbol)
  N.state = stat
end

has_result(N::GeometricGaussNode) = isdefined(N, :result) && N.result isa Vector

function has_locally_constant_rank_distributed(M::MatrixElem)
  return has_locally_constant_rank_distributed(GeometricGaussNode(M))
end

function has_locally_constant_rank_distributed(N0::GeometricGaussNode)
  worker_ids = workers()
  n_workers = length(worker_ids)
  futures = Union{Future, Nothing}[nothing for _ in 1:n_workers]
  assigned_tasks = Any[nothing for _ in 1:n_workers]
  channels = [RemoteChannel(()->Channel{Any}(1024), i) for i in worker_ids]

  while true
    # assign work
    while any(isnothing, futures)
      i = findfirst(isnothing, futures)
      fut = futures[i]
      #@show i, isnothing(fut)
      id = worker_ids[i]
      #println("computing next task...")
      prog, task = get_next_task(N0) 
      #@show prog, task
      if task == :wait
        all(isnothing, futures) && error("waiting for nothing")
        @vprint :GeometricGauss 1 "waiting with unloaded workers ($(sum(isnothing.(futures))) of $(n_workers) idle)\n"
        @vprint :GeometricGauss 1 prod("$j: $task\n" for (j, task) in enumerate(assigned_tasks); init="")
        @vprint :GeometricGauss 1 "$(N0)"
        break
      end
      if task == :done
        all(isnothing, futures) || error("not all tasks are done")
        return true, N0.result
      end
      N = N0[prog]
      assigned_tasks[i] = (prog, task)
      par_task = _prepare_task(N0, prog, task)
      #@show typeof(par_task)
      put_type_params(channels[i], par_task)
      futures[i] = remotecall(_compute, id, par_task)
    end

    i = findfirst(x->(!isnothing(x) && isready(x)), futures)
    i === nothing && continue
    fut = futures[i]
    prog, task = assigned_tasks[i]
    #@show task
    N = N0[prog]
    if task == :prepare_modulus
      #@show "modulus prepared"
      success, g = fetch(fut)
      R = base_ring(matrix(N))
      _set_modulus!(R, g)
      @assert _has_prepared_modulus(R)
      set_status!(N, :modulus_prepared)
    elseif task == :gather_results
      #@show "results gathered"
      _, (success, comps) = fetch(fut)
      #@show success, comps
      if !success 
        N0.result = Vector{Tuple{Ideal, Int}}()
        return false, N0.result
      end
      N.result = comps
      set_status!(N, :done)
    else
      error("task not recognized")
    end
    futures[i] = nothing # make worker available
    assigned_tasks[i] = nothing 
  end
  #@show isnothing.(futures)
  #@show [!isnothing(fut) && isready(fut) for fut in futures]
  if status(N0) == :done
    @assert all(isnothing, assigned_tasks) 
    return true, N0.result
  end
end

_set_modulus!(R::MPolyRing, ::Vector) = nothing

function _set_modulus!(R::MPolyQuoRing, g::Vector)
  P = base_ring(R)
  ig = IdealGens(g, default_ordering(P); keep_ordering=true, isGB=true)
  ig.isReduced = false
  modulus(R).gb[default_ordering(P)] = ig
end

function _set_modulus!(R::MPolyQuoLocRing, g::Vector)
  P = base_ring(R)
  I = ideal(P, g)
  ig = IdealGens(g, default_ordering(P); keep_ordering=true, isGB=true)
  ig.isReduced = false
  I.gb[default_ordering(P)] = ig
  modulus(R).saturated_ideal = I
end


function _compute(task::ComputeLeaf)
  A = task.A
  is_zero(A) || error("not a leaf")
  R = base_ring(A)
  return true, [(ideal(R, elem_type(R)[]), 0)]
end

function _compute(task::GatherResults)
  a = task.a
  loc_comps = task.loc_list
  quo_comps = task.quo_list
  R = parent(a)
  a_ideal = ideal(R, a)
  
  pb_loc_comps = [(saturation(I, a_ideal), r) for (I, r) in loc_comps]
  pb_quo_comps = [(I + a_ideal, r) for (I, r) in quo_comps]
  final_comps = Vector{Tuple{ideal_type(R), Int}}()
  @vprint :GeometricGauss 2 "ordering localized components...\n"
  for (I, r) in pb_loc_comps
    is_one(I) && continue
    for (J, s) in final_comps
      if !is_one(I + J)
        # Components meet
        r == s || return true, (false, [(ideal(R, elem_type(R)[]), 0)])
      end
    end
    push!(final_comps, (I, r))
  end
  @vprint :GeometricGauss 2 "ordering quotient components...\n"
  for (I, r) in pb_quo_comps
    is_one(I) && continue
    container_found = false
    for (J, s) in final_comps
      if !is_one(I + J)
        # Components meet
        r == s || return true, (false, [(ideal(R, elem_type(R)[]), 0)])
        if is_subset(J, I) || all(radical_membership(g, I) for g in gens(J))
          container_found = true # V(J) contains V(I)
        end
      end
    end
    !container_found && push!(final_comps, (I, r))
  end
  @vprint :GeometricGauss 2 "ordering quotient components...\n"
  return true, (true, final_comps)
end

function _prepare_task(N0::GeometricGaussNode, prog::Vector, symb::Symbol)
  N = N0[prog]
  #if symb == :compute_leaf
  #  return ComputeLeaf(matrix(N))
  if symb == :gather_results
    i, j, a, _ = least_complex_entry(N)
    #@show prog
    loc_ideals = N[i, j, :loc].result::Vector
    quo_ideals = N[i, j, :quo].result::Vector
    R = base_ring(matrix(N))
    return GatherResults(a, 
                         [(ideal(R, lifted_numerator.(gens(I))), r+1) for (I, r) in loc_ideals],
                         [(ideal(R, lifted_numerator.(gens(I))), r) for (I, r) in quo_ideals]
                        )
  elseif symb == :prepare_modulus
    R = base_ring(matrix(N))
    return PrepareModulus(R)
  else
    error("task not recognized")
  end
end

#=
# Idea doesn't seem to work because of the unit-block...
function _collect_bases!(prog::Vector, bases::Vector{Vector{Int}})
  is_empty(prog) && return bases
  (i, j, type) = pop!(prog)
  type == :loc && return _collect_bases!(prog, [[a < j ? a : a-1 for a in basis if !(a == j)] for basis in bases])
  return _collect_bases!(prog, bases)
end

function decompose_realization_space(
    M::Matroid; 
    X::MatroidRealizationSpace=realization_space(M; ground_ring=QQ)
  )
  A = realization_matrix(X)
  P = base_ring(A)::MPolyRing
  N = GeometricGaussNode(A)
  progs = collect_leaves(N)
  bas = bases(M)
  nbas = nonbases(M)
  result = Bool[]
  for prog in progs
    @show prog
    leaf = N[prog]
    AA = matrix(leaf)
    @show AA
    bas_res = [ind for ind in _collect_bases!(prog, bas) if length(ind) == nrows(AA)]
    nbas_res = [ind for ind in _collect_bases!(prog, nbas) if length(ind) == nrows(AA)]
    @show bas_res
    @show nbas_res
    f = [det(AA[:, ind]) for ind in nbas_res]
    D = jacobian_matrix(base_ring(AA), f)
    d = [lifted_numerator(det(AA[:, ind])) for ind in bas_res]
    @show f
    @show d
    if any(is_zero, d) 
      push!(result, true)
      continue
    end
    U = MPolyPowersOfElement(P, d)
    R, loc = localization(base_ring(AA), U)
    DD = map_entries(loc, D)
    push!(result, has_locally_constant_rank(DD)[1])
  end
  result
end
=#


# Apply a Gauss-elimination like program to `A` and return the resulting sub-matrix
function _apply!(prog::Vector{Tuple{Int, Int, Symbol}}, A::SMat)
  is_empty(prog) && return A
  R = base_ring(A)
  i, j, symb = pop!(prog)
  c = A[i, j]
  m = nrows(A)
  n = ncols(A)
  if symb == :loc
    L, loc = localization(R, powers_of_element(lifted_numerator(c)))
    lc = loc(c)
    result = sparse_matrix(L, 0, n-1)
    u = A[i]
    uu = map_entries(loc, u)
    for (k, v) in enumerate(A)
      k == i && continue # Skip the i-th row
      w = is_empty(v) ? sparse_row(L) : map_entries(loc, v)
      b = w[j]
      #if !is_zero(b) # Check takes a lot of time because of computation of `saturated_ideal`
        w = Hecke.add_scaled_row!(uu, Hecke.scale_row!(w, lc), -b)
      #end
      push!(result, _remove_column!(w, j))
    end
    return _apply!(prog, result)
  elseif symb == :quo
    Q, pr = quo(R, ideal(R, c))
    result = map_entries(pr, A)
    _zero!(result[i], j)
    return _apply!(prog, result)
  else
    error("symbol $symb not recognized")
  end
end

function _apply!(prog::Vector{Tuple{Int, Int, Symbol}}, A::MatrixElem)
  is_empty(prog) && return A
  R = base_ring(A)
  i, j, symb = pop!(prog)
  c = A[i, j]
  m = nrows(A)
  n = ncols(A)
  if symb == :loc
    L, loc = localization(R, powers_of_element(lifted_numerator(c)))
    LA = map_entries(loc, A)
    lc = loc(c)
    for k in 1:nrows(A)
      k == i && continue # Skip the i-th row
      b = LA[k, j]
      #is_zero(b) && continue # This takes a lot of time because of computation of `saturated_ideal`
      LA = AbstractAlgebra.multiply_row!(LA, lc, k)
      AbstractAlgebra.add_row!(LA, -b, i, k)
    end
    result = vcat(hcat(LA[1:i-1, 1:j-1], LA[1:i-1, j+1:end]), 
                  hcat(LA[i+1:end, 1:j-1], LA[i+1:end, j+1:end]))
    return _apply!(prog, result)
  elseif symb == :quo
    Q, pr = quo(R, ideal(R, c))
    result = map_entries(pr, A)
    result[i, j] = zero(Q)
    return _apply!(prog, result)
  else
    error("symbol $symb not recognized")
  end
end

function _remove_column!(v::SRow, j::Int)
  l = findfirst(>=(j), v.pos)
  l === nothing && return v
  if v.pos[l] == j
    deleteat!(v.pos, l)
    deleteat!(v.values, l)
  end
  for k in l:length(v.pos)
    v.pos[k] -= 1
  end
  return v
end

function _zero!(v::SRow, j::Int)
  l = findfirst(>=(j), v.pos)
  l === nothing && return v
  if v.pos[l] == j
    deleteat!(v.pos, l)
    deleteat!(v.values, l)
  end
  return v
end

# Perform a tree search for the least minimal complexity among all entries 
# of the respective resulting matrix in the Gauss-tree for `N`. 
# Return the linear program leading to that matrix and its final complexity. 
function explore_minimal_complexity(N::MatrixTreeNode; depth::Int=3, width::Int=2)
  @vprint :GeometricGauss 2 "exploring least minimal complexity for node with matrix of size $(size(matrix(N))); depth = $depth, width = $width\n"
  (is_zero(depth) || is_zero(matrix(N))) && return Vector{Tuple{Int, Int, Symbol}}(), _min_complexity(matrix(N))

  exp_rec = [explore_minimal_complexity(ln; depth=depth-1, width) for ln in loc_nodes(N; width)]
  @vprint :GeometricGauss 2 "complexities returned: $([c for (_, c) in exp_rec])\n"

  min = -1
  winner = Vector{Tuple{Int, Int, Symbol}}(), -1
  for ((i, j, c, comp), (prog, min_comp)) in zip(least_complex_entries(N), exp_rec)
    if min_comp < min || min < 0
      push!(prog, (i, j, :loc))
      winner = prog, min_comp
    end
  end
  return winner
end

# Perform a tree search for the least maximal complexity among all entries 
# of the respective resulting matrix in the Gauss-tree for `N`. 
# Return the linear program leading to that matrix and its final complexity. 
function explore_maximal_complexity(N::MatrixTreeNode; depth::Int=3, width::Int=2)
  @vprint :GeometricGauss 2 "exploring least maximal complexity for node with matrix of size $(size(matrix(N))); depth = $depth, width = $width\n"
  (is_zero(depth) || is_zero(matrix(N))) && return Vector{Tuple{Int, Int, Symbol}}(), _max_complexity(matrix(N))

  exp_rec = [explore_maximal_complexity(ln; depth=depth-1, width) for ln in loc_nodes(N; width)]
  @vprint :GeometricGauss 2 "complexities returned: $([c for (_, c) in exp_rec])\n"

  max = -1
  winner = Vector{Tuple{Int, Int, Symbol}}(), -1
  for ((i, j, c, comp), (prog, max_comp)) in zip(least_complex_entries(N), exp_rec)
    if max_comp < max || max < 0
      push!(prog, (i, j, :loc))
      winner = prog, max_comp
    end
  end
  return winner
end

# Check whether the matrix `A` has locally constant rank on the spectrum 
# of its `base_ring` `R`. In the affirmative case, return `true, comps` where 
# `comps` is a list of `Tuple`s `(I, r)` with `I` an ideal in `R` and `r` the 
# rank of `A` along the vanishing locus of `I` and Spec(R) = ∪ V(I).
# Otherwise, return `false, comps` where `comps` is a dummy list. 
function has_locally_constant_rank(
    A::Union{<:MatrixElem, <:SMat}; 
    depth::Int=3, width::Int=2, parallel::Bool=false
  )
  return _has_locally_constant_rank(MatrixTreeNode(A); depth, width, parallel)
end

function _has_locally_constant_rank(
    N0::MatrixTreeNode; 
    depth::Int=2, width::Int=2, parallel::Bool=false
  )
  @vprint :GeometricGauss 2 "exploring whether matrix of size $(size(matrix(N0))) over $(base_ring(matrix(N0))) has locally constant rank...\n"
  A = matrix(N0)
  R = base_ring(A)
  if is_zero(A)
    return true, [(ideal(R, elem_type(R)[]), 0)]
  end
  # As long as we still need to localize, aim for minimizing the next inverted element.
  # Otherwise, aim for keeping all entries in the matrix small.
  #prog, _ = depth < nrows(A) ? explore_minimal_complexity(N0; depth, width) : explore_maximal_complexity(N0; depth, width)
  prog, _ = parallel ? explore_minimal_complexity_parallel(N0; depth, width) : explore_maximal_complexity(N0; depth, width)
  @vprint :GeometricGauss 2 "linear program for least complexity: $prog\n"

  (i, j, symb) = last(prog)
  k = findfirst(x->(x[1]==i && x[2]==j), least_complex_entries(N0))
  k === nothing && error("entry not found")
  @vprint :GeometricGauss 2 "exploring localized direction at item $k with pivot $(A[i, j]) at index ($i, $j)...\n"
  loc_succ, loc_comps = _has_locally_constant_rank(loc_nodes(N0; width)[k]; depth, width, parallel)
  !loc_succ && return false, [(ideal(R, elem_type(R)[]), 0)]
  @vprint :GeometricGauss 2 "taking closures of components...\n"
  pb_loc_comps = [(saturation(ideal(R, [R(lifted_numerator(g)) for g in gens(I)]), 
                              ideal(R, A[i, j])), r+1) for (I, r) in loc_comps]
  @vprint :GeometricGauss 2 "exploring quotient direction...\n"
  quo_succ, quo_comps = _has_locally_constant_rank(quo_nodes(N0; width)[k]; depth, width, parallel)
  !quo_succ && return false, [(ideal(R, elem_type(R)[]), 0)]
  pb_quo_comps = [(ideal(R, push!([R(lifted_numerator(g)) for g in gens(I)], A[i, j])), r) for (I, r) in quo_comps]
  final_comps = Vector{Tuple{ideal_type(R), Int}}()
  @vprint :GeometricGauss 2 "ordering localized components...\n"
  for (I, r) in pb_loc_comps
    is_one(I) && continue
    for (J, s) in final_comps
      if !is_one(I + J)
        # Components meet
        r == s || return false, [(ideal(R, elem_type(R)[]), 0)]
      end
    end
    push!(final_comps, (I, r))
  end
  @vprint :GeometricGauss 2 "ordering quotient components...\n"
  for (I, r) in pb_quo_comps
    is_one(I) && continue
    container_found = false
    for (J, s) in final_comps
      if !is_one(I + J)
        # Components meet
        r == s || return false, [(ideal(R, elem_type(R)[]), 0)]
        if is_subset(J, I) || all(radical_membership(g, I) for g in gens(J))
          container_found = true # V(J) contains V(I)
        end
      end
    end
    !container_found && push!(final_comps, (I, r))
  end
  @vprint :GeometricGauss 2 "ordering quotient components...\n"
  return true, final_comps
end

# Parallel method
function explore_minimal_complexity_parallel(N::MatrixTreeNode; depth::Int=3, width::Int=2)
  @vprint :GeometricGauss 2 "exploring least minimal complexity for node with matrix of size $(size(matrix(N))); depth = $depth, width = $width\n"
  (is_zero(depth) || is_zero(matrix(N))) && return Vector{Tuple{Int, Int, Symbol}}(), _min_complexity(matrix(N))

  _, exp_rec = parallel_all([ComplexityExploration(matrix(ln), depth, width) for ln in loc_nodes(N; width)])
  @vprint :GeometricGauss 2 "complexities returned: $([c for (_, c) in exp_rec])\n"

  min = -1
  winner = Vector{Tuple{Int, Int, Symbol}}(), -1
  for ((i, j, c, comp), (prog, min_comp)) in zip(least_complex_entries(N), exp_rec)
    if min_comp < min || min < 0
      push!(prog, (i, j, :loc))
      winner = prog, min_comp
    end
  end
  return winner
end

function _compute(T::ComplexityExploration)
  prog, compl = explore_minimal_complexity(MatrixTreeNode(T.A); depth=T.depth, width=T.width)
  return true, (prog, compl)
end

# Methods which are allowed to change the internal representative in the affirmative case

function _has_locally_constant_rank_parallel(
    N0::MatrixTreeNode; 
    depth::Int=2, width::Int=2
  )
  @vprint :GeometricGauss 2 "exploring whether matrix of size $(size(matrix(N0))) over $(base_ring(matrix(N0))) has locally constant rank...\n"
  n_workers = length(workers())
  A = matrix(N0)
  R = base_ring(A)
  if is_zero(A)
    return true, [(ideal(R, elem_type(R)[]), 0)]
  end
  # As long as we still need to localize, aim for minimizing the next inverted element.
  # Otherwise, aim for keeping all entries in the matrix small.
  #prog, _ = depth < nrows(A) ? explore_minimal_complexity(N0; depth, width) : explore_maximal_complexity(N0; depth, width)
  lce = least_complex_entries(N0)
  @show lce
  nlce = length(lce)

  # create the tasks
  locs = loc_nodes(N0; width=nlce)
  quos = quo_nodes(N0; width=nlce)
  pools = [[HasLocallyConstantRank(A, i, j, :loc, depth, width), 
            HasLocallyConstantRank(A, i, j, :quo, depth, width)] 
           for (i, j, _, _) in lce]
  success, k, result = parallel_any(pools)
  @show success, k, result
  loc_suc, loc_comps = result[1]
  quo_suc, quo_comps = result[2]
  (!loc_suc || !quo_suc) && return false, [(ideal(R, elem_type(R)[]), 0)]
  pb_loc_comps = [(saturation(ideal(R, [R(lifted_numerator(g)) for g in gens(I)]), 
                              ideal(R, A[i, j])), r+1) for (I, r) in loc_comps]
  @vprint :GeometricGauss 2 "exploring quotient direction...\n"
  quo_succ, quo_comps = _has_locally_constant_rank(quo_nodes(N0; width)[k]; depth, width, parallel)
  !quo_succ && return false, [(ideal(R, elem_type(R)[]), 0)]
  pb_quo_comps = [(ideal(R, push!([R(lifted_numerator(g)) for g in gens(I)], A[i, j])), r) for (I, r) in quo_comps]
  final_comps = Vector{Tuple{ideal_type(R), Int}}()
  @vprint :GeometricGauss 2 "ordering localized components...\n"
  for (I, r) in pb_loc_comps
    is_one(I) && continue
    for (J, s) in final_comps
      if !is_one(I + J)
        # Components meet
        r == s || return false, [(ideal(R, elem_type(R)[]), 0)]
      end
    end
    push!(final_comps, (I, r))
  end
  @vprint :GeometricGauss 2 "ordering quotient components...\n"
  for (I, r) in pb_quo_comps
    is_one(I) && continue
    container_found = false
    for (J, s) in final_comps
      if !is_one(I + J)
        # Components meet
        r == s || return false, [(ideal(R, elem_type(R)[]), 0)]
        if is_subset(J, I) || all(radical_membership(g, I) for g in gens(J))
          container_found = true # V(J) contains V(I)
        end
      end
    end
    !container_found && push!(final_comps, (I, r))
  end
  @vprint :GeometricGauss 2 "ordering quotient components...\n"
  return true, final_comps
end

function _compute(task::HasLocallyConstantRank)
  B = _apply!([(task.i, task.j, task.type)], task.A)
  success, comps = has_locally_constant_rank(B; depth=task.depth, width=task.width)
  R = base_ring(task.A)
  !success && return true, (false, [(ideal(R, elem_type(R)[]), 0)])
  final_comps = Vector{Tuple{ideal_type(R), Int}}()
  if task.type == :loc
    pb_loc_comps = [(saturation(ideal(R, [R(lifted_numerator(g)) for g in gens(I)]), 
                                ideal(R, task.A[task.i, task.j])), r+1) for (I, r) in comps]
    for (I, r) in pb_loc_comps
      is_one(I) && continue
      for (J, s) in final_comps
        if !is_one(I + J)
          # Components meet
          r == s || return true, (false, [(ideal(R, elem_type(R)[]), 0)])
        end
      end
      push!(final_comps, (I, r))
    end
    return true, (true, final_comps)
  end # else task.type == :quo
  pb_quo_comps = [(ideal(R, push!([R(lifted_numerator(g)) for g in gens(I)], task.A[task.i, task.j])), r) for (I, r) in comps]
  for (I, r) in pb_quo_comps
    is_one(I) && continue
    container_found = false
    for (J, s) in final_comps
      if !is_one(I + J)
        # Components meet
        r == s || return true, (false, [(ideal(R, elem_type(R)[]), 0)])
        if is_subset(J, I) || all(radical_membership(g, I) for g in gens(J))
          container_found = true # V(J) contains V(I)
        end
      end
    end
    !container_found && push!(final_comps, (I, r))
  end
  return true, (true, final_comps)
end

function _compute(task::PrepareModulus{RT}) where {RT <: MPolyRing}
  return true, elem_type(task.R)[]
end

function _compute(task::PrepareModulus{RT}) where {RT <: MPolyLocRing}
  return true, elem_type(task.R)[]
end

function _compute(task::PrepareModulus{RT}) where {RT <: MPolyQuoRing}
  return true, gens(groebner_basis(modulus(task.R)))
end

function _compute(task::PrepareModulus{RT}) where {RT <: MPolyQuoLocRing}
  return true, gens(groebner_basis(saturated_ideal(modulus(task.R))))
end

_has_prepared_modulus(R::MPolyRing) = true
_has_prepared_modulus(R::MPolyQuoRing) = !is_empty(modulus(R).gb)
_has_prepared_modulus(R::MPolyLocRing) = true
_has_prepared_modulus(R::MPolyQuoLocRing) = isdefined(modulus(R), :saturated_ideal)

_is_explored(N::GeometricGaussNode) = _has_prepared_modulus(base_ring(matrix(N)))

function show(io::IO, N::GeometricGaussNode)
  _print(io, N)
end

function _print(io::IO, N::GeometricGaussNode; depth::Int=0)
  offset = prod("  " for _ in 1:depth; init = "")
  println(io, offset * "$(status(N))")
  for (prog, c) in children(N)
    println(io, offset * "$(prog)")
    _print(io, c; depth=depth+1)
  end
end

function children(N::GeometricGaussNode)
  if !isdefined(N, :children)
    N.children = Dict{Tuple{Int, Int, Symbol}, GeometricGaussNode}()
  end
  return N.children
end

