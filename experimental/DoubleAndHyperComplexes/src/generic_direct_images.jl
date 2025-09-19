### Production of the chains
struct DirectImageChainFactory{ChainType} <: HyperComplexChainFactory{ChainType}
  pfctx::ToricCtxWithParams
  K::AbsHyperComplex
  ranges::Dict{Int, Vector{Vector{UnitRange{Int64}}}}

  function DirectImageChainFactory(pfctx::ToricCtxWithParams, K::AbsHyperComplex)
    T = elem_type(pfctx.R)
    ranges = Dict{Int, Vector{Vector{UnitRange{Int64}}}}()
    return new{FreeMod{T}}(pfctx, K, ranges)
  end
end

function (fac::DirectImageChainFactory{ChainType})(self::AbsHyperComplex, I::Tuple) where {T, ChainType <: FreeMod{T}}
  i = first(I)
  @show i
  ctx = fac.pfctx
  X = toric_variety(ctx)
  d = dim(X)
  ranges = Vector{Vector{UnitRange{Int64}}}()
  k = 0
  graded_complex = fac.K
  macro_offset = 0
  macro_summands = ChainType[]
  while k <= d
    @show k
    @show can_compute_index(graded_complex, k + i)
    if !can_compute_index(graded_complex, k + i)
      summand = free_module(ctx.R, 0)
      push!(macro_summands, summand)
      push!(ranges, Vector{UnitRange{Int64}}())
      k += 1
      continue
    end
    micro_offset = 0
    micro_ranges = Vector{UnitRange{Int64}}()
    micro_summands = ChainType[]
    for (l, g) in enumerate(gens(graded_complex[i + k]))
      @show l
      dd = degree(g)
      coh_mod = cohomology_model(ctx, -dd)
      str = coh_mod[-k]
      @show ngens(str)
      push!(micro_summands, str)
      push!(micro_ranges, macro_offset+micro_offset+1:macro_offset+micro_offset+ngens(str))
      micro_offset += ngens(str)
      @show micro_offset
    end
    macro_summand = is_empty(micro_summands) ? free_module(ctx.R, 0) : direct_sum(micro_summands)[1]
    macro_offset += ngens(macro_summand)
    @show macro_offset
    push!(macro_summands, macro_summand)
    push!(ranges, micro_ranges)
    k += 1
  end
  fac.ranges[i] = ranges
  return is_empty(macro_summands) ? free_module(ctx.R, 0) : direct_sum(macro_summands)[1]
end

function can_compute(fac::DirectImageChainFactory, self::AbsHyperComplex, i::Tuple)
  return true
end

### Production of the morphisms 
struct DirectImageMapFactory{MorphismType} <: HyperComplexMapFactory{MorphismType} end

function (::DirectImageMapFactory)(self::AbsHyperComplex, p::Int, I::Tuple)
  i = first(I)
  # fill the cache
  self[i]
  self[i-1]
  @show i
  fac = chain_factory(self)
  ctx = fac.pfctx
  X = toric_variety(ctx)
  d = dim(X)
  R = ctx.R
  T = elem_type(R)
  graded_complex = fac.K
  macro_block_lifts = Dict{Tuple{Int, Int}, Vector{Tuple{Vector{Int}, Vector{Tuple{Int, FreeModElem{T}}}}}}()
  macro_block_proj = Dict{Tuple{Int, Int}, Vector{Tuple{Vector{Int}, Vector{Tuple{Int, FreeModElem{T}}}}}}()
  macro_blocks = Dict{Tuple{Int, Int}, Vector{FreeModElem{T}}}()
  macro_img_gens = Dict{Tuple{Int, Int}, Vector{Vector{Tuple{Int, FreeModElem{T}}}}}()
  ranges = fac.ranges[i]
  for (k, macro_range) in enumerate(ranges) # iterating through the domains
    @show k
    @show can_compute_index(graded_complex, i+k-1)
    if !can_compute_index(graded_complex, i+k-1)
      #skip
      continue
    end
    if !can_compute_index(graded_complex, i+k-2)
      #skip
      continue
    end
    mat_col = k
    mat_row = k 
    graded_dom = graded_complex[i+k-1]

    # Every generator of `graded_dom` leads to a monomial basis for the 
    # homogeneous elements in that degree. We map these through the 
    # double complex.
    #                   # of generator
    #                     |      sparse format for its block form
    #                     |       |
    #                     V       V
    micro_block_inter = Vector{Tuple{Vector{Int}, Vector{Tuple{Int, FreeModElem{T}}}}}()
    @show macro_range
    for (l, micro_range) in enumerate(macro_range)
      @show l
      dd = -degree(gen(graded_dom, l))
      min_exp = _minimal_exponent_vector(ctx, dd)
      str = ctx[min_exp, dd]
      str_simp = simplified_strand(ctx, min_exp, dd)
      micro_dom = str_simp[-k+1]
      from = simplified_strand_inclusion(ctx, min_exp, dd, -k+1)
      @assert codomain(from) === ctx[min_exp, dd][-k+1]
      micro_block_inter = vcat(micro_block_inter, [(min_exp, [(l, from(g))]) for g in gens(micro_dom)])
    end
    macro_block_lifts[k, k+1] = micro_block_inter

    micro_block_lifts = Vector{Tuple{Vector{Int}, Vector{Tuple{Int, FreeModElem{T}}}}}()
    micro_img_gens = Vector{Vector{Tuple{Int, FreeModElem{T}}}}()
    graded_dom = graded_complex[i+k-1]
    graded_cod = graded_complex[i+k-2]
    graded_mor = map(graded_complex, i+k-1)
    graded_matrix = sparse_matrix(graded_mor)
    for (e, w) in micro_block_inter
      u_dict = Dict{Int, FreeModElem{T}}()
      for (l, ww) in w
        dd = -degree(graded_dom[l])
        @assert parent(ww) === ctx[e, dd][-k+1]
        mat_row = graded_matrix[l]
        for (kk, p) in mat_row
          ee = -degree(graded_cod[kk])
          strand = ctx[e, ee]
          pp = multiplication_map(ctx, p, e, dd, -k+1)
          @assert -degree(p) == dd - ee
          @assert domain(pp) === parent(ww)
          www = pp(ww)
          @assert parent(www) === ctx[e, ee][-k+1]
          is_zero(www) && continue
          if haskey(u_dict, kk)
            www += u_dict[kk]
            if is_zero(www) 
              delete!(u_dict, kk)
            else
              u_dict[kk] = www
            end
          else
            u_dict[kk] = www
          end
        end
      end
      u = [(i, v) for (i, v) in u_dict]
      #=
      u_projected = Tuple{Int, FreeModElem{T}}[]
      for (i, v) in u
        ee = -degree(graded_cod[i])
        min_exp = _minimal_exponent_vector(ctx, ee)
        psinv = ctx[e, min_exp, ee][-k+1]
        pr = cohomology_model_projection(ctx, ee, -k+1)
        push!(u_projected, (i, pr(psinv(v))))
      end
      @show u_projected
      push!(micro_img_gens, u_projected)
      =#
      push!(micro_block_lifts, (e, u))
    end
    macro_block_lifts[k, k] = micro_block_lifts
    #macro_img_gens[k, k] = micro_img_gens

    # fill up the blocks to the right with zeros
    # compute the blocks to the left
    for j in k-1:-1:0 # go through the blocks on the left
      @show j
      @show i + j - 1
      @show can_compute_index(graded_complex, i + j - 1)
      @show can_compute_index(graded_complex, i + j - 2)
      if !can_compute_index(graded_complex, i + j - 1)
        # skip
        continue
      end
      graded_dom = graded_complex[i+j-1]
      micro_block_lifts_dom = macro_block_lifts[k, j+1]
      micro_block_lifts_inter = Vector{Tuple{Vector{Int}, Vector{Tuple{Int, FreeModElem{T}}}}}() # lifted one step up
      micro_block_lifts_cod = Vector{Tuple{Vector{Int}, Vector{Tuple{Int, FreeModElem{T}}}}}() # mapped to the left
      micro_block_proj = Vector{Tuple{Vector{Int}, Vector{Tuple{Int, FreeModElem{T}}}}}() # projections of the `micro_block_lifts_dom`
      micro_img_gens = Vector{Vector{Tuple{Int, FreeModElem{T}}}}()

      # go up the stair
      for (e, v) in micro_block_lifts_dom
        w = Vector{Tuple{Int, FreeModElem{T}}}()
        v_rem = Vector{Tuple{Int, FreeModElem{T}}}()
        v_rem = Dict{Int, FreeModElem{T}}()
        for (l, vv) in v
          ee = -degree(gen(graded_dom, l))
          cech_complex = simplified_strand(ctx, e, ee)
          strand = ctx[e, ee]
          dom = strand[-j]
          v0 = deepcopy(vv)
          if can_compute_map(strand, -j+1)
            @assert dom === parent(v0)
            cod = strand[-j+1]
            h = simplified_strand_homotopy(ctx, e, ee, -j)
            cech_map = map(strand, -j+1)
            @assert dom === domain(h)
            @assert cod === codomain(h)
            ww = h(vv)
            v0 = v0 - cech_map(ww)
            !is_zero(ww) && push!(w, (l, ww))
          end
          if can_compute_map(strand, -j)
            cech_map = map(strand, -j)
            h = simplified_strand_homotopy(ctx, e, ee, -j-1)
            v0 = v0 - h(cech_map(vv))
            @assert is_zero(map(strand, -j)(v0))
          end
          k0 = _minimal_exponent_vector(ctx, ee)
          psinv = ctx[e, k0, ee][-j]
          pr = cohomology_model_projection(ctx, ee, -j)
          pr_v0 = pr(psinv(v0))
          #!is_zero(pr_v0) && push!(v_rem, (l, pr_v0))
          if !is_zero(pr_v0)
            if haskey(v_rem, l)
              vvv = vrem[l] + pr_v0
              if is_zero(vvv)
                delete!(v_rem, l)
              else
                v_rem[l] = vvv
              end
            else
              v_rem[l] = pr_v0
            end
          end
        end
        push!(micro_block_lifts_inter, (e, w))
        push!(micro_img_gens, [(i, v) for (i, v) in v_rem])
      end
      macro_img_gens[k, j+1] = micro_img_gens

      if !can_compute_index(graded_complex, i + j - 2)
        # skip
        continue
      end
      
      graded_cod = graded_complex[i+j-2]
      graded_mor = map(graded_complex, i+j-1)
      graded_matrix = sparse_matrix(graded_mor)

      # move one step forward on that level
      for (e, w) in micro_block_lifts_inter
        u_dict = Dict{Int, FreeModElem{T}}()
        for (l, ww) in w
          mat_row = graded_matrix[l]
          for (k, p) in mat_row
            dd = -degree(graded_dom[k])
            strand = ctx[e, dd]
            pp = multiplication_map(ctx, p, e, dd, -j+1)
            www = pp(ww)
            is_zero(www) && continue
            if haskey(u_dict, k)
              www += u_dict[k]
              if is_zero(www) 
                delete!(u_dict, k)
              else
                u_dict[k] = www
              end
            else
              u_dict[k] = www
            end
          end
        end
        u = [(i, v) for (i, v) in u_dict]
        #=
        u_projected = Tuple{Int, FreeModElem{T}}[]
        for (i, v) in u
          ee = -degree(graded_cod[i])
          cech_map = map(ctx[e, ee], -j+1)
          @assert is_zero(cech_map(v))
          min_exp = _minimal_exponent_vector(ctx, ee)
          @show e
          @show min_exp
          psinv = ctx[e, min_exp, ee][-j+1]
          pr = cohomology_model_projection(ctx, ee, -j+1)
          push!(u_projected, (i, pr(psinv(v))))
        end
        @show u_projected
        push!(micro_img_gens, u_projected)
        =#
        push!(micro_block_lifts_cod, (e, u))
      end
      macro_block_lifts[k, j] = micro_block_lifts_cod
      #macro_img_gens[k, j] = micro_img_gens
    end # filling up the blocks to the left
  end # going through the domain blocks
  @show keys(macro_img_gens)
  dom = self[i]
  cod = self[i-1]
  img_gens = elem_type(cod)[]
  for (macro_row_ind, macro_pr) in enumerate(canonical_projections(dom))
    @show macro_row_ind
    macro_dom = codomain(macro_pr)
    @show ngens(macro_dom)
    #for (micro_row_ind, micro_pr) in enumerate(canonical_projections(macro_dom))
      #micro_row_offset = 0
      #micro_dom = codomain(micro_pr)
      for (macro_gen_ind, v) in enumerate(gens(macro_dom))
        @show macro_gen_ind
        macro_img_gen = zero(cod) # initialize the result for this generator
        for (macro_col_ind, macro_inc) in enumerate(canonical_injections(cod))
          macro_cod = domain(macro_inc)
          micro_img_gen = zero(macro_cod)
          @show macro_col_ind
          @show haskey(macro_img_gens, (macro_row_ind, macro_col_ind))
          !haskey(macro_img_gens, (macro_row_ind, macro_col_ind)) && continue
          micro_img_gens = macro_img_gens[macro_row_ind, macro_col_ind]
          @show length(micro_img_gens)
          block_img_gen = micro_img_gens[macro_gen_ind]
          @show block_img_gen
          for (ind, v) in block_img_gen
            @show parent(v) === domain(canonical_injection(macro_cod, ind))
            @show codomain(canonical_injection(macro_cod, ind)) === cod
            micro_img_gen += canonical_injection(macro_cod, ind)(v)
          end
          macro_img_gen += macro_inc(micro_img_gen)
        end
        push!(img_gens, macro_img_gen)
      end
      #micro_row_offset += ngens(micro_dom)
    #end
  end
  return hom(dom, cod, img_gens)
end

function can_compute(fac::DirectImageMapFactory, self::AbsHyperComplex, p::Int, i::Tuple)
  return true
end

### The concrete struct
@attributes mutable struct DirectImageComplex{ChainType, MorphismType} <: AbsHyperComplex{ChainType, MorphismType} 
  internal_complex::HyperComplex{ChainType, MorphismType}

  function DirectImageComplex(pfctx::ToricCtxWithParams, K::AbsHyperComplex)
    T = elem_type(pfctx.R)
    chain_fac = DirectImageChainFactory(pfctx, K)
    map_fac = DirectImageMapFactory{FreeModuleHom{FreeMod{T}, FreeMod{T}, Nothing}}()

    internal_complex = HyperComplex(1, chain_fac, map_fac, [:chain])
    return new{FreeMod{T}, FreeModuleHom{FreeMod{T}, FreeMod{T}, Nothing}}(internal_complex)
  end
end

### Implementing the AbsHyperComplex interface via `underlying_complex`
underlying_complex(c::DirectImageComplex) = c.internal_complex

