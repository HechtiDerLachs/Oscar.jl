# task record
struct ChartData{ST <: AbsAffineScheme, FT <: Ideal} <: ParallelTask
  chart::ST
  focus::FT
  function ChartData(U::AbsAffineScheme, I::Ideal)
    return new{typeof(U), typeof(I)}(U, I)
  end
end

function _compute(cd::ChartData)
  result = _is_smooth(cd.chart, focus=cd.focus)
  return result, result
end

function _is_smooth_parallel(X::AbsCoveredScheme)
  cd = ChartData[]
  for U in affine_charts(X)
    focus = ideal(OO(U), Oscar.has_decomposition_info(default_covering(X)) ? Oscar.decomposition_info(default_covering(X))[U] : [zero(OO(U))])
    push!(cd, ChartData(U, focus))
  end
  #result = _deploy_work(cd, workers())
  #return result
  result = wait_all_parallel(cd)
  #return result
  return all(a for (a, _) in result)
end

