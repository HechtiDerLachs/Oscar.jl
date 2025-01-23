@register_serialization_type MPolyAnyMap

function type_params(phi::MPolyAnyMap{S, T, U, V}) where {S, T, U, V}
  return MPolyAnyMap, Dict(
    :domain => (S, domain(phi)),
    :codomain => (T, codomain(phi))
  )
end

function save_object(s::SerializerState{T}, phi::MPolyAnyMap) where {T}
  save_data_dict(s) do
    save_object(s, _images(phi), :images)

    cm = coefficient_map(phi)

    @req _check_whether_this_is_admissible_serialization(typeof(cm), T) "the type of the coefficient map is not supported for long term storage"
    if !isnothing(cm)
      save_object(s, cm, :coeff_map)
    end
  end
end



_check_whether_this_is_admissible_serialization(::Type{CMType}, ::Type{SerializeParam}) where {CMType, SerializeParam <: OscarSerializer} = false
_check_whether_this_is_admissible_serialization(::Type{Nothing}, ::Type{SerializeParam}) where {SerializeParam <: OscarSerializer} = true
# TODO This list can be extended for more types of coefficient maps if needed
_check_whether_this_is_admissible_serialization(::Type{CMType}, ::Type{SerializeParam}) where {CMType, SerializeParam <: IPCSerializer} = true
_check_whether_this_is_admissible_serialization(::Type{Nothing}, ::Type{SerializeParam}) where {SerializeParam <: IPCSerializer} = true

function load_object(s::DeserializerState,
                     ::Type{<:MPolyAnyMap},
                     params::Dict) 
  d = params[:domain]
  c = params[:codomain]
  T = elem_type(c)
  imgs = load_object(s, Vector{T}, c, :images)

  if haskey(s, :coeff_map)
    return hom(d, c, load_object(s, :coeff_map), img_gens)
  end
  return MPolyAnyMap(d, c, nothing, imgs)
end
