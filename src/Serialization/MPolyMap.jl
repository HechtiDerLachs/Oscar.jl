@register_serialization_type MPolyAnyMap uses_params

function type_params(phi::MPolyAnyMap)
  return Dict(
    :domain => domain(phi),
    :codomain => codomain(phi)
  )
end

function save_object(s::SerializerState, phi::MPolyAnyMap)
  save_data_dict(s) do
    save_object(s, _images(phi), :images)

    cm = coefficient_map(phi)
    if !isnothing(cm)
      save_object(s, cm, :coeff_map)
    end
  end
end

function load_object(s::DeserializerState, ::Type{<:MPolyAnyMap},
                     params::Dict) 
  d = params[:domain]
  c = params[:codomain]
  imgs = load_object(s, Vector, c, :images)

  if haskey(s, :coeff_map)
    throw("MPolyAnyMap with coefficient map serialization unimplemented")
  end
  return MPolyAnyMap(d, c, nothing, imgs)
end
