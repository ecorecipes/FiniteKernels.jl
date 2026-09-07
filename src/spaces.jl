# Finite state spaces: labelled axes and their tensor products.

"""
    InvalidAxisError(name, msg)

Thrown when a [`FiniteAxis`](@ref) is constructed with empty or duplicate labels,
or when a label is looked up that the axis does not carry.
"""
struct InvalidAxisError <: Exception
    name::Symbol
    msg::String
end

function Base.showerror(io::IO, e::InvalidAxisError)
    return print(io, "InvalidAxisError: axis ", repr(e.name), ": ", e.msg)
end

"""
    FiniteAxis(name::Symbol, labels::Vector{Symbol})

One finite-valued variable: a name and an ordered list of unique state labels.
The label order is the axis order of every table indexed by this axis.

```jldoctest
julia> a = FiniteAxis(:Rain, [:yes, :no]);

julia> length(a), labels(a)
(2, [:yes, :no])
```
"""
struct FiniteAxis
    name::Symbol
    labels::Vector{Symbol}
    function FiniteAxis(name::Symbol, labels::AbstractVector{Symbol})
        isempty(labels) && throw(InvalidAxisError(name, "labels must be non-empty"))
        allunique(labels) ||
            throw(InvalidAxisError(name, "labels must be unique, got $(collect(labels))"))
        return new(name, collect(Symbol, labels))
    end
end

"""
    labels(a::FiniteAxis) -> Vector{Symbol}
    labels(X::FiniteSpace) -> Vector{Vector{Symbol}}

State labels of an axis, or of every axis of a space.
"""
labels(a::FiniteAxis) = a.labels

Base.length(a::FiniteAxis) = length(a.labels)
Base.:(==)(a::FiniteAxis, b::FiniteAxis) = a.name == b.name && a.labels == b.labels
Base.hash(a::FiniteAxis, h::UInt) = hash(a.labels, hash(a.name, hash(:FiniteAxis, h)))

"""
    label_index(a::FiniteAxis, label::Symbol) -> Int

Position of `label` on the axis; throws [`InvalidAxisError`](@ref) if absent.
"""
function label_index(a::FiniteAxis, label::Symbol)
    i = findfirst(==(label), a.labels)
    i === nothing &&
        throw(InvalidAxisError(a.name, "label $(repr(label)) not among $(a.labels)"))
    return i
end

"""
    FiniteSpace(axes::Vector{FiniteAxis})
    FiniteSpace(name::Symbol, labels::Vector{Symbol})
    FiniteSpace()

An object of **FinStoch**: a finite product of labelled axes. The empty space
`FiniteSpace()` is the monoidal unit, and [`tensor_space`](@ref) concatenates
axes. Axis names may repeat (as in `tensor_space(X, X)`). Equality and hashing
are structural.

```jldoctest
julia> X = FiniteSpace(:X, [:a, :b]); Y = FiniteSpace(:Y, [:u, :v, :w]);

julia> size(tensor_space(X, Y)), length(tensor_space(X, Y))
((2, 3), 6)

julia> isempty(FiniteSpace())
true
```
"""
struct FiniteSpace
    axes::Vector{FiniteAxis}
    FiniteSpace(axes::AbstractVector{FiniteAxis}) = new(collect(FiniteAxis, axes))
end

FiniteSpace() = FiniteSpace(FiniteAxis[])
FiniteSpace(a::FiniteAxis) = FiniteSpace([a])
function FiniteSpace(name::Symbol, labels::AbstractVector{Symbol})
    return FiniteSpace(FiniteAxis(name, labels))
end

"""
    factors(X::FiniteSpace) -> Vector{FiniteAxis}

The axes of a space, in order.
"""
factors(X::FiniteSpace) = X.axes

labels(X::FiniteSpace) = [a.labels for a in X.axes]

"""
    axis_names(X::FiniteSpace) -> Vector{Symbol}

Axis names of a space, in order.

```jldoctest
julia> axis_names(tensor_space(FiniteSpace(:A, [:a1, :a2]), FiniteSpace(:B, [:b1, :b2])))
2-element Vector{Symbol}:
 :A
 :B
```
"""
axis_names(X::FiniteSpace) = [a.name for a in X.axes]

"""
    names(X::FiniteSpace) -> Vector{Symbol}

Deprecated alias of [`axis_names`](@ref). `Base.names` means "the names exported
by a module", so a method of it on a state space is a surprise; the method is
retained (without a deprecation warning) only because downstream packages of the
ecosystem still call it. Use [`axis_names`](@ref) in new code.
"""
Base.names(X::FiniteSpace) = axis_names(X)

"""
    size(X::FiniteSpace) -> NTuple{N,Int}

Number of states of each axis; `()` for the unit space.
"""
Base.size(X::FiniteSpace) = Tuple(map(length, X.axes))

"""
    length(X::FiniteSpace) -> Int

Total number of joint states, `prod(size(X))`; `1` for the unit space.
"""
Base.length(X::FiniteSpace) = prod(size(X))

"""
    ndims(X::FiniteSpace) -> Int

Number of axes.
"""
Base.ndims(X::FiniteSpace) = length(X.axes)
Base.isempty(X::FiniteSpace) = isempty(X.axes)
Base.:(==)(X::FiniteSpace, Y::FiniteSpace) = X.axes == Y.axes
Base.hash(X::FiniteSpace, h::UInt) = hash(X.axes, hash(:FiniteSpace, h))

"""
    tensor_space(X::FiniteSpace, Y::FiniteSpace, Zs::FiniteSpace...) -> FiniteSpace

Concatenate the axes of the given spaces. This is the tensor product of objects
of **FinStoch** (`otimes(X, Y)` once `MarkovCategories.jl` is loaded); it is
strictly associative and strictly unital, with `FiniteSpace()` as the unit.
"""
tensor_space(X::FiniteSpace, Y::FiniteSpace) = FiniteSpace(vcat(X.axes, Y.axes))
function tensor_space(X::FiniteSpace, Y::FiniteSpace, Z::FiniteSpace,
                      Zs::FiniteSpace...)
    return tensor_space(tensor_space(X, Y), Z, Zs...)
end

"""
    state_index(X::FiniteSpace, labels...) -> CartesianIndex
    state_index(X::FiniteSpace, labels::Tuple) -> CartesianIndex

Cartesian index of the joint state with the given label on each axis.

```jldoctest
julia> X = tensor_space(FiniteSpace(:A, [:a1, :a2]), FiniteSpace(:B, [:b1, :b2, :b3]));

julia> state_index(X, :a2, :b3)
CartesianIndex(2, 3)
```
"""
function state_index(X::FiniteSpace, labels::Tuple)
    n = ndims(X)
    length(labels) == n ||
        throw(ArgumentError("expected $n labels for a space with $n axes, got $(length(labels))"))
    return CartesianIndex(ntuple(i -> label_index(X.axes[i], labels[i]), n))
end
state_index(X::FiniteSpace, labels::Symbol...) = state_index(X, labels)

"""
    joint_states(X::FiniteSpace) -> Vector{Tuple}

All joint states of `X` as label tuples, in column-major order (the first axis
varies fastest). This is the order of the flattened kernel tables and of
[`kernel_matrix`](@ref). The unit space has exactly one state, `()`.
"""
function joint_states(X::FiniteSpace)
    n = ndims(X)
    return vec([ntuple(i -> X.axes[i].labels[ci[i]], n) for ci in CartesianIndices(size(X))])
end
