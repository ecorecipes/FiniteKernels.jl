# Exceptions of FiniteKernels (ADR 0013). Every exception the package defines lives in this
# file, with its `showerror` method, and subtypes the root `FiniteKernelsError`. The module
# includes this file after `spaces.jl` and before every other file, because
# `SpaceMismatchError` has `FiniteSpace` fields.
#
# - Carry the offending axis / variable names in the fields and the message. Library code
#   never calls a bare `error("...")`.
# - Invalid arguments and keywords raise `ArgumentError`, not a type from this file (for
#   example `normalize` on a column that sums to zero, or `marginal` on an axis it cannot
#   keep).
# - A docstring names another package's type as a code span, never with `@ref`.

"""
    FiniteKernelsError

Abstract supertype of every exception that FiniteKernels defines:
[`InvalidAxisError`](@ref), [`KernelShapeError`](@ref), [`KernelEntryError`](@ref),
[`KernelNormalizationError`](@ref) and [`SpaceMismatchError`](@ref). It marks the
package that introduced an error, not a kind of failure; ADR 0013 also places
`MarkovCategories`' `UnboundGeneratorError` under it, since that package builds on
this one and has no root of its own. Invalid arguments and keywords raise Base's
`ArgumentError` instead, which is outside this root.

```jldoctest
julia> try
           FiniteAxis(:Rain, Symbol[])
       catch e
           e isa FiniteKernelsError
       end
true
```
"""
abstract type FiniteKernelsError <: Exception end

"""
    InvalidAxisError(name, msg)

Thrown when a [`FiniteAxis`](@ref) is constructed with empty or duplicate labels,
or when a label is looked up that the axis does not carry.
"""
struct InvalidAxisError <: FiniteKernelsError
    name::Symbol
    msg::String
end

function Base.showerror(io::IO, e::InvalidAxisError)
    return print(io, "InvalidAxisError: axis ", repr(e.name), ": ", e.msg)
end

"""
    KernelShapeError(msg, expected, got; name=nothing)

Thrown when a table does not have the shape required by its domain and codomain.
`expected` and `got` are the required and the actual sizes; `name` optionally
names the variable whose table was rejected.
"""
struct KernelShapeError <: FiniteKernelsError
    msg::String
    expected::Tuple
    got::Tuple
    name::Union{Nothing,Symbol}
end

function KernelShapeError(msg::AbstractString, expected::Tuple, got::Tuple;
                          name::Union{Nothing,Symbol}=nothing)
    return KernelShapeError(String(msg), expected, got, name)
end

_error_subject(name) = name === nothing ? "" : " in $(name)"

function Base.showerror(io::IO, e::KernelShapeError)
    return print(io, "KernelShapeError", _error_subject(e.name), ": ", e.msg,
                 " (expected size ", e.expected, ", got ", e.got, ")")
end

"""
    KernelNormalizationError(msg, max_deviation, atol; name=nothing)

Thrown when a kernel table is required to be normalised but some column does not
sum to one within `atol`. `max_deviation` is the largest `|sum - 1|` over the
columns; `name` optionally names the variable whose table was rejected. Named as
in SPEC section 54; the name also keeps this exception distinct from
`BayesianNetworkFormats.NotNormalizedError`, so that both packages can be used
together (ADR 0007).
"""
struct KernelNormalizationError <: FiniteKernelsError
    msg::String
    max_deviation::Float64
    atol::Float64
    name::Union{Nothing,Symbol}
end

function KernelNormalizationError(msg::AbstractString, max_deviation::Real, atol::Real;
                                  name::Union{Nothing,Symbol}=nothing)
    return KernelNormalizationError(String(msg), Float64(max_deviation), Float64(atol),
                                    name)
end

function Base.showerror(io::IO, e::KernelNormalizationError)
    return print(io, "KernelNormalizationError", _error_subject(e.name), ": ", e.msg,
                 " (maximum deviation from 1 is ", e.max_deviation, ", atol = ", e.atol,
                 ")")
end

"""
    KernelEntryError(msg, index, value; name=nothing)

Thrown when an entry of a kernel table is not a probability: negative (by more
than the tolerance `atol`), `NaN`, or infinite. `index` is the `CartesianIndex`
of the first offending entry in the internal `(codom axes..., dom axes...)`
layout and `value` is its value; `name` optionally names the variable whose
table was rejected. Nonnegativity is half of the definition of a morphism of
**FinStoch** (the other half is normalisation), so the constructor of
[`FiniteKernel`](@ref) and [`assert_normalized`](@ref) both check it (ADR 0007).
"""
struct KernelEntryError <: FiniteKernelsError
    msg::String
    index::CartesianIndex
    value::Real
    name::Union{Nothing,Symbol}
end

function KernelEntryError(msg::AbstractString, index::CartesianIndex, value::Real;
                          name::Union{Nothing,Symbol}=nothing)
    return KernelEntryError(String(msg), index, value, name)
end

function Base.showerror(io::IO, e::KernelEntryError)
    return print(io, "KernelEntryError", _error_subject(e.name), ": ", e.msg,
                 " (index ", Tuple(e.index), ", value ", e.value, ")")
end

"""
    SpaceMismatchError(operation, expected, got)

Thrown when two kernels or spaces are combined by `operation` but the spaces that
must agree (for example the codomain of `k` and the domain of `l` in
`compose_kernel(k, l)`) differ.
"""
struct SpaceMismatchError <: FiniteKernelsError
    operation::Symbol
    expected::FiniteSpace
    got::FiniteSpace
end

function Base.showerror(io::IO, e::SpaceMismatchError)
    return print(io, "SpaceMismatchError in ", e.operation, ": expected ", e.expected,
                 ", got ",
                 e.got)
end
