# Finite stochastic kernels and their user-facing constructors.

"""
    DEFAULT_ATOL

The default absolute tolerance (`1e-8`) within which every column of a kernel table
must sum to one. It is the default of the `atol` keyword of [`FiniteKernel`](@ref),
[`cpt`](@ref), [`state`](@ref), [`is_normalized`](@ref) and
[`assert_normalized`](@ref); pass a larger `atol` for tables read from files that
store few significant digits.
"""
const DEFAULT_ATOL = 1e-8

"""
    KernelShapeError(msg, expected, got; name=nothing)

Thrown when a table does not have the shape required by its domain and codomain.
`expected` and `got` are the required and the actual sizes; `name` optionally
names the variable whose table was rejected.
"""
struct KernelShapeError <: Exception
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
struct KernelNormalizationError <: Exception
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
struct KernelEntryError <: Exception
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
struct SpaceMismatchError <: Exception
    operation::Symbol
    expected::FiniteSpace
    got::FiniteSpace
end

function Base.showerror(io::IO, e::SpaceMismatchError)
    return print(io, "SpaceMismatchError in ", e.operation, ": expected ", e.expected,
                 ", got ",
                 e.got)
end

"""
    FiniteKernel{T<:Real,N}(dom::FiniteSpace, codom::FiniteSpace, table::Array{T,N};
                            check=true, atol=DEFAULT_ATOL, name=nothing)
    FiniteKernel(dom, codom, table; check=true, atol=DEFAULT_ATOL, name=nothing)

A stochastic kernel (morphism of **FinStoch**) `dom → codom`.

The two type parameters are those of SPEC section 10.2: `T` is the element type
of the table and `N == ndims(codom) + ndims(dom)` its rank, so that the field
`table::Array{T,N}` is concretely typed. `N` is deduced from the table passed to
the constructor and rarely written by hand; the bare name `FiniteKernel` remains
usable in type annotations (it is the `UnionAll` over both parameters).

Internal axis convention (ADR 0002): `size(table) == (size(codom)..., size(dom)...)`,
that is, **output axes first, then input axes**. The entry
`table[y..., x...]` is `P(y | x)`. A kernel is normalised when the sum over the
output axes is one for every input index; a state `I → X` has an empty domain
and its table is just the distribution over `X`.

The constructor always checks the shape (throwing [`KernelShapeError`](@ref))
and, when `check=true`, the two halves of the **FinStoch** contract: every entry
is finite and nonnegative up to `-atol` (throwing [`KernelEntryError`](@ref)) and
every column sums to one within `atol` (throwing
[`KernelNormalizationError`](@ref)); `name` labels the variable in either error.
Pass `check=false` to skip *both* of those checks — the shape is still checked —
for example to build an unnormalised table deliberately and demonstrate that
discard is natural only for normalised kernels. The table is copied.

Prefer the user-facing constructors [`cpt`](@ref), [`state`](@ref),
[`point_mass`](@ref), [`uniform`](@ref) and [`deterministic`](@ref).
"""
struct FiniteKernel{T<:Real,N}
    dom::FiniteSpace
    codom::FiniteSpace
    table::Array{T,N}
    function FiniteKernel{T,N}(dom::FiniteSpace, codom::FiniteSpace, table::Array{T,N};
                               check::Bool=true, atol::Real=DEFAULT_ATOL,
                               name::Union{Nothing,Symbol}=nothing) where {T<:Real,N}
        expected = (size(codom)..., size(dom)...)
        size(table) == expected ||
            throw(KernelShapeError("kernel table must be laid out as (codom axes..., dom axes...)",
                                   expected, size(table); name))
        k = new{T,N}(dom, codom, table)
        check && assert_normalized(k; atol, name)
        return k
    end
end

function FiniteKernel{T}(dom::FiniteSpace, codom::FiniteSpace,
                         table::AbstractArray{<:Real,N}; check::Bool=true,
                         atol::Real=DEFAULT_ATOL,
                         name::Union{Nothing,Symbol}=nothing) where {T<:Real,N}
    copied = copyto!(Array{T,N}(undef, size(table)), table)
    return FiniteKernel{T,N}(dom, codom, copied; check, atol, name)
end

function FiniteKernel(dom::FiniteSpace, codom::FiniteSpace,
                      table::AbstractArray{T,N}; check::Bool=true,
                      atol::Real=DEFAULT_ATOL,
                      name::Union{Nothing,Symbol}=nothing) where {T<:Real,N}
    return FiniteKernel{T}(dom, codom, table; check, atol, name)
end

# Internal constructor for algebraic operations whose result is normalised by
# construction (or deliberately not checked); does not copy the table.
function _kernel(dom::FiniteSpace, codom::FiniteSpace,
                 table::Array{T,N}) where {T<:Real,N}
    return FiniteKernel{T,N}(dom, codom, table; check=false)
end

Base.eltype(::Type{<:FiniteKernel{T}}) where {T} = T
Base.eltype(::FiniteKernel{T}) where {T} = T

function Base.:(==)(k::FiniteKernel, l::FiniteKernel)
    return k.dom == l.dom && k.codom == l.codom && size(k.table) == size(l.table) &&
           k.table == l.table
end
function Base.hash(k::FiniteKernel, h::UInt)
    return hash(k.table, hash(k.codom, hash(k.dom, hash(:FiniteKernel, h))))
end

"""
    isapprox(k::FiniteKernel, l::FiniteKernel; kwargs...)

Approximate equality: identical domain and codomain and `isapprox` tables.
Keyword arguments (`atol`, `rtol`) are passed to `isapprox` on the tables.
"""
function Base.isapprox(k::FiniteKernel, l::FiniteKernel; kwargs...)
    return k.dom == l.dom && k.codom == l.codom && size(k.table) == size(l.table) &&
           isapprox(k.table, l.table; kwargs...)
end

# Normalisation
# -------------

# Sum of the table over its output axes, as an array indexed by the input axes.
function _column_sums(k::FiniteKernel)
    nc = ndims(k.codom)
    nc == 0 && return k.table
    dims = Tuple(1:nc)
    return dropdims(sum(k.table; dims); dims)
end

# First entry of the table that is not a probability, as
# `(index, value, reason)`, or `nothing` if every entry is finite and at least
# `-atol`. Small negative entries are tolerated because tables read from files
# or produced by floating-point arithmetic round below zero.
function _bad_entry(k::FiniteKernel, atol::Real)
    for i in CartesianIndices(k.table)
        v = k.table[i]
        isfinite(v) || return (i, v, "is not finite")
        v < -atol && return (i, v, "is negative")
    end
    return nothing
end

"""
    is_normalized(k::FiniteKernel; atol=DEFAULT_ATOL) -> Bool

Whether the sum over the output axes equals one (within `atol`) for every input
index. This is only half of the definition of a stochastic kernel; use
[`is_stochastic`](@ref) to require nonnegative entries as well.
"""
function is_normalized(k::FiniteKernel; atol::Real=DEFAULT_ATOL)
    return all(s -> abs(s - 1) <= atol, _column_sums(k))
end

"""
    is_stochastic(k::FiniteKernel; atol=DEFAULT_ATOL) -> Bool

Whether `k` is a morphism of **FinStoch**: every entry is finite and nonnegative
(up to `-atol`) *and* [`is_normalized`](@ref)`(k; atol)`. This is the predicate
`Stochastic := Nonneg ∧ Normalised` of the Lean model in `proofs/`.
"""
function is_stochastic(k::FiniteKernel; atol::Real=DEFAULT_ATOL)
    return _bad_entry(k, atol) === nothing && is_normalized(k; atol)
end

"""
    assert_normalized(k::FiniteKernel; atol=DEFAULT_ATOL, name=nothing)

Check that `k` is a morphism of **FinStoch**, that is [`is_stochastic`](@ref)`(k; atol)`:
throw [`KernelEntryError`](@ref) at the first entry that is negative (by more
than `atol`), `NaN` or infinite, and [`KernelNormalizationError`](@ref) unless
[`is_normalized`](@ref)`(k; atol)`. `name` labels the variable in either error.
Returns `k`.
"""
function assert_normalized(k::FiniteKernel; atol::Real=DEFAULT_ATOL,
                           name::Union{Nothing,Symbol}=nothing)
    bad = _bad_entry(k, atol)
    if bad !== nothing
        i, v, reason = bad
        throw(KernelEntryError("entry of the kernel $(k.dom) → $(k.codom) $(reason); a stochastic kernel has finite nonnegative entries",
                               i, v; name))
    end
    sums = _column_sums(k)
    dev = isempty(sums) ? 0.0 : Float64(maximum(s -> abs(s - 1), sums))
    dev <= atol ||
        throw(KernelNormalizationError("kernel $(k.dom) → $(k.codom) is not normalised over its output axes",
                                       dev, atol; name))
    return k
end

# `normalize` cannot report a deviation from one or a tolerance, so it throws an
# `ArgumentError` (as `marginal` does for an impossible request) rather than a
# `KernelNormalizationError` with fabricated numbers; the message names the
# offending input index.
function _zero_column_error(k::FiniteKernel, i::CartesianIndex)
    return ArgumentError("normalize: the column of the kernel $(k.dom) → $(k.codom) at input index $(Tuple(i)) sums to zero, so it cannot be rescaled to a probability distribution")
end

"""
    normalize(k::FiniteKernel) -> FiniteKernel

Rescale each column (each input index) so that the output axes sum to one.
Throws an `ArgumentError` naming the input index if a column sums to zero.
"""
function normalize(k::FiniteKernel)
    nc = ndims(k.codom)
    if nc == 0
        i = findfirst(iszero, k.table)
        i === nothing || throw(_zero_column_error(k, CartesianIndex(i)))
        return _kernel(k.dom, k.codom, one.(k.table))
    end
    s = sum(k.table; dims=Tuple(1:nc))
    i = findfirst(iszero, s)
    i === nothing || throw(_zero_column_error(k, CartesianIndex(Tuple(i)[(nc + 1):end])))
    return _kernel(k.dom, k.codom, k.table ./ s)
end

# Matrix view and probabilities
# -----------------------------

"""
    kernel_matrix(k::FiniteKernel) -> Matrix

The kernel as a column-stochastic `length(codom) × length(dom)` matrix. Rows
and columns are ordered as [`joint_states`](@ref) of the codomain and domain.
Composition is `kernel_matrix(l) * kernel_matrix(k)` for `compose_kernel(k, l)`.
"""
kernel_matrix(k::FiniteKernel) = reshape(k.table, length(k.codom), length(k.dom))

_as_tuple(x::Symbol) = (x,)
_as_tuple(x::Tuple) = x

# Linear index of the multi-index `idx` in an array of size `dims`. The number
# of axes of a space is runtime data, so `state_index` cannot infer the rank of
# its `CartesianIndex` and `k.table[ci]` would infer `Any`; folding the strides
# by hand and asserting the `Int` result keeps `probability` type-stable.
function _linear_index(dims::Dims, idx)
    lin = 1
    stride = 1
    for (d, i) in zip(dims, idx)
        lin += (i - 1) * stride
        stride *= d
    end
    return lin
end

"""
    probability(k::FiniteKernel, y, x=()) -> Real

The entry `P(y | x)`, where `y` and `x` are label tuples (or single symbols for
one-axis spaces) on the codomain and domain.

```jldoctest
julia> X = FiniteSpace(:X, [:a, :b]); k = cpt(FiniteAxis[], FiniteAxis(:X, [:a, :b]), [0.3, 0.7]);

julia> probability(k, :b)
0.7
```
"""
function probability(k::FiniteKernel, y, x=())
    iy = state_index(k.codom, _as_tuple(y))
    ix = state_index(k.dom, _as_tuple(x))
    return k.table[_linear_index(size(k.table), (Tuple(iy)..., Tuple(ix)...))::Int]
end

# User-facing constructors
# ------------------------

"""
    cpt(parents::Vector{FiniteAxis}, child::FiniteAxis, table::AbstractArray;
        check=true, atol=DEFAULT_ATOL, name=nothing)

Build the kernel `parents → child` from a conditional probability table in the
SPEC layout: `size(table) == (length.(parents)..., length(child))`, normalised
over the **last** axis within `atol`. This is one of the two documented
conversions between the user layout and the internal outputs-first layout: the
child axis is moved to the front with a single `permutedims`. `name` labels the
variable in a [`KernelShapeError`](@ref) or [`KernelNormalizationError`](@ref).

```jldoctest
julia> A = FiniteAxis(:A, [:a0, :a1]); Y = FiniteAxis(:Y, [:y0, :y1]);

julia> k = cpt([A], Y, [0.9 0.1; 0.2 0.8]);

julia> probability(k, :y1, :a1)
0.8

julia> cpt(k) == [0.9 0.1; 0.2 0.8]
true
```
"""
function cpt(parents::AbstractVector{FiniteAxis}, child::FiniteAxis, table::AbstractArray;
             check::Bool=true, atol::Real=DEFAULT_ATOL,
             name::Union{Nothing,Symbol}=nothing)
    n = length(parents)
    expected = (map(length, parents)..., length(child))
    size(table) == expected ||
        throw(KernelShapeError("cpt table must be laid out as (parents..., child)",
                               expected, size(table); name))
    internal = permutedims(table, (n + 1, ntuple(identity, n)...))
    return FiniteKernel(FiniteSpace(collect(parents)), FiniteSpace(child), internal; check,
                        atol, name)
end
function cpt(parent::FiniteAxis, child::FiniteAxis, table::AbstractArray; kw...)
    return cpt([parent], child, table; kw...)
end
cpt(child::FiniteAxis, table::AbstractArray; kw...) = cpt(FiniteAxis[], child, table; kw...)

"""
    cpt(k::FiniteKernel) -> Array

The table of a kernel with a single output axis in the SPEC layout
`(parents..., child)`; the inverse of `cpt(parents, child, table)`.
"""
function cpt(k::FiniteKernel)
    ndims(k.codom) == 1 ||
        throw(KernelShapeError("cpt layout requires a single child axis in the codomain",
                               (1,), size(k.codom)))
    n = ndims(k.dom)
    return permutedims(k.table, (ntuple(i -> i + 1, n)..., 1))
end

"""
    state(X::FiniteSpace, probs::AbstractArray; check=true, atol=DEFAULT_ATOL, name=nothing)

A state `I → X`: a probability distribution over the joint states of `X`.
`probs` may be a vector of length `length(X)` (in [`joint_states`](@ref) order)
or an array of size `size(X)`; it must sum to one within `atol`. `name` labels
the variable in an error.
"""
function state(X::FiniteSpace, probs::AbstractArray{<:Real}; check::Bool=true,
               atol::Real=DEFAULT_ATOL, name::Union{Nothing,Symbol}=nothing)
    length(probs) == length(X) ||
        throw(KernelShapeError("state must have one probability per joint state", size(X),
                               size(probs); name))
    return FiniteKernel(FiniteSpace(), X, reshape(collect(probs), size(X)); check, atol,
                        name)
end

"""
    point_mass(X::FiniteSpace, labels...) -> FiniteKernel
    dirac(X::FiniteSpace, labels...) -> FiniteKernel

The deterministic state `I → X` concentrated on the joint state with the given
labels.
"""
function point_mass(X::FiniteSpace, labels::Symbol...)
    table = zeros(Float64, size(X))
    table[state_index(X, labels)] = 1.0
    return _kernel(FiniteSpace(), X, table)
end
point_mass(X::FiniteSpace, labels::Tuple) = point_mass(X, labels...)
const dirac = point_mass

"""
    uniform(X::FiniteSpace) -> FiniteKernel

The uniform state `I → X`.
"""
uniform(X::FiniteSpace) = _kernel(FiniteSpace(), X, fill(1 / length(X), size(X)))

"""
    deterministic(X::FiniteSpace, Y::FiniteSpace, f) -> FiniteKernel

The deterministic kernel `X → Y` induced by a function on labels. `f` is called
with one label per axis of `X` (`f(x1, x2, ...)`) and must return a label of
`Y` (a `Symbol` for a one-axis codomain, otherwise a tuple of labels).

```jldoctest
julia> X = FiniteSpace(:X, [:a, :b]); Y = FiniteSpace(:Y, [:u, :v]);

julia> k = deterministic(X, Y, x -> x == :a ? :u : :v);

julia> kernel_matrix(k)
2×2 Matrix{Float64}:
 1.0  0.0
 0.0  1.0
```
"""
function deterministic(X::FiniteSpace, Y::FiniteSpace, f)
    table = zeros(Float64, (size(Y)..., size(X)...))
    n = ndims(X)
    for ci in CartesianIndices(size(X))
        x = ntuple(i -> X.axes[i].labels[ci[i]], n)
        iy = state_index(Y, _as_tuple(f(x...)))
        table[CartesianIndex(Tuple(iy)..., Tuple(ci)...)] = 1.0
    end
    return _kernel(X, Y, table)
end

"""
    random_kernel([rng], X::FiniteSpace, Y::FiniteSpace) -> FiniteKernel

A random normalised kernel `X → Y` with strictly positive entries, for tests
and examples.
"""
function random_kernel(rng::AbstractRNG, X::FiniteSpace, Y::FiniteSpace)
    table = rand(rng, Float64, (size(Y)..., size(X)...))
    return normalize(_kernel(X, Y, table))
end
random_kernel(X::FiniteSpace, Y::FiniteSpace) = random_kernel(default_rng(), X, Y)
