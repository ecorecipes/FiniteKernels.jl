# Sequential composition, tensor product and identities of finite kernels.
# These functions carry the implementations; `MarkovCategories.jl` binds the
# Catlab generic functions (`compose`, `otimes`, `id`, ...) to them with an
# `@instance` of `ThMarkovCategory`.

"""
    compose_kernel(k::FiniteKernel, l::FiniteKernel, ms::FiniteKernel...) -> FiniteKernel

Sequential composition `X → Z` of `k : X → Y` and `l : Y → Z`, in diagrammatic
order (first `k`, then `l`): `(l ∘ k)(z | x) = Σ_y l(z | y) k(y | x)`.
Computed as the matrix product `kernel_matrix(l) * kernel_matrix(k)` and
reshaped back to the internal layout. Further kernels are folded on from the
left. Throws [`SpaceMismatchError`](@ref) unless `k.codom == l.dom`. Available
as `compose(k, l)` and `k ⋅ l` once `MarkovCategories.jl` is loaded.
"""
function compose_kernel(k::FiniteKernel, l::FiniteKernel)
    k.codom == l.dom || throw(SpaceMismatchError(:compose, k.codom, l.dom))
    M = kernel_matrix(l) * kernel_matrix(k)
    return _kernel(k.dom, l.codom, reshape(M, (size(l.codom)..., size(k.dom)...)))
end
function compose_kernel(k::FiniteKernel, l::FiniteKernel, m::FiniteKernel,
                        ms::FiniteKernel...)
    return compose_kernel(compose_kernel(k, l), m, ms...)
end

"""
    tensor_kernel(k::FiniteKernel, l::FiniteKernel, ms::FiniteKernel...) -> FiniteKernel

Parallel composition
`tensor_space(k.dom, l.dom) → tensor_space(k.codom, l.codom)`:
`(k ⊗ l)(y1, y2 | x1, x2) = k(y1 | x1) l(y2 | x2)`. The outer product of the two
tables is formed by broadcasting them against each other after reshaping, which
gives the axis order `(codom(k)..., codom(l)..., dom(k)..., dom(l)...)` directly,
with no `permutedims`. Further kernels are folded on from the left. Available as
`otimes(k, l)` and `k ⊗ l` once `MarkovCategories.jl` is loaded.
"""
function tensor_kernel(k::FiniteKernel{T}, l::FiniteKernel{S}) where {T,S}
    ck, dk = size(k.codom), size(k.dom)
    cl, dl = size(l.codom), size(l.dom)
    ones_(n) = ntuple(_ -> 1, n)
    A = reshape(k.table, (ck..., ones_(length(cl))..., dk..., ones_(length(dl))...))
    B = reshape(l.table, (ones_(length(ck))..., cl..., ones_(length(dk))..., dl...))
    # The rank of the reshaped tables is runtime data; asserting the element type
    # keeps it in the inferred return type (the rank cannot be).
    table = (A .* B)::Array{promote_type(T, S)}
    return _kernel(tensor_space(k.dom, l.dom), tensor_space(k.codom, l.codom), table)
end
function tensor_kernel(k::FiniteKernel, l::FiniteKernel, m::FiniteKernel,
                       ms::FiniteKernel...)
    return tensor_kernel(tensor_kernel(k, l), m, ms...)
end

"""
    identity_kernel(X::FiniteSpace) -> FiniteKernel

The identity kernel `X → X`, the diagonal of ones; `id(X)` once
`MarkovCategories.jl` is loaded.
"""
function identity_kernel(X::FiniteSpace)
    n = length(X)
    return _kernel(X, X, reshape(Matrix{Float64}(I, n, n), (size(X)..., size(X)...)))
end

"""
    marginal(k::FiniteKernel, keep) -> FiniteKernel

Marginalise the codomain of `k` onto the output axes listed in `keep` (axis
positions, in the order they should appear in the result), summing out the
others. `keep` may also be a single position or a single axis name (which must
be unique among the output axes).
"""
function marginal(k::FiniteKernel, keep::AbstractVector{<:Integer})
    nc = ndims(k.codom)
    all(i -> 1 <= i <= nc, keep) ||
        throw(ArgumentError("marginal: output axis positions $keep out of range 1:$nc"))
    allunique(keep) || throw(ArgumentError("marginal: output axis positions $keep repeat"))
    drop = setdiff(1:nc, keep)
    t = isempty(drop) ? k.table : dropdims(sum(k.table; dims=Tuple(drop)); dims=Tuple(drop))
    # After dropping, the surviving output axes are sorted(keep); permute to `keep` order.
    rank = invperm(sortperm(keep))
    m = length(keep)
    perm = (rank..., ntuple(i -> m + i, ndims(t) - m)...)
    return _kernel(k.dom, FiniteSpace(k.codom.axes[keep]), permutedims(t, perm))
end
marginal(k::FiniteKernel, keep::Integer) = marginal(k, [keep])
function marginal(k::FiniteKernel, name::Symbol)
    idx = findall(a -> a.name == name, k.codom.axes)
    length(idx) == 1 ||
        throw(ArgumentError("marginal: output axis $(repr(name)) must occur exactly once, found $(length(idx))"))
    return marginal(k, idx)
end

"""
    apply(k::FiniteKernel, x::FiniteKernel) -> FiniteKernel

Push a state `x : I → X` forward through `k : X → Y`; equals
`compose_kernel(x, k)`.
Throws [`SpaceMismatchError`](@ref) if `x` is not a state.
"""
function apply(k::FiniteKernel, x::FiniteKernel)
    isempty(x.dom) || throw(SpaceMismatchError(:apply, FiniteSpace(), x.dom))
    return compose_kernel(x, k)
end
