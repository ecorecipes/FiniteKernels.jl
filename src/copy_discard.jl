# Copy, discard and swap kernels: the comonoid structure of FinStoch.

"""
    copy_kernel(X::FiniteSpace) -> FiniteKernel

The copy map `Δ_X : X → X ⊗ X`, `Δ(x1, x2 | x) = [x1 = x][x2 = x]`.
Copying a state draws **once** and duplicates the outcome; see
[`tensor_kernel`](@ref) for two independent draws. Available as `mcopy(X)` and
`Δ(X)` once `MarkovCategories.jl` is loaded.
"""
function copy_kernel(X::FiniteSpace)
    n = length(X)
    M = zeros(Float64, n * n, n)
    for i in 1:n
        M[i + (i - 1) * n, i] = 1.0
    end
    return _kernel(X, tensor_space(X, X), reshape(M, (size(X)..., size(X)..., size(X)...)))
end

"""
    discard_kernel(X::FiniteSpace) -> FiniteKernel

The discard map `!_X : X → I`, the table of ones. Available as `delete(X)` and
`◊(X)` once `MarkovCategories.jl` is loaded.
"""
discard_kernel(X::FiniteSpace) = _kernel(X, FiniteSpace(), ones(Float64, size(X)))

"""
    swap_kernel(X::FiniteSpace, Y::FiniteSpace) -> FiniteKernel

The symmetry `σ_{X,Y} : X ⊗ Y → Y ⊗ X`. Available as `braid(X, Y)` and
`σ(X, Y)` once `MarkovCategories.jl` is loaded.
"""
function swap_kernel(X::FiniteSpace, Y::FiniteSpace)
    nx, ny = length(X), length(Y)
    M = zeros(Float64, ny * nx, nx * ny)
    for x in 1:nx, y in 1:ny
        # codomain (Y, X) flat index y + (x-1)ny; domain (X, Y) flat index x + (y-1)nx
        M[y + (x - 1) * ny, x + (y - 1) * nx] = 1.0
    end
    return _kernel(tensor_space(X, Y), tensor_space(Y, X),
                   reshape(M, (size(Y)..., size(X)..., size(X)..., size(Y)...)))
end
