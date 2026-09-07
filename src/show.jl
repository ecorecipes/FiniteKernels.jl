# Pretty printing.

function _space_string(X::FiniteSpace)
    return isempty(X) ? "I" :
           join((string(a.name, "{", join(a.labels, ","), "}") for a in X.axes), " ⊗ ")
end

function Base.show(io::IO, a::FiniteAxis)
    return print(io, "FiniteAxis(", repr(a.name), ", ", repr(a.labels), ")")
end
Base.show(io::IO, X::FiniteSpace) = print(io, "FiniteSpace(", _space_string(X), ")")

function Base.show(io::IO, k::FiniteKernel{T}) where {T}
    return print(io, "FiniteKernel{", T, "}(", _space_string(k.dom), " → ",
                 _space_string(k.codom), ")")
end

_joint_label(s::Tuple) = isempty(s) ? "()" : join(string.(s), ",")
_format(v::AbstractFloat) = string(round(v; digits=4))
_format(v::Real) = string(v)

function Base.show(io::IO, ::MIME"text/plain", k::FiniteKernel)
    show(io, k)
    M = kernel_matrix(k)
    nrow, ncol = size(M)
    if nrow * ncol > 400
        print(io, "\n  ", nrow, "×", ncol, " column-stochastic matrix")
        return
    end
    rows = _joint_label.(joint_states(k.codom))
    cols = _joint_label.(joint_states(k.dom))
    cells = [_format(M[i, j]) for i in 1:nrow, j in 1:ncol]
    rw = maximum(length, rows)
    widths = [max(length(cols[j]), maximum(length, view(cells, :, j))) for j in 1:ncol]
    print(io, "\n  ", " "^rw)
    for j in 1:ncol
        print(io, "  ", lpad(cols[j], widths[j]))
    end
    for i in 1:nrow
        print(io, "\n  ", rpad(rows[i], rw))
        for j in 1:ncol
            print(io, "  ", lpad(cells[i, j], widths[j]))
        end
    end
end
