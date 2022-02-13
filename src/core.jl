# ----------------------------------------------------------
# μKanren

# https://www.youtube.com/watch?v=U1khYtIw7gc&t=5728s

import Base: ≡, tail

struct ∅ end

isvar(x::T) where T = x isa Symbol

# ----------------------------------------------------------
# Cartesian Product
struct ×{α,β}
    l::α
    r::β
end

unit(α) = α × ()

×(iterable::α) where α = foldr(×, iterable)
×(x...) = ×(x)

car(x::×) = x.l
cdr(x::×) = x.r

Base.length(ρ::×{α,×}) where α = 1 + Base.length(ρ.r)
Base.length(ρ::×) = 2

Base.firstindex(ρ::×) = 1
Base.lastindex(ρ::×{α,×}) where α = length(ρ)
Base.lastindex(ρ::×{α,Tuple{}}) where α = 1
Base.lastindex(ρ::×) = 2

Base.iterate(ρ::×, θ=1) = θ > length(ρ) ? nothing : (ρ[θ], θ+1)

Base.getindex(ρ::×, i::α) where α <: Integer  = i <= 1 ? ρ.l : ρ.r[i .- 1]
Base.setindex!(ρ::×, val, i::α) where α <: Integer  = ρ.data[i...] = val

Base.BroadcastStyle(::Type{×}) = Broadcast.ArrayStyle{×}()

# x = ×(2:5...)
# x = 1 × x
# length(x)
# x[1]
# print.(x)

# ----------------------------------------------------------
# helpers
car(x) = x
car(x::Pair) = x.first
car(x::Tuple) = first(x)

cdr(x) = nothing
cdr(x::Pair) = x.second
cdr(x::Tuple) = tail(x)

# ----------------------------------------------------------

assp(_, ::Tuple{}) = ()
function assp(ƒ, ρ)
    ƒ(car(car(ρ))) && return car(ρ)
    cdr(ρ) !== nothing && assp(ƒ, cdr(ρ))
end

# function assp(ƒ, ρ)
    # car(ρ) === nothing && return false
    # ƒ(car(car(ρ))) && return car(ρ)
    # assp(ƒ, cdr(ρ))
# end

function walk(α, ρ)
    pr = assp(==(α), ρ)
    pr === nothing && return α
    cdr(pr) !== nothing && return walk(cdr(pr), ρ)
end

function occurs(x, y, z)
    y = walk(y, z)
    isvar(y) && return y == x
    y isa Pair && return occurs(x, car(y), z) || occurs(x, cdr(y), z)
    false
end

ext_s(x, v, s) = occurs(x,v,s) ? s : (x => v) => s

# occurs(1, (1 => 0), (0 => 1))
# occurs(0, (2 => 4), (1 => 3))
# ext_s(1, (1 => 0), (0 => 1))
# ext_s(0, (2 => 4), (1 => 3))

# ----------------------------------------------------------
