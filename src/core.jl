# ----------------------------------------------------------
# μKanren

# https://www.youtube.com/watch?v=U1khYtIw7gc&t=5728s

import Base: tail

struct ∅ end

isvar(x::T) where T = x isa Number

# ----------------------------------------------------------
# Cartesian Product struct
struct ×{α,β}
    l::α
    r::β
end

unit(α) = α × ()

×(iterable::α) where α = foldr(×, iterable)
×(x...) = ×(x)

car(x::×) = x.l
cdr(x::×) = x.r

Base.length(ρ::×{α,×{β,γ}}) where {α,β,γ} = 1 + Base.length(ρ.r)
Base.length(ρ::×) = 2

Base.firstindex(ρ::×) = 1
Base.lastindex(ρ::×{α,×{β,γ}}) where {α,β,γ} = length(ρ)
Base.lastindex(ρ::×{α,Tuple{}}) where α = 1
Base.lastindex(ρ::×) = 2

Base.getindex(ρ::×, i::α) where α <: Integer = i <= 1 ? ρ.l : ρ.r[i-1]
Base.getindex(ρ::×, r::α) where α <: AbstractRange = (r .|> σ -> ρ[σ])

Base.show(io::IO, ρ::×) = print(io, "(", string(ρ[begin])*" ", .*("(", string.(ρ[begin+1:end-1]), " ")..., ρ[end], repeat(")", length(ρ)-1))


# x = ×(2:5...)
# x = 1 × x
# length(x)
# x[1] = 5
# x[1:3] = [6,7,8]
# x
# print.(x)

# ----------------------------------------------------------
# helpers
car(x) = x
car(x::×) = x.l
car(x::Pair) = x.first
car(x::Tuple) = first(x)
car(x::α) where α <: AbstractArray = x[begin]

cdr(x) = false
cdr(x::×) = x.r
cdr(x::Pair) = x.second
cdr(x::Tuple) = tail(x)
cdr(x::Tuple{α,β}) where {α,β} = x[2]
cdr(x::α) where α <: AbstractArray = x[begin+1:end]

# ----------------------------------------------------------
# miniKanren

assp(_, ::Tuple{}) = false
assp(ƒ, t::Tuple{Int,β}) where β = ƒ(t[1]) && t

function assp(ƒ,ρ)
    ƒ(car(car(ρ))) && return car(ρ)
    assp(ƒ, cdr(ρ))
end

function walk(α,ρ)
    pr = assp(==(α), ρ)
    pr == false && return α
    return walk(cdr(pr), ρ)
end

function occurs(α, β, ρ)
    β = walk(β,ρ)
    println("β = $β")
    isvar(β) && return β == α
    β isa Tuple && return occurs(α, car(β), ρ) || occurs(α, cdr(β), ρ)
    false
end

ext_s(α,β,ρ::Tuple{Int,θ}) where θ = occurs(α,β,ρ) ? false : ((α,β),ρ)
ext_s(α,β,ρ) = occurs(α,β,ρ) ? false : ((α,β),ρ...)

function unify(α,β,ρ)
    α = walk(α,ρ)
    β = walk(β,ρ)
    α == β && return ρ
    isvar(α) && return ext_s(α,β,ρ)
    isvar(β) && return unify(β,α,ρ)
    α isa Tuple && β isa Tuple && return unify(car(α), car(β), unify(cdr(α), cdr(β), ρ))
    false
end

function eq(α,β)
    ρ -> begin
        o = unify(α,β,car(ρ))
        o == false ? () : (o, cdr(ρ))
    end
end
    
app(::Bool,β) = β
app(α,β) = () -> app(β,α())
app(α::Tuple,β)  = (car(α), app(β, cdr(α)))

bind(::Tuple{}, _) = ()
bind(α,β) = () -> bind(α(), β)
bind(α::Tuple, β) = app(β(car(α)), bind(cdr(α), β))

∨(ƒ, g) = α -> app(ƒ(α), g(α))
∧(ƒ, g) = α -> bind(ƒ(α), g)

ω(α) = γ -> () -> α(γ)

function call_fresh(ƒ)
    α -> begin
        ƒ(cdr(α))(car(α), cdr(α)+1)
    end
end

reify_name(n) = string("_.", Char(0x2080+n))

anyᵒ() = α -> condᵉ(α, anyᵒ(α))
alwaysᵒ() = anyᵒ(eq(false, false))

function mapᵒ(ƒ,ρ)
  ρ == () && return ()
  (ƒ(car(ρ)), mapo(ƒ, cdr(ρ)))
end

# ----------------------------------------------------------

function mapᵒ(ƒ,ρ)
    ρ == () && return ()
    (ƒ(car(ρ)), mapo(ƒ, cdr(ρ)))
end

macro Zzz(α)
    :(x -> () -> $(esc(α))(x))
  end
  
  macro conj_(g0, g...)
    if (isempty(g))
      return :(@Zzz($(esc(g0))))
    else
      local t = [:($(esc(gg))) for gg in g]
      quote
        @Zzz($(esc(g0))) ∧ @conj_($(t...))
      end
    end
  end
  
  macro disj_(g0, g...)
    if (isempty(g))
      return :(@Zzz($(esc(g0))))
    else
      local t = [:($(esc(gg))) for gg in g]
      quote
        @Zzz($(esc(g0))) ∨ @disj_($(t...))
      end
    end
  end
  
  macro conde(g...)
      local cc = [ begin
          if isa(gg, Expr)
              if gg.head == :tuple
                  [ :($(esc(a))) for a in gg.args ]
              else
                  [ :($(esc(gg))) ]
              end
          else
              [ :($(esc(gg))) ]
              #todo: add other types check, this is in case when gg is Symbol
          end
          end
      for gg in g ]
      local values = [ :(@conj_($(c...))) for c in cc ]
      :(@disj_($(values...)))
  end

# (eq(((:cat,0),1), ((:cat,:tiger),:turtle)) ∨ eq((:cat,0), (:cat,:tiger)))(((),2))
# eq(((:cat,0),1), ((:cat,:tiger),:turtle))(((),2))

# walk(0, ((3,:cat), (2,3), (1,2), (0,1)))
# occurs(1,(1, 0),(0, 1))
# occurs(0, (2, 4), (1, 3))
# ext_s(1, (1, 0), ((0, 1)))
# ext_s(0, (2, 4), ((1, 3)))
# ext_s(0, 2, ((1, 3)))

# ----------------------------------------------------------


f(x,y) = (x^3)*y + (y^3)*x
f(x,k) = 
Float16
f(10,?) = 200
