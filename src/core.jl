# ----------------------------------------------------------
# μKanren

# https://www.youtube.com/watch?v=U1khYtIw7gc&t=5728s

import Base: tail

# ----------------------------------------------------------
# helpers

car(x) = x
car(x::Tuple) = first(x)

cdr(x) = ()
cdr(x::Tuple) = tail(x)
# cdr(x::Tuple{Int,β}) where β = first(tail(x))
isvar(x) = false
isvar(x::Int64) = true

# ----------------------------------------------------------
# miniKanren

assp(ƒ, t::Tuple{Int,β}) where β = ƒ(first(t)) ? t : nothing
assp(ƒ, t::Tuple{}) = nothing
function assp(ƒ,ρ)
    ƒ(car(car(ρ))) && return car(ρ)
    assp(ƒ, cdr(ρ))
end

walk(α::Tuple{β},ρ) where β = walk(car(α),ρ)
function walk(α,ρ)
    pr = assp(==(α), ρ)
    pr ≡ nothing && return α
    return walk(cdr(pr), ρ)
end

function occurs(α, β, ρ)
    β = walk(β,ρ)
    isvar(β) && return β == α
    β isa Tuple && return occurs(α, car(β), ρ) || occurs(α, cdr(β), ρ)
    false
end

ext_s(α,β,ρ::Tuple{Int,θ}) where θ = occurs(α,β,ρ) ? false : ((α,β),ρ)
ext_s(α,β,ρ) = occurs(α,β,ρ) ? false : ((α,β),ρ...)

w_unify(α,β,ρ) = false
w_unify(α::Tuple,β::Tuple,ρ) = unify(cdr(α), cdr(β), unify(car(α), car(β), ρ))

function unify(α,β,ρ)
    α = walk(α,ρ)
    β = walk(β,ρ)
    α == β && return ρ
    isvar(α) && return ext_s(α,β,ρ)
    isvar(β) && return unify(β,α,ρ)
    w_unify(α,β,ρ)
end

# function eq(α,β)
#     (ρ,c) -> begin
#         o = unify(α,β,ρ)
#         o == false ? () : (o, c)
#     end
# end

function ≣(α,β)
    ρ -> begin
        o = unify(α,β,car(ρ))
        o == false ? () : (o, cdr(ρ))
    end
end

# app(::Bool,β) = β
app(α::Tuple{},β)  = β
app(α::Tuple,β)  = (α,β)
app(α::Function,β) = () -> app(β,α())

app((),(1,2))
app((1,2),(1,2))

bind(::Tuple{}, _) = ()
bind(α::Tuple,β) = app(β(car(α)), bind(cdr(α), β))
bind(α::Function,β) = () -> bind(α(), β)

∨(ƒ,g) = ρ -> app(ƒ(ρ), g(ρ))
∧(ƒ,g) = ρ -> bind(ƒ(ρ), g)

turtles(x) = state -> () -> ((x ≣ :turtle) ∨ turtles(x))(state)
cats(x) = state -> () -> (cats(x) ∨ (x ≣ :cats))(state)
torc(x) = state -> () -> (turtles(x) ∧ cats(x))(state)
turtles(5)(((),1))()

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


fresh(f::Function) = begin
    (st) -> begin
        (bindings,count) = st
        goal = f(count)
        st = (bindings,count+1)
        goal(st)
    end
end

fresh(f::Function,n) = begin
    (sc) -> begin
        (bindings,count) = sc
        vars = [i for i=count:count+(n-1)]
        goal = f(vars...)
        sc = (bindings,count+n)
        goal(sc)
    end
end

(eq(((:cat,0),1), ((:cat,:tiger),:turtle)) ∨ eq((:cat,0), (:cat,:tiger)))(((),2))
eq(((:cat,0),1), ((:cat,:tiger),:turtle))(((),2))

walk(0, ((3,:cat), (2,3), (1,2), (0,1)))
occurs(1,(1, 0),(0, 1))
occurs(0, (2, 4), (1, 3))
ext_s(1, (1, 0), ((0, 1)))
ext_s(0, (2, 4), ((1, 3)))
ext_s(0, 2, ((1, 3)))

# ----------------------------------------------------------


f(x,y) = (x^3)*y + (y^3)*x
f(x,k) = 

f(10,?) = 200
