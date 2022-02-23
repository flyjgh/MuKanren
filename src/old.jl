# -------------------------------------------------------------------

import Base: map, bind, string, show, print, ≡, tail

# struct ∅ end

# ----------------------------------------------------------

# Cartesian Product struct
mutable struct ×{α,β}
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
struct var
    i
end

(==)(x::var, y::var) = x.i == y.i

car(x) = x[1]
cdr(x) = x[2:end]
cdr(x::Tuple) = tail(x)
cdr(p::Pair) = p.second

iscons(x) = x isa Pair && cdr(x) isa Pair

list() = ()
function list(vals...)
    vals[1] => list(vals[2:end]...)
end

# (define (var c) (vector c))
# (define (var? x) (vector? x))
# (define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

assp(_, ::Tuple{}) = ()
function assp(ƒ, p)
    car(p) == () && return ()
    ƒ(car(car(p))) && return car(p)
    assp(ƒ, cdr(p))
end

function walk(α, ρ)
    pr = assp(x -> α == x, ρ)
    α isa var && pr != () && return walk(cdr(pr), ρ)
    α
end

# (define (walk u s)
#   (let ((pr (and (var? u) (assp (λ (v) (var=? u v)) s))))
#     (if pr (walk (cdr pr) s) u)))

function occurs(x, y, z)
    y = walk(y, z)
    y isa var && return y == x
    y isa Pair && (occurs(x, car(y), z) || occurs(x, cdr(y), z))
end

ext_s(x, v, s) = occurs(x,v,s) ? s : (x => v) => s

# (define (ext - s x v s) `((, x . , v) . , s))

function unify(α, β, γ)
    α = walk(α, γ)
    β = walk(β, γ)
    α isa var && β isa var && α == β && return γ
    α isa var && return ext_s(α, β, γ)
    β isa var && return ext_s(β, α, γ)
    if α isa Pair && β isa Pair
        γ = unify(car(α), car(β), γ)
        γ != () && return unify(cdr(α), cdr(β), γ)
    else
        α == β && return γ
    end
    ()
end

unit = α -> α => ()

function ≡(α, β)
    x -> begin
        ρ = unify(α, β, car(x))
        ρ != () ? unit(Pair(ρ, cdr(x))) : ()
    end
end

# (define (≡ u v)
#   (λg (s/c)
#     (let ((s (unify u v (car s/c))))
#       (if s (unit `(, s . , (cdr s/c))) mzero))))

# (define (unit s/c) (cons s/c mzero))
# (define mzero '())

# (define (unify u v s)
#   (let ((u (walk u s)) (v (walk v s)))
#     (cond
#       ((and (var? u) (var? v) (var=? u v)) s)
#       ((var? u) (ext- s u v s))
#       ((var? v) (ext- s v u s))
#       ((and (pair? u) (pair? v))
#         (let ((s (unify (car u) (car v) s)))
#           (and s (unify (cdr u) (cdr v) s))))
#       (else (and (eqv? u v) s)))))

function call_fresh(ƒ)
    x -> begin
        if ƒ isa Expr
          ƒ = eval(ƒ)
        end
        ƒ(var(cdr(x)))(car(x) => cdr(x) + 1)
    end
end

# (define (call/fresh f )
#   (λg (s/c)
#     (let ((c (cdr s/c)))
#       ((f (var c)) `(, (car s/c) . , (+ c 1))))))

mplus(::Tuple{}, y) = y
mplus(x::Function, y) = () -> mplus(y, x())
mplus(x::Pair, y) = car(x) => mplus(y, cdr(x))


bind(::Tuple{}, _) = ()
bind(x::Function, y) = () -> bind(x(), y)
bind(x::Pair, y) = mplus(y(car(x)), bind(cdr(x), y))

∨(ƒ, g) = x -> mplus(ƒ(x), g(x))
∧(ƒ, g) = x -> bind(ƒ(x), g)

string(α::var) = string("#(", α.i, ")")
# string(v::Tuple{}) = Base.string("#(nil)")
print(io::IO, α::var)  = print(io, string(α))
# print(io::IO, v::Tuple{})  = print(io, string(v))
show(io::IO, α::var) = print(io, α)
# show(io::IO, v::Tuple{}) = print(io, v)

# (define (disj g1 g2) (λg (s/c) (mplus (g1 s/c) (g2 s/c))))
# (define (conj g1 g2) (λg (s/c) (bind (g1 s/c) g2)))

# (define (mplus $1 $2)
#   (cond
#     ((null? $1) $2)
#     ((procedure? $1) (λ$ () (mplus $2 ($1))))
#     (else (cons (car $1) (mplus (cdr $1) $2)))))

# (define (bind $ g)
#   (cond
#     ((null? $) mzero)
#     ((procedure? $) (λ$ () (bind ($) g)))
#     (else (mplus (g (car $)) (bind (cdr $) g)))))

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

macro fresh_helper(g0, vars...)
  if (isempty(vars))
    return :($(esc(g0)))
  else
    local vars0 = vars[1]
    if length(vars) > 1
      local vars1 = vars[2:end]
      local exp = :($(esc(Expr(:->, :($vars0), :(@fresh_helper($g0, $(vars1...)))))))
      quote
        call_fresh($exp)
      end
    else
      local exp2 = :($(esc(Expr(:->, vars0, g0))))
      return :( call_fresh($exp2) )
    end
  end
end

macro fresh(vars, g0, g...)
  if isempty(g)
    local c = begin
      if isa(vars, Symbol)
        [:($(esc(eval(QuoteNode(vars)))))]
      elseif isa(vars, Expr)
        [:($(esc(eval(isa(v, Symbol) ? QuoteNode(v) : v)))) for v in vars.args]
      else
        []
      end
    end
    #println(c)
    :(@fresh_helper($(esc(g0)), $(c...) ))
  else
    local glist = [:($(esc(gg))) for gg in g]
    :(@fresh($(esc(vars)), @conj_($(esc(g0)), $(glist...)) ) )
  end
end

fresh(f) = f(Var(gensym()))
fresh2(f) = f(Var(gensym()), Var(gensym()))
fresh3(f) = f(Var(gensym()), Var(gensym()), Var(gensym()))
freshn(n, f) = f([Var(gensym()) for i in 1:n ]...)

reify_name(n) = string("_.", n)

function map(ƒ::Function, p::Pair)
    p == () && return ()
    Pair(ƒ(car(p)), map(ƒ, cdr(p)))
end

function reify_s(α, β)
  length(n::Tuple{}) = 0
  length(p::Pair) = cdr(p) == () && car(p) == () ? 0 : (car(p) != () ? 1 : 1 + length(cdr(p)))
  α = walk(α, β)
  #println(β)
  α isa var && return (α => reify_name(length(β))) => β
  α isa Pair && return reify_s(cdr(α), reify_s(car(α), β))
  β
end


function walk✶(α, β)
  α = walk(α, β)
  α isa var && return α
  α isa var && return walk✶(car(α), β) => walk✶(cdr(α), β)
  α
end

mk_reify(x) = map(reify_state, x)

export reify_state, mk_reify


function reify_state(p::Pair)
  w = walk✶(var(0), car(p))
  walk✶(w, reify_s(w, ()))
end

call_empty_state(ƒ) = ƒ(() => 0)

function pull(s)
  #println(string("pull ", s))
  s isa Function ? pull(s()) : s
end

function takeall(s)
  s = pull(s)
  #println(s)
  s == () && return []
  [car(s), takeall(cdr(s))...]
end

function take(n, s)
  n == 0 &&  return []
  s = pull(s)
  s == () && return []
  [car(s), take(n - 1, cdr(s))...]
end

macro r(n, vars, g0, g...)
  #println("in r ", vars, " ", g0)
  local t = [:($(esc(gg))) for gg in g]
  :(mk_reify(take($n, call_empty_state(@fresh($(esc(vars)), $(esc(g0)), $(t...))))))
end

macro r✶(vars, g0, g...)
  local t = [:($(esc(gg))) for gg in g]
  :(mk_reify(takeall(call_empty_state(@fresh($(esc(vars)), $(esc(g0)), $(t...))))))
end

# -------------------------------------------------------------------

# function appendo(l, s, out)
#   conde((l == () && s == out),
#       @fresh((a,d,res),
#           (a => d) == l,
#           (a => res) == out,
#           appendo(d,s,res)))
# end


