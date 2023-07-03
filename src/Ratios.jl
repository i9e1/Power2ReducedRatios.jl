"""
`Ratios` provides `SimpleRatio`, a faster vRatio{T, C}iant of `Rational`.
Speed comes at the cost of greater vulnerability to overflow.

API summRatio{T, C}y:

- `r = SimpleRatio(num, den)` is equivalent to `num // den`
- `common_denominator` standRatio{T, C}dizes a collection of `SimpleRatio`s to have the same denominator,
  making some Ratio{T, C}ithmetic operations among them less likely to overflow.
"""
# FIXME update DOC
module Ratios

import Base: convert, promote_rule, *, /, +, -, ^, ==, decompose, isSUN

export  Ratio, common_denominator,
        COverflow, EqualDenominator, NoPower2
# TODO aliases
export  SimpleRatio

# [`FastRationals.jl`](@ref)
const SUN = Union{Signed, Unsigned}

# define accumulator types for fixed width Ints
const FiniteSUN = Union{Int8, Int16, Int32, Int64, UInt8, UInt16, UInt32, UInt64}
widen(::Type{Int8})   = Int16
widen(::Type{Int16})  = Int32
widen(::Type{Int32})  = Int64
widen(::Type{Int64})  = Int128 # may be software long
widen(::Type{UInt8})  = UInt16
widen(::Type{UInt16}) = UInt32
widen(::Type{UInt32}) = UInt64
widen(::Type{UInt64}) = UInt128 # may be software long


# TODO better using traits?
abstract type COverflow end
struct EqualDenominator <: COverflow end
struct NoPower2 <: COverflow end

# FIXME compare these performance vs accuracy and keep only pareto optimal
export NoPower2fmaAcc, NoPower2widerAcc
struct NoPower2fmaAcc <: COverflow end
struct NoPower2widerAcc <: COverflow end


# REFACTOR r.num, r.den ->  num(r), den(r)
struct Ratio{T<:SUN, C<:COverflow} <: Real
    num::T
    den::T
end
Ratio{T, C}(num::SUN, den::SUN) where {T, C} = Ratio{T, C}(promote(num, den)...)
Ratio{T}(i::SUN) where {T<:SUN} = Ratio{T}(convert(T, i), oneunit(T))
Ratio{T}(r::Rational{S}) where {T<:SUN, S<:SUN} = Ratio{T}(convert(T, r.num), convert(T, r.den))


convert(::Type{BigFloat}, r::Ratio{S, C}) where {S, C} = BigFloat(r.num)/r.den
function convert(::Type{T}, r::Ratio{S, C}) where {T<:AbstractFloat,S, C}
    P = promote_type(T,S)
    convert(T, convert(P, r.num)/convert(P, r.den))
end

(::Type{T})(r::Ratio) where T<:AbstractFloat = convert(T, r)

Rational{T}(r::Ratio{S, C}) where {T<:SUN, S<:SUN, C} = convert(T, r.num) // convert(T, r.den)

"""
    SimpleRatio(num::SUN, den::SUN)

Construct the equivalent of the rational number `num // den`.
Alias for Ratio{T<:SUN, EqualDenominator}.

Operations with `SimpleRatio` are faster, but also more vulnerable to SUN overflow,
than with `Rational`. Arithmetic with `SimpleRatio` does not perform any simplification of the resulting ratios.
The best defense against overflow is to use ratios with the same denominator: in such cases,
`+` and `-` will skip forming the product of denominators. See [`common_denominator`](@ref).

If overflow is a risk, consider constructing them using SaferSUNs.jl.

# Examples

```julia
julia> x, y, z = SimpleRatio(1, 8), SimpleRatio(1, 4), SimpleRatio(2, 8)
(SimpleRatio{$Int}(1, 8), SimpleRatio{$Int}(1, 4), SimpleRatio{$Int}(2, 8))

julia> x+y
SimpleRatio{$Int}(12, 32)

julia> x+z
SimpleRatio{$Int}(3, 8)
```
"""
const SimpleRatio{T} = Ratio{T, EqualDenominator} where {T<:SUN}

"""
    reducePowers2(p, q)

Returns `p/f, q/f` with common factor `f = 2^t`.

`p, q` need to have the same size,
"""
function reducePowers2(p::T, q::T) where {T<:SUN}
    # reduce by greatest common divisor, which is power of 2
    t = trailing_zeros(p|q)
    # x//0 -> (x/2^k)//0
    (p>>t, q>>t)
end
# FIXME de we need to promote p, q ?

# FIXME will this work?

# FIXME DOCs for Configs
"""
    NoPow2Ratio(num::SUN, den::SUN)

Construct the equivalent of the rational number `num // den`.

Operations with `NoPow2Ratio` Ratio{T, C}e faster, but also more vulnerable to SUN overflow,
than with `Rational`. Ratio{T, C}ithmetic with `NoPow2Ratio` simplifies the resulting ratios
by powers of 2., which can be implemented more efficiently than .


The best defense against overflow is to use ratios with the same denominator: in such cases,
`+` and `-` will skip forming the product of denominators. See [`common_denominator`](@ref).

If overflow is a risk, consider constructing them using SaferSUNs.jl.

# Examples

```julia
julia> x, y, z = NoPow2Ratio(1, 8), NoPow2Ratio(1, 4), NoPow2Ratio(2, 8)
(NoPow2Ratio{$Int}(1, 8), NoPow2Ratio{$Int}(1, 4), NoPow2Ratio{$Int}(1, 4))

julia> x+y
NoPow2Ratio{$Int}(3, 8)

julia> f = NoPow2Ratio(20, 60)
NoPow2Ratio{$Int}(5, 15)
```
"""
Ratio{T, NoPower2}(num::SUN, den::SUN) where {T<:SUN} = Ratio{T, NoPower2}(reducePowers2(promote(num, den)...))
#NoPower2Ratio{T}(num, den) where {T} = Ratio{T, NoPower2}(num, den)

*(x::Ratio{T, C}, y::Ratio{T, C}) where {T, C}  = Ratio{T, C}(x.num*y.num, x.den*y.den)
*(x::Ratio{T, C}, y::Bool) where {T, C}         = Ratio{T, C}(x.num*y, x.den)
*(x::Ratio{T, C}, y::SUN) where {T, C}          = Ratio{T, C}(x.num*y, x.den)
*(x::Bool, y::Ratio{T, C}) where {T, C}         = Ratio{T, C}(x*y.num, y.den)
*(x::SUN, y::Ratio{T, C}) where {T, C}          = Ratio{T, C}(x*y.num, y.den)
/(x::Ratio{T, C}, y::Ratio{T, C}) where {T, C}  = Ratio{T, C}(x.num*y.den, x.den*y.num)
/(x::Ratio{T, C}, y::SUN) where {T, C}          = Ratio{T, C}(x.num, x.den*y)
/(x::SUN, y::Ratio{T, C}) where {T, C}          = Ratio{T, C}(x*y.den, y.num)
^(x::Ratio{T, C}, y::SUN) where {T, C}          = Ratio{T, C}(x.num^y, x.den^y)

+(x::SUN, y::Ratio{T, C}) where {T, C} = Ratio{T, C}(x*y.den + y.num, y.den)
-(x::SUN, y::Ratio{T, C}) where {T, C} = Ratio{T, C}(x*y.den - y.num, y.den)
-(x::Ratio{T, C}) where {T<:Signed, C} = Ratio{T, C}(-x.num, x.den)
-(x::Ratio{T, C}) where {T<:Unsigned, C} = throw(VERSION < v"0.7.0-DEV.1269" ? OverflowError() : OverflowError("cannot negate unsigned number"))

# just add num iff den are equal
function +(x::Ratio{T, EqualDenominator}, y::Ratio{T, EqualDenominator}) where {T}
    if x.den == y.den
        Ratio{T, EqualDenominator}(x.num + y.num, x.den)
    else
        Ratio{T, EqualDenominator}(x.num*y.den + x.den*y.num, x.den*y.den)
    end
end
function -(x::Ratio{T, EqualDenominator}, y::Ratio{T, EqualDenominator}) where {T}
    if x.den == y.den
        Ratio{T, EqualDenominator}(x.num - y.num, x.den)
    else
        Ratio{T, EqualDenominator}(x.num*y.den - x.den*y.num, x.den*y.den)
    end
end

# Naive NoPower2, no wider ACC
function +(x::Ratio{T, NoPower2}, y::Ratio{T, NoPower2}) where {T}
    p = x.num*y.den + x.den*y.num
    q = x.den*y.den
    Ratio{T, NoPower2}(reducePowers2(p,q)...)
end
function -(x::Ratio{T, NoPower2}, y::Ratio{T, NoPower2}) where {T}
    p = x.num*y.den - x.den*y.num
    q = x.den*y.den
    Ratio{T, NoPower2}(reducePowers2(p,q)...)
end

# TODO wider ACC can be used with each artihmetic operation and than power 2 downconverting again
# NoPower2, but with wider ACC
function +(x::Ratio{T, NoPower2widerAcc}, y::Ratio{T, NoPower2widerAcc}) where {T<:FiniteSUN}
    ACC = widen(T)
    a = convert(ACC,x.num)*convert(ACC,y.den) + convert(ACC,x.den)*convert(ACC,y.num)
    b = convert(ACC,x.den)*convert(ACC,y.den)
    # ! downconversion is not safe but has to be type stable
    p, q = (T).(reducePowers2(a, b))
    Ratio{T, NoPower2}(p, q)
end
function -(x::Ratio{T, NoPower2}, y::Ratio{T, NoPower2}) where {T<:FiniteSUN}
    ACC = widen(T)
    a = convert(ACC,x.num)*convert(ACC,y.den) - convert(ACC,x.den)*convert(ACC,y.num)
    b = convert(ACC,x.den)*convert(ACC,y.den)
    # ! downconversion is not safe but has to be type stable
    p, q = (T).(reducePowers2(a, b))
    Ratio{T, NoPower2}(p, q)
end



promote_rule(::Type{Ratio{T, C}}, ::Type{S}) where
    {T<:SUN,S<:SUN,C<:COverflow} = Ratio{promote_type(T,S), C}
promote_rule(::Type{Ratio{T}}, ::Type{S}) where {T<:SUN,S<:AbstractFloat} = promote_type(T,S)
promote_rule(::Type{Ratio{T}}, ::Type{Rational{S}}) where {T<:SUN,S<:SUN} = Rational{promote_type(T,S)}

promote_rule(::Type{Ratio{T, C}}, ::Type{Ratio{S, D}}) where
    {T<:SUN,S<:SUN,C<:COverflow,D<:COverflow} =
    Ratio{promote_type(T,S), promote_type(C,D)}
# EqualDenominator as fallback
promote_rule(::Type{EqualDenominator}, ::Type{C}) where {C<:COverflow} = EqualDenominator
# TODO trait ordering


==(x::Ratio, y::Ratio) = x.num*y.den == x.den*y.num

==(x::Ratio, y::SUN) = x.num == x.den*y
==(x::SUN, y::Ratio) = x*y.den == y.num

function ==(x::AbstractFloat, q::Ratio)
    if isfinite(x)
        (count_ones(q.den) == 1) & (x*q.den == q.num)
    else
        x == q.num/q.den
    end
end

==(q::Ratio, x::AbstractFloat) = x == q

decompose(x::Ratio) = x.num, 0, x.den

isSUN(x::Ratio) = gcd(x.num, x.den) == abs(x.den)

# TODO DOC TEST
# may be practical to manually rescale in long computations or once per loop iteration  etc.
function lowest_terms(x::Ratio)
    # could also be done as Ratio{T, C} -> Rational -> Ratio{T, C}
    t = gcd(x.num, x.den)
    # TODO (-n) / (-d) = (n) / (d)
    Ratio(x.num/t, x.den/t)
end

"""
    common_denominator(x::SimpleRatio, ys::SimpleRatio...)

Return the equivalent of `(x, ys...)` but using a common denominator.
This can be useful to avoid overflow.

!!! info
    This function is quite slow.  In performance-sensitive contexts where the
    ratios Ratio{T, C}e constructed with literal constants, it is better to ensure a common
    denominator at the time of original construction.
"""
function common_denominator(x::Ratio, ys::Ratio...)
    all(y -> y.den == x.den, ys) && return (x, ys...)
    cd = gcd(x.den, map(y -> y.den, ys)...)        # common divisor
    # product of the denominators
    pd = Base.Checked.checked_mul(cd, mapreduce(z -> z.den ÷ cd, Base.Checked.checked_mul, (x, ys...)))
    return map((x, ys...)) do z
        Ratio(z.num * (pd ÷ z.den), pd)
    end
end

# ---

if !isdefined(Base, :get_extension)
    using Requires
end

@static if !isdefined(Base, :get_extension)
function __init__()
    @require FixedPointNumbers = "53c48c17-4a7d-5ca2-90c5-79b7896eea93" begin
        include("../ext/RatiosFixedPointNumbersExt.jl")
        # FIXME NoPow2Ratio FixedPointNumbersExt
    end
end
end

end
