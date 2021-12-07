using ..Compologicircuits
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using Catlab.Theories
using Catlab.Syntax
using Catlab.GAT
using Catlab.Present
using Catlab.Programs
using Catlab.Graphics

B = Ob(FreeCartesianCategory, :B)
dup = mcopy(B)
I = id(B)
and = Hom(:AND, B⊗B, B)
or = Hom(:OR, B⊗B, B)
xor = Hom(:XOR, B⊗B,B)
not = Hom(:NOT, B,B)

to_diagram(x) = add_junctions!(to_wiring_diagram(x))

normal_form(x) = to_hom_expr(FreeCartesianCategory, to_diagram(x))


normal_form(dup⋅(dup⊗dup))
expr1 = dup⋅(dup⊗dup)
head(args(expr1)[1]) == :mcopy

#returns set of all identical pairs of n length bool vectors
function all_match(n::Int)
    output = []
    for i in 0:(2^n)-1
        vect = .!Vector{Bool}(iszero.(digits(i, base=2, pad=n)))
        push!(output, [vect, vect])
    end
    return output
end

#binary vectors to int
function bivec_int(w)::Int
    output = 0
    v = Vector{Int}(w)    
    for i in 0:length(v)-1
        output += (v[i+1])*2^i
    end   
    return output
end

#brute force SAT algorithm, loops over all the possible inputs
#return true and first argument that gives true if sat., else returns false and the last argument
function brute_SAT(f::Circuit)
    sat = false
    i = 0
    dom = f.dom.n
    arr = Bool[]

    if !(f.codom == CircuitDom(1))
        error("circuit codomain needs to be 1!")
    else
        while (!sat)&&(i < 2^dom)
                arr = iszero.(digits(i, base=2, pad=dom))
                sat = f.impl(arr)[1]                
                i += 1
        end
        return (sat, arr)
    end
end

#Observation: if dup is never used then the circtuit has all possible outputs, hence satisfiable
#returns true if contains swap, otherwise return false TODO: add a case for swap
function vibe_check(expr)::Bool
    argss = args(expr)
    output = false
    headd = head(expr)
    
    if headd == :mcopy
        output = true
    elseif (headd == :generator)||(headd == :id)||(headd == :braid)||(headd == :pair)||
           (headd == :delete)||(headd == :proj1)||(headd == :proj2)
        output = false
    else
        for i in argss
            output = output||vibe_check(i)
        end
    end
    
    return output
end

#=examples
demo1 = (dup⊗dup)⋅(not⊗σ(B,B)⊗not)⋅(and⊗and)⋅and
demo2 = normal_form(demo1)
[brute_SAT(Impl(demo1)), brute_SAT(Impl(demo2)), dup_check(demo1), dup_check(demo2)]
=#

#=
struct Augmented_Circuit
    circ::Circuit
    sol::Vector{Vector{Vector{Bool}}} #array of type Vector{Vector{Vector{Bool}} matching input to output
end

aiNOT = Augmented_Circuit(iNOT, [ [[true],[true]], [[false],[false]] ])
aiAND = Augmented_Circuit(iAND, [ [[true, true],[true]], [[true, false],[false]], [[false, true],[false]], [[false, false],[false]]  ])
aiOR = Augmented_Circuit(iOR, [ [[true, true],[true]], [[true, false],[true]], [[false, true],[true]], [[false, false],[false]]  ])

#@instance CartesianCategory{CircuitDom, Augmented_Circuit} begin
    id(A::CircuitDom) = Augmented_Circuit(Circuit(A,A, x->x), all_match(n))
    dom(f::Augmented_Circuit) = f.circ.dom
    codom(f::Augmented_Circuit) = f.circ.codom

    # Circuit composition is just function composition
    compose(f::Augmented_Circuit, g::Augmented_Circuit) = begin
        @assert(f.circ.codom == f.circ.dom)
        output = []
        for i in f.sol
            push!(output, [i[1], g.sol[bivec_int(i[1])+1][2]])
        end
        return Augmented_Circuit(Circuit(f.circ.dom, g.circ.codom, x->g.impl(f.impl(x))), output)
    end

    otimes(A::CircuitDom, B::CircuitDom) = CircuitDom(A.n + B.n)
    # Monoidal product of circuits runs both circuits (TODO: run them in parallel to improve performance) and concatenates the results
    otimes(f::Augmented_Circuitt, g::Augmented_Circuit) = begin
        impl = x -> vcat(f.circ.impl(x[1:f.circ.dom.n]), g.circ.impl(x[f.circ.dom.n + 1:end]))
        output = []
        for i in g.sol
            for j in f.sol
                push!(output, [vcat(j[1],i[1]), vcat(j[2],i[2])] )
            end
        end
        return (Circuit(f.circ.dom.n + g.circ.dom.n, f.circ.codom.n + g.circ.codom.n, impl), output)
    end

    # A symmetric braiding just swaps the A and B parts of the input vector
    braid(A::CircuitDom, B::CircuitDom) = begin
        impl = x -> vcat(x[A.n+1:end], x[1:A.n])
        n = A.n + B.n
        Circuit(n, n, impl)
    end

    # Monoidal unit is a 0-dimensional bool space (i.e. a point or empty list)
    munit(::Type{CircuitDom}) = CircuitDom(0)

    # Stuff for Cartesian Category
    mcopy(A::CircuitDom) = Circuit(A.n, A.n+A.n, x->vcat(x,x))
    delete(A::CircuitDom) = Circuit(A.n, 0, x->Bool[])

    pair(f::Circuit, g::Circuit) = begin
        @assert(f.dom == g.dom)
        return Circuit(f.dom.n, f.codom.n+g.codom.n, x->vcat(f.impl(x), g.impl(x)))
    end
    proj1(A::CircuitDom, B::CircuitDom) = Circuit(A.n+B.n, A.n, x->x[1:A.n])
    proj2(A::CircuitDom, B::CircuitDom) = Circuit(A.n+B.n, B.n, x->x[A.n+1:end])
end
=#

