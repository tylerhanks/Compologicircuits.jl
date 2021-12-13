#=
This is just a copy of Compologicircuits.jl, the code is copy and pasted from that, except the struct Augmented_Circuit has
a new field called sol, the solutions of the circuit, or the graph of the boolean function implied by the circuits
sol is intended to have the type Vector{Vector{BitVector}}, as a vector of pairs [input, output], ordered as
binary numbers on the inputs in increasing order, for instance if f.circ.dom = 5 then 
f.sol[1][1] = [0,0,0,0,0], f.sol[2][1] = [0,0,0,0,1], f.sol[3][1] = [0,0,0,1,0], f.sol.[31][1] = [1,1,1,1,1]
Augmented_Circuit might be a useful structure
=#
include("Circuits.jl")
using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using Catlab.Theories
using Catlab.Syntax
using Catlab.GAT
using Catlab.Present
using Catlab.Programs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Catlab.Programs
using Catlab.WiringDiagrams
using ..Compologicircuits: CircuitDom, Circuit, iNOT, iAND, iOR, Impl, Circuits, show_diagram
import Catlab.Theories: id, compose, otimes, braid, munit, mcopy, delete, pair, proj1, proj2, ⊗, ⋅, σ

B = Ob(FreeCartesianCategory, :B)
dup = mcopy(B)
I = id(B)
and = Hom(:AND, B⊗B, B)
or = Hom(:OR, B⊗B, B)
xor = Hom(:XOR, B⊗B,B)
not = Hom(:NOT, B,B)

to_diagram(x) = add_junctions!(to_wiring_diagram(x))

normal_form(x) = to_hom_expr(FreeCartesianCategory, to_diagram(x))

#returns set of all identical pairs of n length bool vectors
function all_match(n::Int)
    output = []
    for i in 0:(2^n)-1
        vect = .!Vector{Bool}(iszero.(digits(i, base=2, pad=n)))
        push!(output, [vect, vect])
    end
    return output
end

function all_inputs(n::Int)
    output = Vector{Vector{Bool}}()
    for i in 0:(2^n)-1
        vect = .!Vector{Bool}(iszero.(digits(i, base=2, pad=n)))
        push!(output, vect)
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

struct Augmented_CircuitDom
    n::Int
end

struct Augmented_Circuit
    circ::Circuit
    sol::Vector{Vector{Vector{Bool}}} #array of type Vector{Vector{Vector{Bool}} matching input to output
end

Augmented_Circuit(c::Circuit) = begin
    n_ins = c.dom.n
    inputs = all_inputs(n_ins)
    truth_table = Vector{Vector{Vector{Bool}}}()
    for input in inputs
        output = c.impl(input)
        push!(truth_table, [input, output])
    end

    Augmented_Circuit(c, truth_table)
end

aiNOT = Augmented_Circuit(iNOT, [ [[false],[true]], [[true],[false]]])

aiAND = Augmented_Circuit(iAND, [ [[false, false],[false]], [[false, true],[false]], [[true, false],[false]], [[true, true],[true]]  ])

aiOR = Augmented_Circuit(iOR, [ [[false, false],[false]], [[false, true],[true]], [[true, false],[true]], [[true, true],[true]]  ])

#=@instance CartesianCategory{Augmented_CircuitDom, Augmented_Circuit} begin
    id(A::Augmented_CircuitDom) = Augmented_Circuit(Circuit(A,A, x->x), all_match(A.n))
    dom(f::Augmented_Circuit) = f.circ.dom
    codom(f::Augmented_Circuit) = f.circ.codom

    # Circuit composition is just function composition
    compose(f::Augmented_Circuit, g::Augmented_Circuit) = begin
        @assert(f.circ.codom == g.circ.dom)
        output = []
        for i in f.sol
            push!(output, [i[1], g.sol[bivec_int(i[2])+1][2]])
        end
        return Augmented_Circuit(Circuit(f.circ.dom, g.circ.codom, x->g.impl(f.impl(x))), output)
    end

    otimes(A::Augmented_CircuitDom, B::Augmented_CircuitDom) = Augmented_CircuitDom(A.n + B.n)
    # Monoidal product of circuits runs both circuits (TODO: run them in parallel to improve performance) and concatenates the results
    otimes(f::Augmented_Circuit, g::Augmented_Circuit) = begin
        impl = x -> vcat(f.circ.impl(x[1:f.circ.dom.n]), g.circ.impl(x[f.circ.dom.n + 1:end]))
        output = []
        for i in g.sol
            for j in f.sol
                push!(output, [vcat(j[1],i[1]), vcat(j[2],i[2])] )
            end
        end
        return Augmented_Circuit(Circuit(f.circ.dom.n + g.circ.dom.n, f.circ.codom.n + g.circ.codom.n, impl), output)
    end

    # A symmetric braiding just swaps the A and B parts of the input vector
    braid(A::Augmented_CircuitDom, B::Augmented_CircuitDom) = begin
        impl = x -> vcat(x[A.n+1:end], x[1:A.n])
        n = A.n + B.n
        output = all_match(n)
        output = map(v->[v[1],vcat(v[2][A.n+1:end], v[2][1:A.n])], output)      
        Augmented_Circuit(Circuit(n, n, impl), output)
    end

    # Monoidal unit is a 0-dimensional bool space (i.e. a point or empty list)
    munit(::Type{Augmented_CircuitDom}) = Augmented_CircuitDom(0)

    # Stuff for Cartesian Category
    mcopy(A::Augmented_CircuitDom) = begin
        output = all_match(A.n)
        output = map(v->[v[1],vcat(v[1],v[1])], output)
        return Augmented_Circuit(Circuit(A.n, A.n+A.n, x->vcat(x,x)), output)
    end
        
    delete(A::Augmented_CircuitDom) = Augmented_Circuit(Circuit(A.n, 0, x->Bool[]), all_match(0))

    pair(f::Augmented_Circuit, g::Augmented_Circuit) = begin
        @assert(f.circ.dom == g.circ.dom)
        output = []
        for i in f.sol
            push!(output, [i[1], vcat(i[2], g.sol[bivec_int(i[1])+1][2])])
        end
        return Augmented_Circuit(
            Circuit(f.cric.dom.n, f.circ.codom.n+g.circ.codom.n, x->vcat(f.circ.impl(x), g.circ.impl(x))), output)
            
    end
    proj1(A::Augmented_CircuitDom, B::Augmented_CircuitDom) = begin
        output = all_match(A.n+B.n)
        output = map(v->[v[1], v[2][1:A.n]], output)  
        return Augmented_Circuit(Circuit(A.n+B.n, A.n, x->x[1:A.n]), output)
    end
    proj2(A::Augmented_CircuitDom, B::Augmented_CircuitDom) = begin
        output = all_match(A.n+B.n)
        output = map(v->[v[1], v[2][A.n+1:end]], output)  
        return Augmented_Circuit(Circuit(A.n+B.n, B.n, x->x[A.n+1:end]), output)
    end
end

gens = Dict(
    Circuits[:B]=>Augmented_CircuitDom(1), 
    Circuits[:NOT]=>aiNOT, 
    Circuits[:AND]=>aiAND, 
    Circuits[:OR]=>aiOR
)

AImpl(expr) = functor((Augmented_CircuitDom, Augmented_Circuit), expr, generators=gens)=#
