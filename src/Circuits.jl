using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using Catlab.Theories
using Catlab.Syntax
using Catlab.GAT
using Catlab.Present
using Catlab.Programs
using Catlab.Graphics
import Catlab.Graphics: Graphviz
import Catlab.Theories: dom, codom, id, compose, otimes, braid, munit, mcopy, delete, pair, proj1, proj2, ⊗, ⋅, σ

#export CircuitDom, Circuit, show_diagram, apply, iNOT, iAND, iOR, Impl, Circuits


# Helper function to show graphviz diagrams
show_diagram(d::WiringDiagram) = to_graphviz(
    add_junctions(d),
    orientation=LeftToRight,
    labels=false, label_attr=:xlabel,
    node_attrs=Graphviz.Attributes(
        :fontname => "Courier",
    ),
    edge_attrs=Graphviz.Attributes(
        :fontname => "Courier",
    )
)

# The skeleton of n-dimensional bool spaces which are the input/output types of logic circuits
struct CircuitDom
    n::Int
end

# Implement a logic circuit as a function from Vector{Bool} to Vector{Bool}
struct Circuit
    dom::CircuitDom
    codom::CircuitDom
    impl::Function # Vector{Bool} of size dom -> Vector{Bool} of size codom
end

# Convenience constructor
Circuit(nins::Int, nouts::Int, impl) = Circuit(CircuitDom(nins), CircuitDom(nouts), impl)

# Apply a circuit to the specified input vector
apply(circuit::Circuit, input::Vector{Bool})::Vector{Bool} = circuit.impl(input)

# Basic logic gate implementations
iNOT = Circuit(1, 1, x->map(b->!b, x))

iAND = Circuit(2, 1, x->[x[1] && x[2]])

iOR = Circuit(2, 1, x->[x[1] || x[2]])

#iδ = Circuit(1, 2, x->[x[1], x[1]])

# Make circuits compositional by implementing them as an SMC instance
@instance CartesianCategory{CircuitDom, Circuit} begin
    id(A::CircuitDom) = Circuit(A,A, x->x)
    dom(f::Circuit) = f.dom
    codom(f::Circuit) = f.codom

    # Circuit composition is just function composition
    compose(f::Circuit, g::Circuit) = begin
        @assert(f.codom == g.dom)
        return Circuit(f.dom, g.codom, x->g.impl(f.impl(x)))
    end

    otimes(A::CircuitDom, B::CircuitDom) = CircuitDom(A.n + B.n)
    # Monoidal product of circuits runs both circuits (TODO: run them in parallel to improve performance) and concatenates the results
    otimes(f::Circuit, g::Circuit) = begin
        impl = x -> vcat(f.impl(x[1:f.dom.n]), g.impl(x[f.dom.n + 1:end]))
        return Circuit(f.dom.n + g.dom.n, f.codom.n + g.codom.n, impl)
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

# Syntactic representation of logic circuits

@present Circuits(FreeCartesianCategory) begin
    B::Ob
    NOT::Hom(B,B)
    AND::Hom(B⊗B,B)
    OR::Hom(B⊗B,B)
    #XOR::Hom(B⊗B,B)
    #FA::Hom(B⊗B⊗B,B⊗B)
end

# Functor from circuit diagrams to circuit implementations
gens = Dict(
    Circuits[:B]=>CircuitDom(1), 
    Circuits[:NOT]=>iNOT, 
    Circuits[:AND]=>iAND, 
    Circuits[:OR]=>iOR
)
Impl(expr) = functor((CircuitDom, Circuit), expr, generators=gens)