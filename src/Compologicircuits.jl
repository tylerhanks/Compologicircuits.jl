#module Compologicircuits

using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using Catlab.Theories
using Catlab.Syntax
using Catlab.GAT
using Catlab.Present
using Catlab.Programs
using Catlab.Graphics
import Catlab.Graphics: Graphviz
import Catlab.Theories: dom, codom, id, compose, otimes, braid, munit, ⊗, ⋅, σ

# Helper function to show graphviz diagrams
show_diagram(d::WiringDiagram) = to_graphviz(d,
    orientation=LeftToRight,
    labels=false, label_attr=:xlabel,
    node_attrs=Graphviz.Attributes(
        :fontname => "Courier",
    ),
    edge_attrs=Graphviz.Attributes(
        :fontname => "Courier",
    )
)

# Syntactic representation of logic circuits
B = Ob(FreeCartesianCategory, :B)
NOT = Hom(:NOT, B, B)
AND = Hom(:AND, B⊗B, B)
OR = Hom(:OR, B⊗B, B)
δ = Hom(:δ, B, B⊗B)

@present Circuits(FreeSymmetricMonoidalCategory) begin
    B::Ob
    NOT::Hom(B,B)
    AND::Hom(B⊗B,B)
    OR::Hom(B⊗B,B)
    δ::Hom(B,B⊗B)
end

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

iδ = Circuit(1, 2, x->[x[1], x[1]])

# Make circuits compositional by implementing them as an SMC instance
@instance SymmetricMonoidalCategory{CircuitDom, Circuit} begin
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
end

# Functor from circuit diagrams to circuit implementations
gens = Dict(B=>CircuitDom(1), NOT=>iNOT, AND=>iAND, OR=>iOR, δ=>iδ)
Impl(expr) = functor((CircuitDom, Circuit), expr, generators=gens)

# Make some circuits
XOR = @program Circuits (x::B, y::B) begin
    x1, x2 = δ(x)
    y1, y2 = δ(y)
    xnandy = NOT(AND(x1,y1))
    xory = OR(x2,y2)
    return AND(xnandy,xory)
end

XOR_expr = to_hom_expr(FreeSymmetricMonoidalCategory, XOR)

#end