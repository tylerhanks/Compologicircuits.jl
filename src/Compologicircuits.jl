module Compologicircuits

using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using Catlab.Theories
using Catlab.GAT
using Catlab.Present
using Catlab.Programs
using Catlab.Graphics
import Catlab.Graphics: Graphviz
import Catlab.Theories: dom, codom, id, compose, otimes, braid, munit, ⊗, ⋅, σ

#helper function to show graphviz diagrams
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

B = Ob(FreeCartesianCategory, :B)
NAND = Hom(:NAND, B⊗B,B)
NAND = to_wiring_diagram(NAND)

@present Circuits(FreeCartesianCategory) begin
    B::Ob
    NAND::Hom(B⊗B,B)
end

NOT = @program Circuits (x::B) begin
    return NAND(x,x)
end

OR = (NOT ⊗ NOT) ⋅ NAND 

#=struct BoolSpace
    n::Int
end=#

struct CircuitDom
    n::Int
end

struct Circuit
    dom::CircuitDom
    codom::CircuitDom
    impl::Function #dom -> codom
end

@instance SymmetricMonoidalCategory{CircuitDom, Circuit} begin
    id(A::CircuitDom) = Circuit(A,A, x->x)
    dom(f::Circuit) = f.dom
    codom(f::Circuit) = f.codom

    compose(f::Circuit, g::Circuit) = begin
        @assert(f.codom == g.dom)
        return Circuit(f.dom, g.codom, x->g.impl(f.impl(x)))
    end

    otimes(A::CircuitDom, B::CircuitDom) = CircuitDom(A.n + B.n)
    otimes(f::Circuit, g::Circuit) = begin
        impl = x -> vcat(f.impl(x[1:f.dom.n]), g.impl(x[f.dom.n + 1:end]))
        return Circuit(CircuitDom(f.dom.n + g.dom.n), CircuitDom(f.codom.n + g.codom.n), impl)
    end

    braid(A::CircuitDom, B::CircuitDom) = begin
        impl = x -> vcat(x[A.n+1:end], x[1:A.n])
        n = A.n + B.n
        Circuit(CircuitDom(n), CircuitDom(n), impl)
    end

    munit(::Type{CircuitDom}) = CircuitDom(0)

end


#=OR = @program Circuits (a::B, b::B) begin

end=#



greet() = println("Hello!")

end