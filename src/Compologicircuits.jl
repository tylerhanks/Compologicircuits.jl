module Compologicircuits

using Catlab.WiringDiagrams
using Catlab.CategoricalAlgebra
using Catlab.Theories
using Catlab.GAT
using Catlab.Present
using Catlab.Programs
using Catlab.Graphics
import Catlab.Graphics: Graphviz

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

struct CircuitDom
    val::Bool
end

struct Circuit
    impl::Function
end



#=OR = @program Circuits (a::B, b::B) begin

end=#



greet() = println("Hello!")

end