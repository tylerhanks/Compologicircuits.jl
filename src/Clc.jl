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
import Catlab.Theories: dom, codom, id, compose, otimes, braid, munit, mcopy, delete, pair, proj1, proj2, ⊗, ⋅, σ

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
    XOR::Hom(B⊗B,B)
    FA::Hom(B⊗B⊗B,B⊗B)
end

# Functor from circuit diagrams to circuit implementations
gens = Dict(
    Circuits[:B]=>CircuitDom(1), 
    Circuits[:NOT]=>iNOT, 
    Circuits[:AND]=>iAND, 
    Circuits[:OR]=>iOR
)
Impl(expr) = functor((CircuitDom, Circuit), expr, generators=gens)

# Make some circuits

XOR = @program Circuits (x::B, y::B) begin
    xnandy = NOT(AND(x,y))
    xory = OR(x,y)
    return AND(xnandy,xory)
end

XOR_expr = to_hom_expr(FreeCartesianCategory, XOR)

iXOR = Impl(XOR_expr)

# Print XOR truth table

print_xor() = for i in Iterators.product([false, true], [false, true])
    input = collect(i)
    output = apply(iXOR, input)
    println("XOR on $input = $output")
end

full_adder = @program Circuits (x::B, y::B, cin::B) begin
    z = XOR(x,y)
    s = XOR(z,cin)
    cout = OR(AND(z,cin),AND(x,y))
    return (s, cout)
end

AND = to_wiring_diagram(Circuits[:AND])
NOT = to_wiring_diagram(Circuits[:NOT])
OR = to_wiring_diagram(Circuits[:OR])
total_full_adder = ocompose(full_adder, [XOR, XOR, AND, AND, OR])
iFA = Impl(to_hom_expr(FreeCartesianCategory, total_full_adder))

# Print Full Adder truth table

print_fa() = for i in Iterators.product([false, true], [false, true], [false, true])
    input = collect(i)
    output = apply(iFA, input)
    println("FA on $input = $output")
end

four_bit_adder = @program Circuits (cin::B, x1::B, x2::B, x3::B, x4::B, y1::B, y2::B, y3::B, y4::B) begin
    s1, cout1 = FA(x4,y4,cin)
    s2, cout2 = FA(x3,y3,cout1)
    s3, cout3 = FA(x2,y2,cout2)
    s4, cout = FA(x1,y1,cout3)
    return (cout, s4, s3, s2, s1)
end

total_four_bit_adder = ocompose(four_bit_adder, [total_full_adder, total_full_adder, total_full_adder, total_full_adder])
tfba_expr = to_hom_expr(FreeCartesianCategory, total_four_bit_adder)
i4bitadder = Impl(tfba_expr)

sum = apply(i4bitadder, 
    Bool[0,      #carry in
        0,1,1,1, #x
        0,1,1,0] #y
)

### Perform sub-circuit matching.
# The theory of directed wiring diagrams without outer ports.
@present TheoryNotOpenWiringDiagram(FreeSchema) begin
  Box::Ob
  (InPort, OutPort)::Ob
  Wire::Ob
  #(InWire, OutWire)::Ob
  PortValue::AttrType
  WireValue::AttrType
  BoxValue::AttrType
  BoxType::AttrType
  
  # To which in/out port is a wire attached?
  src::Hom(Wire, OutPort)
  tgt::Hom(Wire, InPort)

  in_port_type::Attr(InPort, PortValue)
  out_port_type::Attr(OutPort, PortValue)

  value::Attr(Box, BoxValue)
  box_type::Attr(Box, BoxType)
  wire_value::Attr(Wire, WireValue)
  #in_wire_value::Attr(InWire, WireValue)
  #out_wire_value::Attr(OutWire, WireValue)

  #in_tgt::Hom(InWire, InPort)
  #out_src::Hom(OutWire, OutPort)

  # To which box is an in/out port attached?
  in_port_box::Hom(InPort, Box)
  out_port_box::Hom(OutPort, Box)
end
F = @finfunctor TheoryNotOpenWiringDiagram DirectedWiringDiagrams.TheoryAttributedWiringDiagram begin
  Box => Box
  InPort => InPort
  OutPort => OutPort
  Wire => Wire
  #InWire => InWire
  #OutWire => OutWire

  PortValue => PortValue
  WireValue => WireValue
  BoxValue => BoxValue
  BoxType => BoxType

  src => src
  tgt => tgt

  in_port_type => in_port_type
  out_port_type => out_port_type

  value => value
  box_type => box_type
  wire_value => wire_value
  #in_wire_value => in_wire_value
  #out_wire_value => out_wire_value

  in_tgt => in_tgt
  out_src => out_src

  in_port_box => in_port_box
  out_port_box => out_port_box
end

@acset_type NOWDACSet(TheoryNotOpenWiringDiagram)

deltaF = DeltaMigration(F, NOWDACSet{Any, Any, Any, DataType})

cAND = deltaF(AND.diagram)
cOR = deltaF(OR.diagram)
cNOT = deltaF(NOT.diagram)
cXOR = deltaF(XOR.diagram)

## Pick out AND's in AND.
println("There are ", length(homomorphisms(cAND, cAND, monic=true)), " monic homomorphisms from AND to AND.")

## Pick out OR's in AND.
println("There are ", length(homomorphisms(cOR, cAND, monic=true)), " monic homomorphisms from OR to AND.")

# Pick out AND's in XOR.
println("There are ", length(homomorphisms(cAND, cXOR, monic=true)), " monic homomorphisms from AND to XOR.")

# Pick out circuits in total_four_bit_adder that can be replaced by FA's.
println("There are ", length(homomorphisms(deltaF(total_full_adder.diagram), deltaF(total_four_bit_adder.diagram), monic=true)), " monic homomorphisms from total_full_adder to total_four_bit_adder.")

#end
