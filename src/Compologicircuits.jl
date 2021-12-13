module Compologicircuits

#include("Circuits.jl")
include("AugmentedCircuit.jl")
#include("SAT.jl")
#include("Clc.jl")

export CircuitDom, Circuit, show_diagram, apply, iNOT, iAND, iOR, Impl, Circuits,
Augmented_Circuit, aiAND, aiNOT, aiOR, AImpl

# Make some circuits

#=XOR = @program Circuits (x::B, y::B) begin
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
)=#

end