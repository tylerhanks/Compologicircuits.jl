using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Catlab.Programs
using Catlab.WiringDiagrams

draw(d::WiringDiagram) = to_graphviz(d,
  orientation=LeftToRight,
  labels=false, label_attr=:xlabel,
  node_attrs=Graphviz.Attributes(
    :fontname => "Courier",
  ),
  edge_attrs=Graphviz.Attributes(
    :fontname => "Courier",
  )
)

to_diagram(x) = add_junctions!(to_wiring_diagram(x))

normal_form(x) = to_hom_expr(FreeCartesianCategory, to_diagram(x))

#julia function composition
∘(f::Function, g::Function) = x->f(g(x)) 

@present Circuit(FreeCartesianCategory) begin
    Bool::Ob
    NOR::Hom(Bool⊗Bool, Bool)
    NOT::Hom(Bool, Bool)
    AND::Hom(Bool⊗Bool, Bool)
    OR::Hom(Bool⊗Bool, Bool)
    NAND::Hom(Bool⊗Bool, Bool)
end

B = Ob(FreeCartesianCategory, :Bool)
NAND = Hom(:NAND, B⊗B,B)
Dup = mcopy(B)
NOT = Hom(:NOT, B, B)
AND = Hom(:AND, B⊗B, B)
OR = Hom(:OR, B⊗B, B)
NOR = Hom(:NOR, B⊗B,B)

#function that turns basic gates into a boolean(vector) function
function gate_to_bool_func(gate::Catlab.Theories.FreeCartesianCategory.Hom{:generator})::Function
    if gate == NOT
        return NOT_EVAL(vec) = [!(vec[1])]
    elseif gate == AND
        return AND_EVAL(vec) = [vec[1]&&vec[2]]
    elseif gate == OR
        return OR_EVAL(vec) = [vec[1]||vec[2]]
    elseif gate == NAND
        return NAND_EVAL(vec) = [!(vec[1]&&vec[2])]
    elseif gate == NOR
        return NOR_EVAL(vec) = [!(vec[1]||vec[2])]
    end
end

#function that returns the number of input wires for basic gates
function gate_input(gate::Catlab.Theories.FreeCartesianCategory.Hom{:generator})::Int
    if gate == NOT
        return 1
    else 
        return 2
    end
end

#function that returns the number of input wires for circuits
function circ_input(circ::Catlab.Theories.FreeCartesianCategory.Hom)::Int
    
    input = 0
    argvec = args(circ)
    len = length(argvec)
    
    if head(circ) == :compose
        input = circ_input(argvec[1])
        
    elseif head(circ) == :otimes
            for arg in argvec
                input += circ_input(arg)
            end
            
    elseif head(circ) == :mcopy
        input = length(args(argvec[1]))
        
    elseif head(circ) == :braid
        input = length(args(argvec[1])) + length(args(argvec[2]))
    
    elseif head(circ) == :id
        input = length(args(argvec[1]))
        
    elseif head(circ) == :generator
        input = gate_input(circ)
    end
    
    return input
end

#function that returns the number of output wires for circuits
function circ_output(circ::Catlab.Theories.FreeCartesianCategory.Hom)::Int
    
    output = 0
    argvec = args(circ)
    len = length(argvec)
    
    if head(circ) == :compose
        output = circ_output(argvec[len])
        
    elseif head(circ) == :otimes
            for arg in argvec
                output += circ_output(arg)
            end
            
    elseif head(circ) == :mcopy
        output = 2*length(args(argvec[1]))
        
    elseif head(circ) == :braid
        output = length(args(argvec[1])) + length(args(argvec[2]))
    
    elseif head(circ) == :id
        output = length(args(argvec[1]))
        
    elseif head(circ) == :generator
        output = 1
    end
    
    return output
end

#function that turns circuits to their boolean(vector) functions
#careful! function returned from to_bool_func don't check for domains!
function to_bool_func(circ::Catlab.Theories.FreeCartesianCategory.Hom)::Function
    
    argvec = args(circ)
    len = length(argvec)
    
    
    if head(circ) == :compose
        g_comp = to_bool_func(argvec[1])
        for arg in argvec[2:len]
            g_comp = to_bool_func(arg)∘g_comp
        end
        return g_comp
    
    elseif head(circ) == :otimes
        g_prod = to_bool_func(argvec[1])
        for arg in argvec[2:len]
            arg_input_size = circ_input(arg)
            *(f₁::Function, f₂::Function) = 
                x->vcat(f₁(x[1:length(x) - arg_input_size]),f₂(x[length(x) - arg_input_size + 1:length(x)]))
            g_prod = g_prod*to_bool_func(arg)
        end
        return g_prod
    
    elseif head(circ) == :mcopy
        g_copy(x) = vcat(x,x)
        return g_copy
        
    elseif head(circ) == :braid
    copies = length(args(argvec[1]))
        function g_braid(x)
            return vcat(x[copies + 1:len], x[1:copies])
        end
        return g_braid
        
    elseif head(circ) == :id
    copies = length(args(argvec[1]))
        function g_id(x)
            if length(x) == copies
                return x
            else
                lenx = length(x)
                error("domain $copies not $lenx !")
            end
        end
        return g_id
    
    elseif head(circ) == :generator
        return gate_to_bool_func(circ) 
    end    
end

struct Bool_Circuit
    bool_circ::Catlab.Theories.FreeCartesianCategory.Hom
    bool_func::Function
    bool_dom::Int
    bool_cod::Int
    bool_diag
end

function Bool_Circuit(x::Catlab.Theories.FreeCartesianCategory.Hom)::Bool_Circuit
    return Bool_Circuit(x, to_bool_func(x), circ_input(x), circ_output(x), to_diagram(x))
end

#brute force SAT algorithm, loops over all the possible inputs
function brute_SAT(f::Bool_Circuit)
    sat = false
    i = 0
    dom = f.bool_dom
    arr = Bool[]

    if !(f.bool_cod == 1)
        error("circuit codomain needs to be 1!")
    else
        while (!sat)&&(i < 2^dom)
                arr = iszero.(digits(i, base=2, pad=dom))
                sat = f.bool_func(arr)[1]                
                i += 1
        end
        return (sat, arr)
    end
end
  
#TRYME
#demo = (Dup⊗Dup)⋅(NOT⊗σ(B,B)⊗NOT)⋅(AND⊗AND)
#demo_diagram = to_diagram(demo)
#draw(demo_diagram)
#demo_func = to_bool_func(demo)
#demo_func([true, true])
#demo_func([true, false])
#demo_func([false, true])
#demo_func([false, false])
#demo1 = demo⋅NOR
#demo2 = (Dup⊗Dup)⋅(demo⊗demo)⋅(AND⊗AND)
#demo3 = demo2⋅demo1
#demo_ult = (demo3 ⊗ demo3) ⋅ demo3
#demo_ult_circ = Bool_Circuit(demo_ult)
#draw(demo_ult_circ.bool_diag)
#brute_SAT(demo_ult_circ)
#unsatisfiable circuit
#demo_unsat = Dup ⋅ (NOT⊗id(B)) ⋅ NOR
#demo_unsat_circ = Bool_Circuit(demo_unsat)
#draw(demo_unsat_circ.bool_diag)
#brute_SAT(demo_unsat_circ)
#demo_unsat2 = demo_unsat ⋅ demo_unsat ⋅ demo_unsat
#demo_unsat2_circ = Bool_Circuit(demo_unsat2)
#brute_SAT(demo_unsat2_circ)
#demo_unsat_ult = (demo_unsat2⊗demo_unsat2⊗demo_unsat2⊗demo_unsat2)⋅(AND⊗NOR)⋅demo1 
#demo_unsat_ult_circ = Bool_Circuit(demo_unsat_ult)
#draw(demo_unsat_ult_circ.bool_diag)
#brute_SAT(demo_unsat_ult_circ)
