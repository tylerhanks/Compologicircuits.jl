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
using MLStyle
#using ..Compologicircuits: CircuitDom, Circuit, iNOT, iAND, iOR, Impl, Circuits, tfba_expr, show_diagram
#using PicoSAT
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

brute_SAT(expr) = brute_SAT(Impl(expr))

#if dup is never used then the circtuit has all possible outputs, hence satisfiable
#returns true if contains dup, otherwise return false
function dup_check(expr)::Bool
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
            output = output||dup_check(i)
        end
    end
    
    return output
end

vibe_check(expr::FreeCartesianCategory.Hom)::Bool =
    @match head(expr) begin
        :mcopy => true
        :compose || :otimes => any(map(vibe_check, args(expr)))
        _ => false
    end

#replacing all instances of i and j in v with r, ignoring but keeping their signs
function copy_replace(v::Vector, i::Int, j::Int, r::Int)
    count = 1
    for a in v
        if (abs(a) == abs(i)) || (abs(a) == abs(j))
            v[count] = Int((abs(a)/a)*abs(r))
        end
        count += 1
    end
    return v
end

#replace all instances of n with m, and m with n, at the same time, ignoring but keeping signs
function braid_replace(v::Vector, n::Int, m::Int)
    count = 1
    for i in v
        if abs(i) == abs(n)
            v[count] = Int((abs(i)/i)*abs(m))
        elseif abs(i) == abs(m)
            v[count] = Int((abs(i)/i)*abs(n))
        end
        count += 1
    end
    return v
end

#replace all instances of n or -n with its negation
function not_replace(v::Vector, n::Int)
    count = 1
    for i in v
        if abs(i) == abs(n)
            v[count] = -Int((abs(i)/i)*abs(n))
        end
        count += 1
    end
    return v
end

function populate(v::Vector, anc::Int, offs::Int)
    output = []
    for i in v
        if i != anc
            push!(output, i)
        else
            push!(push!(output, i), offs)
        end
    end
    return output
end

#get rid of all instances of n in v, except the first
function cleanse(v::Vector, n::Int)
    output = []
    found = false
    for i in v
        if i != n
            push!(output, i)
        elseif !found
            found = true
            push!(output, i)
        end
    end
    return output
end

function splate(v::Vector, old::Int, new::Int)
    temp =[]
    for i in v
        if i != old
            push!(temp, i)
        else
            push!(temp, new)
        end
    end
    if v == temp
        return [v]
    else
        return [v, temp]
    end
end

#apply the expression expr to the current cnf
#only works for expressions with no nested otimes, every exression is expressible without nested otimes
function app_expr(expr, vars::Vector, cnf::Vector, begn::Int, ed::Int)
    #assuming that if head(expr) == :otimes then no argument of expr has :otimes head
    #vars = the boolean variables on each wire in order, must all be positive
    #begn = which wire to begin applying expr in vars
    #ed = the number of input wires of the previous application, might not always be relevant
    
    out_vars = vars #the vars on the wires after applying expr
    out_cnf = cnf #cnf after applying expr
    out_begn = begn #which wire to start the next application, should always be 1
    out_ed = ed #the input wires of expr, might not always be relevant
    new_var = maximum(vars)+1 #only needed to introduce a new variable for and, or gates
    heads = head(expr)
    argss = args(expr)
    
    if heads == :compose
        for i in reverse(argss)
            (out_vars, out_cnf, out_begn, out_ed) = app_expr(i, out_vars, out_cnf, out_begn, out_ed)
        end
    elseif heads == :otimes
        #@assert begn == 1
        (out_vars, out_cnf, out_begn, out_ed) = app_expr(argss[1], out_vars, out_cnf, out_begn, out_ed)
        for i in argss[2:end]
            v = app_expr(i, out_vars, out_cnf, out_ed+1, out_ed)
            out_ed += v[4]
            out_vars = v[1]
            out_cnf = v[2]
        end
    #assume to be Δ(B)
    elseif heads == :mcopy
        n = max(vars[begn], vars[begn+1])
        out_cnf = map(x -> copy_replace(x, vars[begn], vars[begn+1], n), out_cnf)
        out_vars[begn] = n
        out_vars = out_vars[1:end .!= begn+1]
        out_ed = 1
    #assumed to be σ(B,B)
    elseif heads == :braid
        n = vars[begn]
        m = vars[begn+1]
        out_vars[begn] = m
        out_vars[begn+1] = n
        out_cnf = map(x -> braid_replace(x, n, m), out_cnf)
        out_ed = 2
    elseif heads == :id
        out_ed = Impl(expr).dom.n
    elseif expr == not
        var = out_vars[begn]
        out_ed = 1
        out_cnf = map(x -> not_replace(x, var), out_cnf)
    elseif expr == and
        var = vars[begn]
        out_vars = vcat(vcat(vars[1:begn], [new_var]), vars[begn+1:end])
        temp = Vector{Int}[]
        out_cnf = map(x -> cleanse(x, var), out_cnf)
        out_cnf = map(x -> cleanse(x, -var), out_cnf)
        for v in out_cnf
            if (!(var in v) && !(-var in v))
                push!(temp, v)
            else
                temp_v = populate(v, -var, -new_var)
                temp_v = splate(temp_v, var, new_var)
                temp = vcat(temp, temp_v)
            end
        end
        out_cnf = temp
        out_ed = 2   
    elseif expr == or
        var = vars[begn]
        out_vars = vcat(vcat(vars[1:begn], [new_var]), vars[begn+1:end])
        temp = Vector{Int}[]
        out_cnf = map(x -> cleanse(x, var), out_cnf)
        out_cnf = map(x -> cleanse(x, -var), out_cnf)
        for v in out_cnf
            if (!(var in v) && !(-var in v))
                push!(temp, v)
            else
                temp_v = populate(v, var, new_var)
                temp_v = splate(temp_v, -var, -new_var)
                temp = vcat(temp, temp_v)
            end
        end
        out_cnf = temp
        out_ed = 2
    end
    
    return (out_vars, out_cnf, out_begn, out_ed)  
end

function expr_to_cnf(expr)
    @assert Impl(expr).codom.n == 1 
    return app_expr(normal_form(expr), [1], [[1]], 1, 0)
end

demo1 = (dup⊗dup)⋅(not⊗σ(B,B)⊗not)⋅(and⊗and)⋅and
#=demo_cnf = expr_to_cnf(demo1)[2]

PicoSAT.solve(demo_cnf)
time brute_SAT(demo1)=#
