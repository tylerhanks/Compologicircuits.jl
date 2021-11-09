# Compologicircuits.jl: **C**ompositional **L**ogic **C**ircuits

## What is Compologicircuits.jl?
Compologicircuits.jl implements Logic Circuits using [Catlab](https://github.com/AlgebraicJulia/Catlab.jl). The project name "CompoLogiCircuits.jl” may be subject to change. The theory behind this project is covered in the Spivak's Seven Sketches in Compositionality under chapters 4.4 (SMCs), 2.1/4.\[1-9\] (String Diagrams), and 6.5 (Operads).

## Why Compologicircuits.jl?
Logic circuits are ubiquitous and are fundamental to software packages like Verilog. Specifying logic circuits is done essentially “by hand.” They do not allow for easy “sub-circuit composition.” 

Unlike existing solutions, our project lends itself easily to Applied Category Theory’s composition (in-sequence, in-parallel, hierarchically) to specify otherwise complex circuits with little code. We make the problem of defining certain types of logic circuits tractable where they previously were not. We can use knowledge of sub-circuits that we have seen before to solve SAT over our logic circuits more quickly.

## Goals
When our project is completed, we will be able to:

- Easily and elegantly define classes of tractable sub-circuits

- Express logic circuits as functors from the SMC of logic circuits to **Set**

- Compose logic circuits in-sequence, in-parallel and hierarchically.

## Data Structures, Algorithms, and Software Packages
We will eventually implement a SAT solver that runs on our logic circuit implementation. The algorithm we use for SAT solving remains to be picked. The main modules in Catlab of use to us are CategoricalAlgebra, WiringDiagrams, and Theories (as well as useful utilities like GAT, Present, Programs, Graphics, and Graphics.GraphViz.)
