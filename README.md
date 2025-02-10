# Circuit Minimization Algorithms

This repository contains a C program implementing an algorithm for synthesizing minimal circuits for 
completely-specified multi-output Boolean functions. The algorithm leverages redundancy addition and 
removal (RAR) and utilizes multi-input And-Inverter Graphs (MAIG) as its primary data structure.
This algorithm was developed as part of my Bachelor's thesis in Applied Mathematics at the 
National University of "Kyiv-Mohyla Academy." It was presented at the <a href="https://mathconf.ukma.edu.ua/Program2024.pdf">XII Ukrainian Scientific Conference of Young Mathematicians, 2024</a>.

The benchmarks used to evaluate the algorithms are taken from the set of 100 testcases of
<a href="https://github.com/alanminko/iwls2022-ls-contest">IWLS Programming Contest 2022</a>.

## Usage
To run the program, use the following command line: `./rewire-code [-IEGDFSTV <num>] <file.aig>` where:<br>
`-I <num>` - the number of iterations;<br>
`-E <num>` - the number of nodes to expand;<br>
`-G <num>` - the number of fanins that can be added;<br>          
`-D <num>` - the number of shared divisors to extract;<br>        
`-F <num>` - the limit on the fanin count at a node;<br>      
`-S <num>` - the random seed;<br>
`-T <num>` - the timeout in seconds;<br>
`-V <num>` - the verbosity level;<br>                 
`<file.aig> ` - the input file name;<br>
## Examples
Here is the result of synthesis by the proposed algorithm for the AIG  
of the 2 to 1 Multiplexer function:
```
[...]>./rewire-code -I 10000 -E 10 -G 4 -D 2 -F 5 aig-inputs/mux21.aig
Parameters:  Iters = 10000  Expand = 10  Growth = 4  Divs = 2  FaninMax = 5  Seed = 1  Timeout = 0  Verbose = 0
Loaded MiniAIG from the AIGER file "aig-inputs/mux21.aig".
MiniAIG stats:  PI = 3  PO = 1  FF = 0  AND = 6
Iteration     0 :  Added =   5  Shared =   1  Removed =   7  Best =    3
Total solving time =      0.12 sec  (Expand = 35.1 %  Share = 14.1 %  Reduce = 37.8 %)
MiniAIG stats:  PI = 3  PO = 1  FF = 0  AND = 3
Written MiniAIG into the AIGER file "aig-inputs/mux21_out.aig".
```
