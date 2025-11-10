# CDCL Sat Solver
A simple sat solver implementation using conflict driven clause learning.

# Input

At the standard input, the program will receive a number (**z**) of formulas, and then descriptions of individual formulas. The description of a single formula consists of the numbers **n** and **m** denoting the number of variables (variables are numbered from 1 to **n**) and the number of clauses in the formula, respectively, and then **m** descriptions of the clauses. Each clause description consists of variable numbers corresponding to the variables in the clause (negative numbers mean variable negations) ending in the number 0

# Wyjście
If the formula is satisfiable, program will output **TAK**. Otherwise the output will be **NO**

# Example

# Input
 ```
2
3 2
1 2 3 0
-1 -2 0
3 4
-1 0
1 2 0
-2 3 0
-3 1 0
```
# Output
```
TAK
NIE
```
