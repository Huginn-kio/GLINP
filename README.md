# A Generate-and-Verify Framework

## 1.WHAT IS It ?

* It is a generate-and-verify framework for the Generalized Linear Integer Numeric Planning (GLINP) problem, including generating planning program process and verifying correctness process.
The framework first generate planning program with Lin et al.'s states or random states, and then verify its correctness.

------

## 2.REQUIREMENTS
- This repository have been compiled, executed and tested in Ubuntu 20.04.4 LTS, 64bit

- The version of Z3 SMT solver is  4.8.13.0

- The version of Antlr4 is 4.8.

- The version of python's operating environment is 3.8.10.

- The access permission of Metric-FF planner  needs to be changed before running. e.g.chmod 777 ./ff

------

## 3.USAGE
run the code with the following command:
```
python main.py -d <GLINP Problem> -b <Bound of Numberic Variable> -n <Number of Train Instance> -m <Option of The Method of Generating Initial States> -f <Option of The Decidable Program Fragment>
```
* ```<GLINP Domain>``` : it is a string with the GLINP problem, 
* ```<Bound of Numberic Variable>``` : it is an integer with the Bound of Numberic Variable. The default option is 3.
* ```<Number of Train Instance>``` : it is an integer with the Number of Train Instance. The default option is 3.

The current GLINP problems in the paper can be run directly according to the following commands;

For example, the GLINP problem：Arith

```
python main.py -b 3 -n 3 -d Arith 
```

The result after running:

```
#######################################################
####################                 ##################
####################      Arith      ##################
####################                 ##################
#######################################################

------------------------------------------------------
---------------------Generate Initial States----------------
------------------------------------------------------
ANTLR runtime and generated code versions disagree: 4.8!=4.7.2
init_cons:  And(v1 == 0, v2 == 0, n > 0)
ANTLR runtime and generated code versions disagree: 4.8!=4.7.2
new_init_states_cons: [n == 3, v1 == 0, v2 == 0]
new_init_states_cons: [n == 4, v1 == 0, v2 == 0]
new_init_states_cons: [n == 5, v1 == 0, v2 == 0]
ANTLR runtime and generated code versions disagree: 4.8!=4.7.2

------------------------------------------------------
---------------------Generate Plans----------------
------------------------------------------------------

1.Compute corresponding solution by planner as follows:
['INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV1', 'INCV1', 'INCV1']
['INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV1', 'INCV1', 'INCV1', 'INCV1']
['INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV1', 'INCV1', 'INCV1', 'INCV1', 'INCV1']
ANTLR runtime and generated code versions disagree: 4.8!=4.7.2

2.The action representing by letter as follows:
{'INCV1': 'a', 'INCV2': 'b', 'EMPTYACTION': '#'}
{'a': 'INCV1', 'b': 'INCV2', '#': 'EMPTYACTION'}

------------------------------------------------------
---------------------InfSkeleton----------------
------------------------------------------------------

 the abbr char of example list:
['bbbbbbbaaa', 'bbbbbbbbbaaaa', 'bbbbbbbbbbbaaaaa']

1. The multiple lowercase letter representing by single uppercase letter as follows:
{'(b)*': 'A', '(a)*': 'B'}
{'A': '(b)*', 'B': '(a)*'}

2. Identification of Iteration Subregexes:
['(b)*(a)*', '(b)*(a)*', '(b)*(a)*']

3. Identification of Iteration Subregexes representing by Abbreviation:
['AB', 'AB', 'AB']

4. Alignment of Iteration Subregexes:
['(b)*(a)*', '(b)*(a)*', '(b)*(a)*']

5. Alignment of Iteration Subregexes representing by Abbreviation:
['AB', 'AB', 'AB']

6. Alignment of Iteration Subregexes representing by unrepeated Abbreviation:
['AB']

7. There is only one unrepeatedRegex:
['AB']

8. Identification of Alternation Subregexes:
[[], [], []]
['A', 'B']
The regex List of program:
['A', 'B']

9. The Program Skeleton:
(INCV2*,INCV1*)

10. The regex of Program:
((((b)*))(((a)*)))

------------------------------------------------------
---------------------Complete----------------
------------------------------------------------------

1. Tracking the trace of performing solution to collect positive state and negative state as follows:

2. The generated Planning Program as follow:
while (n) != (v2) - ((n) + 1) do
 INCV2
 od·
while (n) - (v1) != 0 do
 INCV1
 od
The length of Planning Program is:21
The depth of Planning Program is:1
Generation Time: 1.706589s

#######################################################
##################                  ###################
##################        END       ###################
##################                  ###################
#######################################################




