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
* ```<Option of The Method of Generating Initial States>``` : it is an integer with option of the method of generating initial states(1.the method originated from Lin2022 ;2.the method of generating random initial states).The default option is 1.
* ```<Option of The Decidable Program Fragment>``` : it is an integer with the option of the decidable program fragment(1.the unconditional pseudo-primitive program;2.the restricted program).The default option is 1.

The current GLINP problems in the paper can be run directly according to the following commands;

For example, the GLINP problem：Arith

```
python main.py -d Arith -b 3 -n 3 -m 1 -f 1
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
init_cons:  And(v1 == 0, v2 == 0, n > 0)
new_init_states_cons: [n == 3, v1 == 0, v2 == 0]
new_init_states_cons: [n == 4, v1 == 0, v2 == 0]
new_init_states_cons: [n == 5, v1 == 0, v2 == 0]

------------------------------------------------------
---------------------Generate Plans----------------
------------------------------------------------------

1.Compute corresponding solution by planner as follows:
['INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV1', 'INCV1', 'INCV1']
['INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV1', 'INCV1', 'INCV1', 'INCV1']
['INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV2', 'INCV1', 'INCV1', 'INCV1', 'INCV1', 'INCV1']

2.The action representing by letter as follows:
{'INCV1': 'a', 'INCV2': 'b', 'EMPTYACTION': '#'}
{'a': 'INCV1', 'b': 'INCV2', '#': 'EMPTYACTION'}

------------------------------------------------------
---------------------InfSkeleton----------------
------------------------------------------------------

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

9. The Program Skeleton:
while phi1 do
    INCV2
od;
while phi2 do
    INCV1
od

------------------------------------------------------
---------------------Complete----------------
------------------------------------------------------

1. Tracking the trace of performing solution to collect positive state and negative state as follows:
while phi1 do
    INCV2
od;
while phi2 do
    INCV1
od

2. The generated Planning Program as follow:
while (n) != (v2) - ((n) + 1) do
    INCV2
od;
while (n) != (v1) do
    INCV1
od

------------------------------------------------------
---------------------PP or Not----------------
------------------------------------------------------

The program is PP.


------------------------------------------------------
---------------------Verify---------------------------
------------------------------------------------------

The Correctness Verification of Program as follow:

Goal reachable successful proven!!!!

Termination and Executability successful proven!!!!

Verification Time: 0.029113s

#######################################################
##################                  ###################
##################        END       ###################
##################                  ###################
#######################################################

```

Other domains of  GLINP that appear in the experiment can follow the above running command and directly replace "Arith" with the corresponding domain name.

------



## 4. BENCHMARKS


The following are the 47 GLINP domains of the experiment

|   ***Arith***    |    ***Baking***    |   ***Barman***   |   ***Barman3***   |
|:----------------:|:------------------:|:----------------:|:-----------------:|
|  ***Barman4***   |   ***Barman5***    |  ***Barman6***   |   ***Barman7***   |
|  ***Barman8***   |  ***Childsnack***  |    ***Chop***    | ***ClearBlock***  |
|  ***Corner-A***  |   ***Corner-R***   |  ***Corridor***  |  ***D-Return***   |
| ***D-Return-R*** |   ***Delivery***   |     ***Grid***     |   ***Gripper***   |
|   ***Hall-A***   |   ***Hall-R***   |     ***Hiking***     |  ***Intrusion***  |
|    ***Lock***    |  ***Miconic***   |  ***MNestVar2***   |  ***MNestVar3***  |
| ***MNestVar4***  | ***MNestVar5***  |  ***MNestVar6***  |  ***MNestVar7***  |
| ***MNestVar8***  |  ***NestVar2***  |  ***NestVar3***   |  ***NestVar4***   |
|  ***NestVar5***  |  ***NestVar6***  |  ***NestVar7***   |  ***NestVar8***   |
| ***PlaceBlock*** |   ***Rewards***  |    ***Snow***     |    ***Spanner***  |
|   ***TestOn***   |  ***Visitall***  |  ***Visitall-R***  |
