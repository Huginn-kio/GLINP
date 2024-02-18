import getopt
import sys
import time

from generate.complete import complete, GenCode2GenCodeWithElse, getInitState, getInitialStateSet
from generate.complete2 import complete2
from generate.generateinit import modifyGenerateInitialState, addInitialState
from generate.generateplan import generateItemPlan
from generate.infskeleton import infskeleton, PrintNoElseProgram
from utils.util import simplifyGenCode
from verify.verifyNewDecFrg1 import isProgram1, verifyProgram1
from verify.verifyNewDecFrg1Plus import verifyProgram1Plus, isProgram1Plus
from verify.verifyNewDecFrg2 import verifyProgram2, isProgram2
from verify.verifyPseudoProgram import verifyPseudoProgram, isPseudo
from verify.verifyRestricedProgram import isRestricted, verifyRestrictedProgram

def generateInitStates(domain):
    global left
    global right
    global bound
    global stateSize
    global modelSort
    probfileSet = []

    width = 17 - len(domain)
    for i in range(int(width / 2)):
        left += ' '
    right = left
    if (len(left) + len(right) + len(domain) != 17):
        right = right + ' '

    print("\n#######################################################")
    print("####################                 ##################")
    print("####################" + left + domain + right + "##################")
    print("####################                 ##################")
    print("#######################################################")

    print("\n------------------------------------------------------")
    print("---------------------Generate Initial States----------------")
    print("------------------------------------------------------")

    root = ''
    if modelSort == 1:
        root = './domain/' + domain
        modifyGenerateInitialState(domain, bound, stateSize, modelSort)
    elif modelSort == 2:
        root = './domain/' + domain + '/Random'
        modifyGenerateInitialState(domain, bound, stateSize, modelSort)

    i = 1
    while i <= stateSize:
        probfileSet.append(root + '/prob' + str(i) + '.pddl')
        i = i + 1

    return probfileSet

def printInitStates(initset):
    for init in initset:
        print(init)

# generate planning program
def generatePlanningProgram(domain,  probfileSet):
    print("\n------------------------------------------------------")
    print("---------------------Generate Plans----------------")
    print("------------------------------------------------------")

    ItemPlan, plans, actionToLetterList, letterToActionList = generateItemPlan(domain,probfileSet)

    print("\n------------------------------------------------------")
    print("---------------------InfSkeleton----------------")
    print("------------------------------------------------------")

    regexSet,R_regexSet,commonRegex,A_regexSet,GenProgram,letterToNestList,nestToLetterList = infskeleton(ItemPlan, actionToLetterList, letterToActionList)


    print("\n------------------------------------------------------")
    print("---------------------Complete----------------")
    print("------------------------------------------------------")

    domainfile = './domain/' + domain + '/domain.pddl'

    #GenCode,actionList,proList,numList = complete(GenProgram,domainfile,probfileSet,plans)
    GenCode,actionList,proList,numList = complete2(GenProgram,domainfile,probfileSet,plans)

    print("\n1. The generated Planning Program as follow:")
    PrintNoElseProgram(GenCode, 0, 0)
    print("\n2. The simplified Planning Program as follow:")
    simplifyGenCode(GenCode)
    PrintNoElseProgram(GenCode, 0, 0)
    # G1 = GenCode2GenCodeWithElse(GenCode)
    # print('\n3. candidate program with Else structure:')
    # PrintProgramWithElse(G1, 0, 0)

    return GenCode,actionList,proList,numList

def verifyPlanningProgramNonIterative(domain,GenCode, actionList,proList,numList):
    global frag
    print("\n------------------------------------------------------")

    sat = True
    if frag == 1:
        print("---------------------PP or Not----------------")
        print("------------------------------------------------------\n")
        if isPseudo(GenCode, actionList, proList, numList) == True:
            print('The program is PP.')
        else:
            print('The program is not PP.')
            sat = False

    elif frag == 2:
        print("---------------------Restricted or Not----------------")
        print("------------------------------------------------------\n")
        if isRestricted(GenCode, actionList, proList, numList) == True:
            print('The program is Restricted.')
        else:
            print('The program is not Restricted.')
            sat = False

    elif frag == 3:
        print("---------------------program1 or Not----------------")
        print("------------------------------------------------------\n")
        if isProgram1(GenCode, actionList, proList, numList) == True:
            print('The program is program1.')
        else:
            print('The program is not program1.')
            sat = False

    elif frag == 4:
        print("---------------------program2 or Not----------------")
        print("------------------------------------------------------\n")
        if isProgram2(GenCode, actionList, proList, numList) == True:
            print('The program is program2.')
        else:
            print('The program is not program2.')
            sat = False

    elif frag == 5:
        print("---------------------program1Plus or Not----------------")
        print("------------------------------------------------------\n")
        if isProgram1Plus(GenCode, actionList, proList, numList) == True:
            print('The program is program1Plus.')
        else:
            print('The program is not program1Plus.')
            sat = False

    if sat is True:
        return chooseVerification(domain, GenCode, actionList, proList, numList, frag)
    else:
        return sat,0

def verifyPlanningProgramIterative(domain, GenCode, actionList, proList, numList):
    print("\n------------------------------------------------------")
    print("---------------------Can Verified or Not----------------")
    print("------------------------------------------------------\n")
    if isRestricted(GenCode, actionList, proList, numList) == True:
        print('The program is Restricted.')
        return chooseVerification(domain, GenCode, actionList, proList, numList, 2)
    else:
        print('The program is not Restricted.')
        if isProgram2(GenCode, actionList, proList, numList) == True:
            print('The program is program2.')
            return chooseVerification(domain, GenCode, actionList, proList, numList, 4)
        else:
            print('The program is not program2.')
            if isProgram1Plus(GenCode, actionList, proList, numList) == True:
                print('The program is program1Plus.')
                return chooseVerification(domain, GenCode, actionList, proList, numList, 5)
            else:
                print('The program is not program1Plus.')
                return False,0

def chooseVerification(domain, GenCode, actionList, proList, numList, frag):
        print()
        print("\n------------------------------------------------------")
        print("---------------------Verify---------------------------")
        print("------------------------------------------------------\n")
        print("The Correctness Verification of Program as follow:")
        if frag == 1:
            return verifyPseudoProgram(domain, GenCode, actionList, proList, numList)
        elif frag == 2:
            return verifyRestrictedProgram(domain, GenCode, actionList, proList, numList)
        elif frag == 3:
            return verifyProgram1(domain, GenCode, actionList, proList, numList)
        elif frag == 4:
            return verifyProgram2(domain, GenCode, actionList, proList, numList)
        elif frag == 5:
            return verifyProgram1Plus(domain, GenCode, actionList, proList, numList)

#generate and test123.py framework
def iterativeGenerateAndTest(domain):
    global stateSize
    global modelSort

    root = ''
    if modelSort == 1:
        root = './domain/' + domain
    elif modelSort == 2:
        root = './domain/' + domain + '/Random'

    e1 = time.time()
    generateInitStates(domain)
    iteration = 1
    stateNum = 1
    probfileSet = []
    initset = []

    # gnerate and vefrify
    while True:
        print()
        print(f"################## Iteration: {iteration} ######################\n")
        print("------------------------------------------------------")
        print("-------------------initial states---------------------")
        print("------------------------------------------------------")
        print("In the process of generating initial state......")
        print("1. Generation of initial state as follows:")

        i = stateNum
        while i <= stateSize:
            probfileSet.append(root + '/prob' + str(i) + '.pddl')
            i = i + 1

        # 把初始状态信息打印出来
        initset = getInitialStateSet(probfileSet)
        printInitStates(initset)

        GenCode, actionList, proList, numList = generatePlanningProgram(domain, probfileSet)

        #verify planning program
        result, counterexamples = verifyPlanningProgramIterative(domain, GenCode, actionList, proList, numList)

        if result == True:

            print('\nThe final planning program:')
            length = PrintNoElseProgram(GenCode, 0, 0)
            print()
            # print('The initial states formula: %s' % stateFormu)
            # print()
            print('verify successfully.')
            print('The number of states used: %d' % len(initset))
            print('The length of the program: %d' % length)
            break

        else:
            if counterexamples != 0:
                j = 1
                for s in initset:
                    if s in counterexamples:
                        print('Iteration: ', iteration)
                        print('errer, counterexample exists in the initSet')
                        print('initSet:')
                        printInitStates(initset)
                        print(f'counterexample: Seq {j}')
                        print(s)
                        return
                    j += 1

                stateNum = stateSize + 1
                stateSize += len(counterexamples)
                addInitialState(domain, modelSort, stateNum, counterexamples)
                iteration += 1
            else:
                print()
                print('The planning program does not satisfy any decidable fragment. It can not be verified.')
                break

    e2 = time.time()
    print('Iteration: ', iteration)
    print('Time: %fs' % (e2 - e1))
    print("#######################################################")
    print("##################                  ###################")
    print("##################        END       ###################")
    print("##################                  ###################")
    print("#######################################################")

# verify the planning program
def nonIterativeGenerateAndTest(domain):
    probfileSet = generateInitStates(domain)
    initset = getInitialStateSet(probfileSet)
    printInitStates(initset)
    GenCode, actionList, proList, numList = generatePlanningProgram(domain,probfileSet)
    e1 = time.time()
    verifyPlanningProgramNonIterative(domain,GenCode, actionList,proList,numList)
    e2 = time.time()
    print()
    print('Verification Time: %fs' % (e2 - e1))
    print("#######################################################")
    print("##################                  ###################")
    print("##################        END       ###################")
    print("##################                  ###################")
    print("#######################################################")

default=3
#the bound of variable
bound=default
#the number of the initial state
stateSize=default
# mode 1 lin2022, mode 2 random
modelSort = 1
# frag 1 pp, frag 2 restricted
frag = 1
# domain
GLINP=''
# test123.py method
test=1

left=''
right=''

if __name__ == "__main__":
    try:
        options, args = getopt.getopt(sys.argv[1:], "d:b:n:m:f:t:", ["domain", "bound", "number","model","fragment","test123.py"])
        for option, value in options:
            if option in ("-d", "--domain"):
                GLINP = value
            if option in ("-b", "--bound"):
                bound = int(value)
            if option in ("-n", "--number"):
                stateSize = int(value)
            if option in ("-m", "--model"):
                modelSort = int(value)
                if modelSort != 1 and modelSort != 2:
                    print('invalid model. Please input 1 or 2.')
                    sys.exit()
            if option in ("-f", "--frag"):
                frag = int(value)
                if frag not in range(1,6):
                    print('invalid fragment. Please input 1 ~ 5.')
                    sys.exit()
            if option in ("-t", "--test123.py"):
                test = int(value)
                if test != 1 and test != 2:
                    print('invalid test123.py method. Please input 1 or 2.')
                    sys.exit()
    except:
        print("#############################################################################")
        print("Incorrect run command.")
        print("Please recheck the run command.")
        print("Exit the synthesis of the program")
        print("#############################################################################")
        sys.exit()
    if test == 1:
        nonIterativeGenerateAndTest(GLINP)
    else:
        iterativeGenerateAndTest(GLINP)


