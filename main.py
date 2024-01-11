import getopt
import sys
import time

from generate.complete import complete, GenCode2GenCodeWithElse
from generate.generateinit import modifyGenerateInitialState, addInitialState
from generate.generateplan import generateItemPlan
from generate.infskeleton import infskeleton, PrintNoElseProgram
from verify.verifyNewDecFrg1 import isProgram1, verifyProgram1
from verify.verifyPseudoProgram import verifyPseudoProgram, isPseudo
from verify.verifyRestricedProgram import isRestricted, verifyRestrictedProgram

# generate planning program
def generatePlanningProgram(domain):
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
        modifyGenerateInitialState(domain,bound,stateSize,modelSort)
    elif modelSort == 2:
        root = './domain/' + domain + '/Random'
        modifyGenerateInitialState(domain,bound,stateSize,modelSort)

    i = 1
    while i <= stateSize:
        probfileSet.append(root + '/prob' + str(i) + '.pddl')
        i = i + 1

    # print(probfileSet)

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

    GenCode,actionList,proList,numList = complete(GenProgram,domainfile,probfileSet,plans)

    print("\n2. The generated Planning Program as follow:")
    PrintNoElseProgram(GenCode, 0, 0)
    G1 = GenCode2GenCodeWithElse(GenCode)
    # print('\n3. candidate program with Else structure:')
    # PrintProgramWithElse(G1, 0, 0)

    return GenCode,actionList,proList,numList



def verifyPlanningProgram(domain,GenCode,init,goal,actionList,proList,numList):
  print("\n------------------------------------------------------")
  print("---------------------Verify---------------------------")
  print("------------------------------------------------------\n")
  print("The Correctness Verification of Program as follow:")
  if frag == 1:
      return verifyPseudoProgram(domain, GenCode, init, goal, actionList, proList, numList)
  elif frag == 2:
      return verifyRestrictedProgram(domain, GenCode, init, goal, actionList, proList, numList)
  elif frag == 3:
      return verifyProgram1(domain, GenCode, init, goal, actionList, proList, numList)



#generate and test framework
def generateAndIterativeVerifyPlanningProgram(domain):
    global left
    global right
    global bound
    global stateSize
    global modelSort
    # 产生框体结构
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

    e1 = time.time()
    root = ''
    if modelSort == 1:
        root = './domain/' + domain
        modifyGenerateInitialState(domain,bound,stateSize,modelSort)
    elif modelSort == 2:
        root = './domain/' + domain + '/Random'
        modifyGenerateInitialState(domain,bound,stateSize,modelSort)

    iteration = 1
    stateNum = 1
    probfileSet = []
    initset = []

    # gnerate and vefrify
    while True:
        i = stateNum
        while i <= stateSize:
            probfileSet.append( root + '/prob' + str(i) + '.pddl')
            i = i + 1

        print("\n------------------------------------------------------")
        print("---------------------Generate Plans----------------")
        print("------------------------------------------------------")

        ItemPlan, plans, actionToLetterList, letterToActionList = generateItemPlan(domain, probfileSet)

        print("\n------------------------------------------------------")
        print("---------------------InfSkeleton----------------")
        print("------------------------------------------------------")

        regexSet, R_regexSet, commonRegex, A_regexSet, GenProgram, letterToNestList, nestToLetterList = infskeleton(
            ItemPlan, actionToLetterList, letterToActionList)

        print("\n------------------------------------------------------")
        print("---------------------Complete----------------")
        print("------------------------------------------------------")

        domainfile = './domain/' + domain + '/domain.pddl'

        GenCode, actionList, proList, numList = complete(GenProgram, domainfile, probfileSet, plans)

        if isRestricted(GenCode, actionList, proList, numList) == True:
             print('The program is restricted.')

             #verify restricted planning program
             result, states = verifyPlanningProgram(domain, GenCode, '','',actionList, proList, numList)

             if result == True:
                 e2 = time.time()
                 print()
                 print("#######################################################")
                 print("##################                  ###################")
                 print("##################        END       ###################")
                 print("##################                  ###################")
                 print("#######################################################")
                 print()

                 # stateFormu = getStateFormu(initset,proList,numList)
                 print('The final planning program:')
                 length = PrintNoElseProgram(GenCode, 0, 0)
                 print()
                 # print('The initial states formula: %s' % stateFormu)
                 # print()
                 print('verify successfully.')
                 print('The number of states used: %d' % len(initset))
                 print('The length of the program: %d' % length)
                 print('Iteration: ', iteration)
                 print('Time: %fs' % (e2 - e1))
                 return

             else:
                 for s in states:
                     if s in initset:
                         print('errer!!!!!!!!!!!!!')
                         print('Iteration: ', iteration)
                         print('The number of states used: %d' % len(initset))
                         return
                 stateNum = stateSize + 1
                 stateSize += len(states)
                 addInitialState(domain, modelSort, stateNum, states)
                 iteration += 1


        else:
            print('The program is not restricted')
            e2 = time.time()
            print()
            print("#######################################################")
            print("##################                  ###################")
            print("##################        END       ###################")
            print("##################                  ###################")
            print("#######################################################")
            print()

            print('verify failed.')
            print('Iteration: ', iteration)
            # print('Time: %fs'%(e2-e1))
            # stateFormu = getStateFormu(initset, proList, numList)
            # print('The final planning program:')
            # length = PrintNoElseProgram(GenCode, 0, 0)
            # print()
            # print('The length of the program: %d' % length)
            # print()
            # print('The initial states formula: %s' %stateFormu)
            return


# verify the planning program
def NonIterativeVerifyPlanningProgram(domain):
    GenCode, actionList, proList, numList = generatePlanningProgram(domain)
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

    if sat is True:
            # verify restricted planning program
            print()
            e1 = time.time()
            verifyPlanningProgram(domain, GenCode, '', '', actionList, proList, numList)
            e2 = time.time()
            print()
            print('Verification Time: %fs' % (e2 - e1))

    print()
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
# test method
test=1

left=''
right=''

if __name__ == "__main__":
    try:
        options, args = getopt.getopt(sys.argv[1:], "d:b:n:m:f:t:", ["domain", "bound", "number","model","fragment","test"])
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
                if frag != 1 and frag != 2 and frag != 3:
                    print('invalid fragment. Please input 1 or 2.')
                    sys.exit()
            if option in ("-t", "--test"):
                test = int(value)
                if test != 1 and test != 2:
                    print('invalid test method. Please input 1 or 2.')
                    sys.exit()
    except:
        print("#############################################################################")
        print("Incorrect run command.")
        print("Please recheck the run command.")
        print("Exit the synthesis of the program")
        print("#############################################################################")
        sys.exit()
    if test == 1:
        NonIterativeVerifyPlanningProgram(GLINP)
    else:
        generateAndIterativeVerifyPlanningProgram(GLINP)


