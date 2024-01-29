# translate program3
import re

from z3 import And, Implies, Not, Exists, substitute, simplify, is_int_value, Int, ForAll, Or
from generate.datastructure import Program
from utils.util import getCoff, getLinearTermInCondition, generateZ3Variable, uncondAct2Logic, isAcyclic, isCremental, \
    verifyTEAndG

# check whether a prorgam is program3
def isProgram3(GenCode, actionList, proList, numList):
    if type(GenCode) == list:  # list type
        for program in GenCode:
            if not isProgram3(program, actionList, proList, numList):
                return False
        return True

    elif type(GenCode) == Program:  # one program
        # no choice
        if GenCode.flag == 'IF' or GenCode.flag == 'IFe':  # if-else
            # print("contains IF")
            return False

        # action
        elif GenCode.flag == 'Seq':  # action seq
            act = actionList[GenCode.actionList[0]]
            if len(act.subAction) != 0:
                # print("PP contains conditional effect")
                return False
            else:
                return True

        # loop
        elif GenCode.flag == 'Loop':
            # need modify to Pseudo primitive program
            if not isProgram3(GenCode.actionList, actionList, proList, numList):
                # print("Loop body is not sat program3")
                return False

            else:
                preproV, postproV, prenumV, postnumV = generateZ3Variable(proList, numList, 'i', 'o')
                subSeqAxioms, loopBodyproEff, loopBodynumEff = program12Logic(GenCode.actionList, actionList, proList,
                                                                                   numList, preproV, postproV, prenumV,
                                                                                   postnumV)

                # check whether props are simple
                for k, v in loopBodyproEff.items():
                    if not (v == True or v == False or simplify(v == preproV[k])):
                        print("Loop body prop is not simple")
                        return False

                #check condition
                condition = GenCode.strcondition

                for p in proList:
                    if p in condition:
                        # print("Loop condition %s  contain prop" %condition)
                        return False

                numIncond = []
                # 判断while条件是否满足线性
                for n in numList:
                    if n in condition:
                        numIncond.append(n)

                # 获得循环体的num变量变化
                cIncNumInCond = []
                wInloop = []
                loopEff = {}
                flag = True
                for n in numList:
                    loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])
                    cur = prenumV[n].__repr__()
                    if is_int_value(loopEff[n]):
                        # print("c-incremental:",prenumV[n].__repr__()+" = "+loopBodynumEff[n].__repr__())
                        if not loopEff[n].__eq__(0) and n in numIncond :
                            cIncNumInCond.append(n)
                    else:
                        # linear by contain it self
                        # print("linear:",prenumV[n].__repr__()+" = "+loopBodynumEff[n].__repr__())
                        varList = re.findall(r"(\([\d\w]*\)[io]?)", loopBodynumEff[n].__repr__())
                        # print(varList)
                        if cur in varList:
                            print("constant symbol " + cur + " (" + loopBodynumEff[n] + ")" +
                                  " not sat c-incremental or linear")
                            return False
                        elif n in numIncond:
                            wInloop.append(n)
                        flag = False

                if len(wInloop) != 1:
                    # print("Loop body more than one w in condition")
                    return False

                if len(cIncNumInCond) > 0:
                    return False

                w = wInloop[0]
                wEff = loopBodynumEff[w]
                for n in numList:
                    if n != w:
                        wEff = substitute(wEff, (prenumV[n], loopEff[n]))

                if not is_int_value(wEff) or not wEff.__eq__(1) or wEff.__eq__(-1):
                    return False

                coff = getCoff(w, condition)
                if (abs(coff) != 1):
                    # print("Cw's coff in loop condition  is not sat")
                    return False

                if flag == True:
                    # print("all c-incremental")
                    return True
                if not isAcyclic(numList,loopBodynumEff,prenumV):
                    print("The body of loop is not acyclic")
                    return False
                return True
    else:
        return True

# translate restricted program to logic formula
level = 0
iterN = 0
def program32Logic(program,actionList, proList, numList, preproV, postproV, prenumV, postnumV):
    global level
    global iterN
    axioms = []

    level += 1

    proEff = {}
    numEff = {}

    for p in proList:
        proEff[p] = preproV[p]

    for n in numList:
        numEff[n] = prenumV[n]

    for i in range(len(program)):

        if program[i].flag == 'Seq':
            act = program[i].actionList[0]
            subAxioms, proEff, numEff = uncondAct2Logic(actionList[act], proList, numList, proEff, numEff)
            axioms += subAxioms

        elif program[i].flag == 'Loop':

            subLoopBodyAxioms, loopBodyproEff, loopBodynumEff = program32Logic(program[i].actionList, actionList,
                                                                               proList, numList, preproV, postproV,
                                                                               prenumV, postnumV)
            iterN += 1
            t = Int('K' + str(iterN))
            T = ''
            cond = program[i].strcondition
            condt = program[i].strcondition

            # get vars in condition
            numIncond = []
            for n in numList:
                if n in cond:
                    numIncond.append(n)

            # 获得循环体的num变量变化
            loopEff = {}
            wInloop = []
            creNumVs = []
            linNumVs = []
            wInloop = {}
            for n in numList:
                loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])
                cur = prenumV[n].__repr__()
                if is_int_value(loopEff[n]):
                    creNumVs.append(n)
                else:
                    # linear by contain it self
                    # print("linear:",prenumV[n].__repr__()+" = "+loopBodynumEff[n].__repr__())
                    varList = re.findall(r"(\([\d\w]*\)[io]?)", loopBodynumEff[n].__repr__())
                    # print(varList)
                    if cur not in varList:
                        linNumVs.append(n)
                        if n in numIncond:
                            wInloop.append(n)

            # get linear term e
            eTmp = getLinearTermInCondition(cond, numList)
            for k, v in numEff.items():
                eTmp = eTmp.replace(k, 'numEff["' + k + '"]')
                cond = cond.replace(k, 'numEff["' + k + '"]')

            cond = eval(cond)

            # get N=e or N = -e
            for n in numIncond:
                if loopEff[n] == 1:
                    coff = getCoff(n, condt)
                    if coff == 1:
                        T = simplify(-(e))
                    elif coff == -1:
                        T = simplify(e)
                if loopEff[n] == -1:
                    coff = getCoff(n, condt)
                    if coff == 1:
                        T = simplify(e)
                    elif coff == -1:
                        T = simplify(-(e))

            # kth effect  k-1 th effect  nth effect in c-incremental
            kloopEff = {}
            k_1loopEff = {}
            nloopEff = {}

            for n in numList:
                if isCremental(loopEff[n], prenumV[n]):
                    kloopEff[n] = simplify(numEff[n] + t * loopEff[n])
                    k_1loopEff[n] = simplify(numEff[n] + (t-1) * loopEff[n])
                    nloopEff[n] = simplify(numEff[n] + T * loopEff[n])
                    creNumVs.append(n)
                else :
                    kloopEff[n] = loopBodynumEff[n]
                    linNumVs.append(n)

            # kth nth linear effect
            for n in linNumVs:
                for m in creNumVs:
                    kloopEff[n] = substitute(kloopEff[n], (prenumV[m], simplify(k_1loopEff[m])))
                    nloopEff[n] = substitute(kloopEff[n], (t,T))

            # 循环条件的变量替换
            for n in numList:
                condt = condt.replace(n, 'kloopEff["' + n + '"]')

            # condt = substitute(condt,(prenumV[changeNum], numEff[changeNum]))
            condt = eval(condt)
            condt = simplify(condt)

            # 循环体的前提的变量替换
            # N > 0 and K > 0
            # N > 0 and K = 0
            subLoopBodyAxiom = simplify(And(subLoopBodyAxioms))
            subLoopBodyAxiomOne = simplify(And(subLoopBodyAxioms))

            # N > 0 and K > 0
            for n in numList:
                subLoopBodyAxiom = substitute(subLoopBodyAxiom, (prenumV[n], kloopEff[n]))

            for p in proList:
                subLoopBodyAxiom = substitute(subLoopBodyAxiom, (preproV[p], simplify(Not(Not(proEff[p])))))

            # N > 0 and K = 0
            subLoopBodyK0Axiom = And(t == 0, cond, subLoopBodyAxiomOne);

            # N > 0 and K > 0
            subLoopBodyKAxiom = And(t > 0, condt, subLoopBodyAxiom);


            # 生成公理  N > 0
            loopsubAxiom = And(T >= 0, ForAll(t, Implies(And(0 <= t, t < T), Or(subLoopBodyK0Axiom, subLoopBodyKAxiom))))

            axioms.append(loopsubAxiom)

            # print('+++++++++++++++++++++')
            # print(numEff)
            # print('++++++++++++++++++=')

            # 生成最后的proEff(不变) numEff
            for n in numList:
                numEff[n] = nloopEff[n]

            # print('--------------numefff-------------')
            # print(nloopEff)
            # print(numEff)
            # print('--------------numefff-------------')
    if level == 1:
        # 程序最顶层
        for p in proList:
            axioms.append(simplify(postproV[p] == proEff[p]))

        for n in numList:
            axioms.append(simplify(postnumV[n] == numEff[n]))

    level -= 1
    return axioms, proEff, numEff


def verifyProgram3(domain, GenCode, actionList, proList, numList):
    propInitZ3, propGoalZ3, numInitZ3, numGoalZ3 = generateZ3Variable(proList, numList, 'i', 'g')
    axiom,proEff,numEff = program32Logic(GenCode,actionList, proList, numList, propInitZ3, propGoalZ3, numInitZ3, numGoalZ3)
    axiom = simplify(And(axiom))
    return verifyTEAndG(domain, axiom, propInitZ3, numInitZ3, propGoalZ3, numGoalZ3)