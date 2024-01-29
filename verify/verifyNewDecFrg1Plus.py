# translate program1
import re

from z3 import And, Implies, Not, Exists, substitute, simplify, is_int_value, Int, ForAll, Or
from generate.datastructure import Program
from utils.util import getCoff, getLinearTermInCondition, generateZ3Variable, uncondAct2Logic, isAcyclic, isCremental, \
    verifyTEAndG, isContainChoice, condAct2Logic, is2DArray

# check whether a prorgam is program1Plus
from verify.verifyNewDecFrg1 import program12Logic, isProgram1


def isProgram1Plus(GenCode, actionList, proList, numList):
    if type(GenCode) == list:  # list type
        for program in GenCode:
            if not isProgram1Plus(program, actionList, proList, numList):
                print(program.strcondition)
                return False
        return True

    elif type(GenCode) == Program:  # one program
        if GenCode.flag == 'IFe':
            return True

        elif GenCode.flag == 'IF' :  # if-else
            # print("contains IF")
            return isProgram1Plus(GenCode.actionList, actionList, proList, numList)

        # action
        elif GenCode.flag == 'Seq':  # action seq
            return True

        # loop
        elif GenCode.flag == 'Loop':
            # need modify to Pseudo primitive program
            if not isProgram1(GenCode.actionList, actionList, proList, numList):
                # print("Loop body is not sat program1")
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

                # 获得循环体的num变量变化
                cIncNum = []
                loopEff = {}
                flag = True
                for n in numList:
                    loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])
                    cur = prenumV[n].__repr__()
                    if is_int_value(loopEff[n]):
                        # print("c-incremental:",prenumV[n].__repr__()+" = "+loopBodynumEff[n].__repr__())
                        cIncNum.append(n)
                    else:
                        # linear by contain it self
                        # print("linear:",prenumV[n].__repr__()+" = "+loopBodynumEff[n].__repr__())
                        varList = re.findall(r"(\([\d\w]*\)[io]?)", loopBodynumEff[n].__repr__())
                        # print(varList)
                        if cur in varList:
                            print("constant symbol " + cur + " (" + loopBodynumEff[n].__repr__() + ")" +
                                  " not sat c-incremental or linear")
                            return False
                        flag = False

                if flag :
                    # print("all c-incremental")
                    return True
                if not isAcyclic(numList,loopBodynumEff,prenumV):
                    print("The body of loop is not acyclic")
                    return False
                return True
    else:
        return True

# translate restricted program to logic formula
iteN = 0
def program1Plus2Logic(program, actionList, proList, numList, root, preproV, prenumV, postproV, postnumV):
    global iteN
    axioms = []
    axiom = []
    iproV = preproV
    inumV = prenumV
    firstIproV = None
    firstInumV = None

    for i in range(len(program)):

        propZ3pre, propZ3post, numZ3pre, numZ3post = generateZ3Variable(proList, numList, str(root) + str(i) + 'i',
                                                                        str(root) + str(i) + 'o')
        if(i == 0):
            firstInumV = numZ3pre
            firstIproV = propZ3pre

        interPro = preproV
        interNum = prenumV


        if program[i].flag == 'Seq':
            act = program[i].actionList[0]
            axiomsNew, preproV, prenumV = condAct2Logic(actionList[act], propZ3pre, propZ3post, numZ3pre,
                                                      numZ3post, proList, numList)

            axioms += axiomsNew


        elif program[i].flag == 'IFe':

            for p in proList:
                axioms.append(propZ3pre[p] == propZ3post[p])

            for m in numList:
                axioms.append(numZ3pre[m] == numZ3post[m])

            preproV = propZ3post
            prenumV = numZ3post



        elif program[i].flag == 'IF':
            str1 = program[i].strcondition

            if str1 == 'False':

                for p in proList:
                    axioms.append(propZ3pre[p] == propZ3post[p])

                for m in numList:
                    axioms.append(numZ3pre[m] == numZ3post[m])

                preproV = propZ3post
                prenumV = numZ3post


            elif str1 == 'True':


                subaxiom = program1Plus2Logic(program[i].actionList, actionList, proList, numList,
                                                                       root + str(i), preproV, prenumV,propZ3post,numZ3post)

                preproV = propZ3post
                prenumV = numZ3post
                axioms.append(subaxiom)

            else:
                for p in proList:
                    str1 = str1.replace(p, 'propZ3pre["' + p + '"]')
                for m in numList:
                    str1 = str1.replace(m, 'numZ3pre["' + m + '"]')

                expCond = eval(str1)

                #condition satisfied
                subaxiomSat = program1Plus2Logic(program[i].actionList, actionList, proList, numList,
                                                                       root + str(i), propZ3pre, numZ3pre,propZ3post,numZ3post)


                exp1 = Implies(expCond, subaxiomSat)
                axioms.append(exp1)

                #condition unsatisfied
                subaxiomUnsat = []
                for p in proList:
                    subaxiomUnsat.append(propZ3pre[p] == propZ3post[p])
                for m in numList:
                    subaxiomUnsat.append(numZ3pre[m] == numZ3post[m])

                exp2 = Implies(Not(expCond), And(subaxiomUnsat))
                axioms.append(exp2)

                preproV = propZ3post
                prenumV = numZ3post


        elif program[i].flag == 'Loop':

            if program[i].strcondition == 'False':
                for p in proList:
                    axioms.append(propZ3pre[p] == propZ3post[p])

                for m in numList:
                    axioms.append(numZ3pre[m] == numZ3post[m])

                preproV = propZ3post
                prenumV = numZ3post


            elif program[i].strcondition == 'True':
                axiom = False
                break

            else:
                # obtain the axioms and effects of body
                subLBaxioms, proEff, numEff = program12Logic(program[i].actionList, actionList, proList, numList,
                                                                  propZ3pre, propZ3post, numZ3pre, numZ3post)

                # print('----------1-------------')
                # print(subLBaxioms)
                # print(proEff)
                # print(numEff)
                # print('----------1-------------')

                # N K
                t = Int('K' + str(iteN))
                T = Int('N' + str(iteN))
                iteN += 1

                # not satisfy condition N=0 or N > 0 and k = 0
                # N > 0 and K > 0 satisfied
                # N > 0 and k > 0 unsatisfied
                cond0 = program[i].strcondition
                condt = program[i].strcondition
                condT = program[i].strcondition

                # obtain loop body effect
                kloopEff = {}
                k_1loopEff = {}
                nloopEff = {}

                # get K  k-1 effect of loop body
                # only one dependency
                for m in numList:
                    temp = simplify(numEff[m] - numZ3pre[m])
                    # c-incremental
                    if isCremental(temp, numZ3pre[m]):
                        kloopEff[m] = simplify(numZ3pre[m] + (t * temp))
                        k_1loopEff[m] = simplify(numZ3pre[m] + (t - 1) * temp)
                    # assignment
                    else:
                        kloopEff[m] = numEff[m]

                # v1 = v1 + 1
                # v2 = v1
                # kloopEff: v1 = v1 + k; v2 = v1 + 1
                # k_1loopEff: v1 = v1 + k-1

                # print('---------------0----------')
                # print(kloopEff)
                # print(k_1loopEff)
                # print('---------------0----------')

                # get assignment effect
                for k1, v1 in kloopEff.items():  # x2 : x1_0i - 1
                    for k2, v2 in k_1loopEff.items():  # x1 : x1_0i - 2k + 2
                        # k1 is x2, k2 is x1, if x2 : x1_0i - 1 in kloopEff, it means numZ3pre(k2) (x1_0i) in v1 and k1 != k2,then we get kloopEff x2: x1_0i - 2k + 2 -1
                        if str(numZ3pre[k2]) in str(v1) and k1 != k2:
                            kloopEff[k1] = substitute(kloopEff[k1], (numZ3pre[k2], simplify(k_1loopEff[k2])))

                # get n-iter loop effect
                for k, v in kloopEff.items():
                    nloopEff[k] = simplify(substitute(kloopEff[k], (t, T)))

                # print('########################')
                # print(k_1loopEff)
                # print(kloopEff)
                # print(nloopEff)
                # print('########################')

                # 循环条件的变量替换
                # not satisfy condition N=0 or N > 0 and k = 0
                # N > 0 and K > 0 satisfied
                # N > 0 and k > 0 unsatisfied
                for p in proList:
                    cond0 = cond0.replace(p, 'propZ3pre["' + p + '"]')
                    condt = condt.replace(p, 'proEff["' + p + '"]')
                    condT = condT.replace(p, 'proEff["' + p + '"]')

                for n in numList:
                    cond0 = cond0.replace(n, 'numZ3pre["' + n + '"]')
                    condt = condt.replace(n, 'kloopEff["' + n + '"]')
                    condT = condT.replace(n, 'nloopEff["' + n + '"]')

                cond0 = eval(cond0)
                condt = eval(condt)
                condT = eval(condT)

                # if str(condt) != 'True' and str(condt) != 'False':
                #     condt = simplify(condt)
                #     condT = simplify(condT)
                #
                # if str(condt) != 'True' and str(condt) != 'False':
                #     # condition version: K=0  K>0  N
                #     for n in numList:
                #         # print(condt)
                #         # print(prenumV[n])
                #         # print(inloopEff[n])
                #         condt = substitute(condt, (prenumV[n], inloopEff[n]))
                #         condT = substitute(condT, (prenumV[n], nloopEff[n]))
                #     condt = simplify(condt)
                #     condT = simplify(condT)
                #
                # cond0 = simplify(cond0)

                # print('---------------')
                # print(subLBaxioms)

                # delete (x)o == (x)i - c from subLBaxioms
                lenNum = len(numList)
                lenPro = len(proList)
                lenVar = lenNum + lenPro
                if lenVar > 0:
                    subLBaxioms = subLBaxioms[0:-lenVar]
                # print(subLBaxioms)
                # print('--------------')

                # 循环体的前提的变量替换
                # N > 0 and K > 0
                # N > 0 and K = 0
                subLBaxiom = And(subLBaxioms)
                subLBaxiomOne = And(subLBaxioms)

                # N > 0 and K > 0
                for m in numList:
                    subLBaxiom = substitute(subLBaxiom, (numZ3pre[m], kloopEff[m]))

                for p in proList:
                    subLBaxiom = substitute(subLBaxiom, (propZ3pre[p], simplify(Not(Not(proEff[p])))))

                # 生成公理
                # N=0 axioms
                LBAxiomEuqZero = []
                # N>0
                LBAxiomTempOverZero = []

                # N = 0
                LBAxiomEuqZero.append(Not(cond0))
                for p in proList:
                    LBAxiomEuqZero.append(propZ3post[p] == propZ3pre[p])
                    LBAxiomTempOverZero.append(propZ3post[p] == proEff[p])

                for m in numList:
                    LBAxiomEuqZero.append(numZ3post[m] == numZ3pre[m])
                    LBAxiomTempOverZero.append(numZ3post[m] == nloopEff[m])

                # N = 0
                LBAxiomEuqZero = And(LBAxiomEuqZero)

                # N > 0
                # N > 0 and K = 0
                LBAxiomEuqOne = And(t == 0, cond0, subLBaxiomOne)

                # N > 0 and K > 0
                LBAxiomOverOne = And(t > 0, condt, simplify(subLBaxiom))

                # N > 0 axioms - K = 0 or K > 0
                LBAxiomTempOverZero.extend([T > 0, Not(condT), ForAll(t, Implies(And(0 <= t, t < T),
                                                                                 Or(LBAxiomEuqOne, LBAxiomOverOne)))])

                LBAxiomOverZero = And(cond0, Exists(T, And(LBAxiomTempOverZero)))

                # final axioms
                finalAxiom = Or(LBAxiomEuqZero, LBAxiomOverZero)

                axioms.append(finalAxiom)

                preproV = propZ3post
                prenumV = numZ3post



        if (len(program) == 1):
            #conditional effect
            for j in range(len(axioms)):
                if type(axioms[j] is list):
                    axioms[j] = And(axioms[j])
            axiom = And(axioms)
        else:
            if (i > 0):
                for j in range(len(axioms)):
                    for p in proList:
                        if(type(axioms[j]) is list):
                            for k in range(len(axioms[j])):
                                axioms[j][k] = substitute(simplify(Not(Not(axioms[j][k]))), (interPro[p], propZ3pre[p]))
                        else:
                            axioms[j] = substitute(simplify(Not(Not(axioms[j]))), (interPro[p], propZ3pre[p]))
                        # axioms[j] = substitute(simplify(Not(Not(axioms[j]))), (interPro[p], propZ3pre[p]))

                    for m in numList:
                        if (type(axioms[j]) is list):
                            for k in range(len(axioms[j])):
                                axioms[j][k] = substitute(axioms[j][k], (interNum[m], numZ3pre[m]))
                        else:
                            axioms[j] = substitute(axioms[j], (interNum[m], numZ3pre[m]))
                        # axioms[j] = substitute(axioms[j], (interNum[m], numZ3pre[m]))

                if is2DArray(axioms):
                    subAxiom = [];
                    for k in range(len(axioms)):
                        if type(axioms[k]) is list:
                            subAxiom.append(And(axioms[k]))
                        else:
                            subAxiom.append(axioms[k])
                    axiom = And(subAxiom)

                else:
                    axiom = And(axioms)
                # axiom = And(axiomsti)

                forget = []
                for p in propZ3pre:
                    forget.append(propZ3pre[p])


                for m in numZ3pre:
                    forget.append(numZ3pre[m])

                axiom = Exists(forget, axiom)
                axioms = []
                axioms.append(axiom)

        if(i == len(program)-1):
            # print('------------1-----------------')
            # print(axiom)
            # print('------------2-----------------')
            # print(firstIproV)
            # print(firstInumV)
            # print('------------3-----------------')
            # print(iproV)
            # print(inumV)
            # print('------------4-----------------')
            # print(preproV)
            # print(prenumV)
            # print('------------5-----------------')
            # print(postproV)
            # print(postnumV)
            # print('------------6-----------------')


            for p in proList:
                axiom = substitute(axiom, (firstIproV[p], iproV[p]))
                axiom = substitute(axiom, (preproV[p], postproV[p]))
            for m in numList:
                axiom = substitute(axiom, (firstInumV[m], inumV[m]))
                axiom = substitute(axiom, (prenumV[m], postnumV[m]))

    #deal with empty program
    if (len(program) == 0):
        for p in proList:
            axioms.append(iproV[p] == postproV[p])

        for m in numList:
            axioms.append(inumV[m] == postnumV[m])
        axiom = And(axioms)

    return axiom


def verifyProgram1Plus(domain, GenCode, actionList, proList, numList):
    root = ''
    propInitZ3, propGoalZ3, numInitZ3, numGoalZ3 = generateZ3Variable(proList, numList, 'i', 'g')
    axiom = program1Plus2Logic(GenCode, actionList, proList, numList, root, propInitZ3, numInitZ3, propGoalZ3, numGoalZ3)
    return verifyTEAndG(domain, axiom, propInitZ3, numInitZ3, propGoalZ3, numGoalZ3)