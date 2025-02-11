import copy
import re

from datastructure import Program
from domain import Switch
from util import isCremental, is_number, generateZ3Variable, is2DArray
from verifyPseudoProgram import pseudoProgram2Logic, isPseudo
from z3 import *

# translate a retricted planning program
actionList = {}
iteN = 0


# check whether a prorgam is a retricted planning program
nodeIndex = {}
visit = []
stack = []
cyclePath = []
edgeTo = {}
g = []
maxDepth = 0
isDAG = True


def initGraph(len):
    global g
    g = [list() for i in range(len)]  # graph


def addEdge(ia, ib):
    global g
    if ib not in g[ia]:
        g[ia].append(ib)


def dfs(root, depth):
    global visit, g, isDAG, stack, cyclePath, maxDepth
    stack[root] = True
    visit[root] = True
    if depth > maxDepth:
        maxDepth = depth
    for item in g[root]:
        if not isDAG:
            return
        elif not visit[item]:
            edgeTo[item] = root
            dfs(item, depth + 1)
        elif stack[item]:
            isDAG = False
            x = root
            while (x != item):
                cyclePath.append(x)
                x = edgeTo[x]
            cyclePath.append(item)
            cyclePath.append(root)
    stack[root] = False


def checkDAG(len):
    global isDAG, visit, stack, cyclePath, edgeTo, maxDepth
    maxDepth = -1
    isDAG = True
    # print("start to DAG checking")
    visit = [False for x in range(len)]
    stack = [False for x in range(len)]
    cyclePath = []
    edgeTo = {}
    for i in range(len):
        visit = [False for x in range(len)]
        if isDAG:
            dfs(i, 0)
        # print("current maxDeth is:",maxDepth)

    return isDAG


def getNodeIndex(cur):
    global nodeIndex
    if cur in nodeIndex.keys():
        return nodeIndex[cur]
    else:
        t = len(nodeIndex)
        nodeIndex[cur] = t
        return t


def clearNodeIndex():
    global nodeIndex
    nodeIndex = {}


def printGraph():
    global g
    for i, item in enumerate(g):
        print("[%d]: %s" % (i, item))


def printCycle():
    global cyclePath
    print("CyclePath is:", cyclePath)


def isRestricted(GenCode, actList, proList, numList):
    if type(GenCode) == list:  # list type
        for program in GenCode:
            if isRestricted(program, actList, proList, numList) == False:
                return False
        return True

    elif type(GenCode) == Program:  # one program
        # no choice
        if GenCode.flag == 'IF':
            return isRestricted(GenCode.actionList, actList, proList, numList)
        if GenCode.flag == 'IFe':
            return True
        # action
        elif GenCode.flag == 'Seq':  # action seq
            return True

        # loop
        elif GenCode.flag == 'Loop':
            # need modify to Pseudo primitive program
            if isPseudo(GenCode.actionList, actList, proList, numList) == False:
                print("Loop body is not sat PP")
                return False

            # 判断条件是否线性，是否-1，num是否incremental。pro是否不变，
            else:
                preproV, postproV, prenumV, postnumV = generateZ3Variable(proList, numList, 'i', 'o')
                subSeqAxioms, loopBodyproEff, loopBodynumEff = pseudoProgram2Logic(GenCode.actionList, actList, proList,
                                                                                   numList, preproV, postproV, prenumV,
                                                                                   postnumV, {}, {})

                # check whether props are simple
                for k, v in loopBodyproEff.items():
                    if not (v == True or v == False or simplify(v == preproV[k])):
                        print("Loop body prop is not simple")
                        return False

                # 获得循环体的num变量变化
                cIncNUm = []
                varList = []
                loopEff = {}
                clearNodeIndex()
                initGraph(len(numList))
                flag = True
                for n in numList:
                    loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])
                    cur = prenumV[n].__repr__()
                    ia = getNodeIndex(cur)
                    if is_int_value(loopEff[n]) == True:
                        # print("c-incremental:",prenumV[n].__repr__()+" = "+loopBodynumEff[n].__repr__())
                        cIncNUm.append(prenumV[n].__repr__())
                    else:
                        # linear by contain it self
                        # print("linear:",prenumV[n].__repr__()+" = "+loopBodynumEff[n].__repr__())
                        varList = re.findall(r"(\([\d\w]*\)[io]?)", loopBodynumEff[n].__repr__())
                        # print(varList)
                        if cur in varList:
                            print("Contain itself, not sat c-incremental or linear")
                            return False
                        flag = False
                        for item in varList:
                            ib = getNodeIndex(item)
                            addEdge(ia, ib)
                            # print("add edge %d %s -> %d %s" %(ia,cur,ib,item))
                # print("Graph is following:")
                # printGraph()
                # print("#################")
                if flag == True:
                    # print("all c-incremental")
                    return True
                if not checkDAG(len(numList)):
                    # printCycle()
                    print("cyclic")
                    return False
                # print("DAG")
                return True

    else:
        return True


# translate conditional action to logic formulas
def action2Logic(act, propZ3pre, propZ3post, numZ3pre, numZ3post, proList, numList, preproV, prenumV):
    axioms = []
    effNums = set()
    effPros = set()

    preproV = propZ3post
    prenumV = numZ3post

    for f in act.preFormu:
        # print('====---====')
        # print(f'{f.left} {f.op} {f.right}')
        # print('====---====')
        exp = ''
        if int(f.right) == 0:
            exp = Not(propZ3pre[f.left])
        else:
            exp = propZ3pre[f.left]

        axioms.append(exp)

    for m in act.preMetric:
        if isinstance(m, list):
            orAxioms = []
            for n in m:
                if n.op == "=":
                    n.op = "=="

                # right = ''
                # for k, v in numZ3pre.items():
                #     if k in n.right:
                #         right = n.right.replace(k, "numZ3pre['" + k + "']")
                #     else:
                #         right = n.right
                # exp = eval('numZ3pre[n.left]' + n.op + right)

                if n.right in numList:
                    exp = eval('numZ3pre["' + n.left + '"]' + n.op + 'numZ3pre["' + n.right + '"]')
                else:
                    exp = eval('numZ3pre["' + n.left + '"]' + n.op + n.right)
                orAxioms.append(exp)
            axioms.append(Or(orAxioms))

        else:
            if m.op == "=":
                m.op = "=="

            if m.right in numList:
                exp = eval('numZ3pre["' + m.left + '"]' + m.op + 'numZ3pre["' + m.right + '"]')
            else:
                exp = eval('numZ3pre["' + m.left + '"]' + m.op + m.right)
            axioms.append(exp)

    # effect
    for p in act.effect_pos:
        exp = propZ3post[p]
        effPros.add(p)
        axioms.append(exp)

    for p in act.effect_neg:
        exp = Not(propZ3post[p])
        effPros.add(p)
        axioms.append(exp)

    for m in act.effect_Metric:
        effNums.add(m.left)
        if (m.op == "increase"):
            exp = eval('numZ3post[m.left]' + "==" + 'numZ3pre[m.left]' + "+" + m.right)
        elif (m.op == "decrease"):
            exp = eval('numZ3post[m.left]' + "==" + 'numZ3pre[m.left]' + "-" + m.right)
        elif m.op == "assign":
            right = m.right
            for n in numList:
                right = right.replace(n, 'numZ3pre["' + n + '"]')
            exp = eval('numZ3post[m.left]' + "==" + right)
        axioms.append(exp)

    if len(act.subAction) != 0:
        subaxioms, effPros, effNums = getcondEff(act, propZ3pre, propZ3post, numZ3pre, numZ3post, proList, numList,
                                                 effPros, effNums)
        axioms.append(subaxioms)

    for p in proList:
        if p not in effPros:
            exp = propZ3post[p] == propZ3pre[p]
            axioms.append(exp)

    for m in numList:
        if m not in effNums:
            axioms.append(numZ3post[m] == numZ3pre[m])

    return axioms, preproV, prenumV


# merger conditional effect
def getcondEff(act, propZ3pre, propZ3post, numZ3pre, numZ3post, proList, numList, effPros, effNums):
    axioms = []
    preAxioms = []
    notChangeAxioms = []
    condeffPros = set()
    condeffNums = set()
    for subact in act.subAction:
        precond = []
        effect = []

        # precond
        if len(subact.preFormu) != 0:
            for p in subact.preFormu:
                if int(p.right) == 0:
                    exp = Not(propZ3pre[p.left])
                else:
                    exp = propZ3pre[p.left]
                precond.append(exp)

        if len(subact.preMetric) != 0:
            for m in subact.preMetric:
                if m.op == "=":
                    m.op = "=="

                right = ''
                for k, v in numZ3pre.items():
                    if k in m.right:
                        right = m.right.replace(k, "numZ3pre['" + k + "']")
                    else:
                        right = m.right

                exp = eval('numZ3pre[m.left]' + m.op + right)
                precond.append(exp)

        # effect
        # propEff
        for p in subact.effect_pos:
            exp = propZ3post[p]
            condeffPros.add(p)
            effect.append(exp)

        for p in subact.effect_neg:
            exp = Not(propZ3post[p])
            condeffPros.add(p)
            effect.append(exp)

        # numEff
        for m in subact.effect_Metric:
            condeffNums.add(m.left)
            if (m.op == "increase"):
                exp = eval('numZ3post[m.left]' + "==" + 'numZ3pre[m.left]' + "+" + m.right)
            elif (m.op == "decrease"):
                exp = eval('numZ3post[m.left]' + "==" + 'numZ3pre[m.left]' + "-" + m.right)
            elif (m.op == "assign" and m.right.count('(') == 1):
                if m.right in numZ3pre:
                    exp = eval('numZ3post[m.left]' + "==" + 'numZ3pre[m.right]')
                else:
                    right = ''
                    for k, v in numZ3pre.items():
                        right = m.right.replace(k, 'numZ3pre["' + k + '"]')
                    exp = eval('numZ3post[m.left]' + "==" + right)
            effect.append(exp)

        precond = And(precond)
        effect = And(effect)
        # print('----------------')
        # print(effect)
        # print('-----------------')
        subAxiom = Implies(precond, effect)
        preAxioms.append(precond)
        axioms.append(subAxiom)

    for p in condeffPros:
        exp = propZ3post[p] == propZ3pre[p]
        notChangeAxioms.append(exp)

    for n in condeffNums:
        exp = numZ3post[n] == numZ3pre[n]
        notChangeAxioms.append(exp)

    notChangePreAxiom = Not(Or(preAxioms))
    notChangeAxiom = Implies(notChangePreAxiom, And(notChangeAxioms))
    axioms.append(notChangeAxiom)

    effPros = effPros.union(condeffPros)
    effNums = effNums.union(condeffNums)

    # print('--------')
    # print(condeffNums)
    # print(condeffPros)
    # print(effPros)
    # print(effNums)
    # print('--------')

    return axioms, effPros, effNums


# translate restricted program to logic formula
def restrictedProgram2Logic(program, proList, numList, root, preproV, prenumV, postproV, postnumV):
    global iteN, actionList
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
            axiomsNew, preproV, prenumV = action2Logic(actionList[act], propZ3pre, propZ3post, numZ3pre,
                                                      numZ3post, proList, numList, preproV, prenumV)

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


                subaxiom = restrictedProgram2Logic(program[i].actionList, proList, numList,
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
                subaxiomSat = restrictedProgram2Logic(program[i].actionList, proList, numList,
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
                subLBaxioms, proEff, numEff = pseudoProgram2Logic(program[i].actionList, actionList, proList, numList,
                                                                  propZ3pre, propZ3post, numZ3pre, numZ3post, {}, {})

                # print('----------1-------------')
                # print(subLBaxioms)
                # print(proEff)
                # print(numEff)
                # print('----------1-------------')

                # N K
                t = Int('K' + str(iteN))
                T = Int('N' + str(iteN))
                iteN += 1

                # not satisfy condition N=0
                # N > 0 and k = 0
                # N > 0 and K > 0 satisfied
                # N > 0 and k > 0 unsatisfied
                cond0 = program[i].strcondition
                cond1 = program[i].strcondition
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
                    if isCremental(temp, numZ3pre[m]) == True:
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
                for k1, v1 in kloopEff.items():               # x2 : x1_0i - 1
                    for k2, v2 in k_1loopEff.items():         # x1 : x1_0i - 2k + 2
                        # k1 is x2, k2 is x1, if x2 : x1_0i - 1 in kloopEff, it means numZ3pre(k2) (x1_0i) in v1 and k1 != k2,then we get kloopEff x2: x1_0i - 2k + 2 -1
                        if str(numZ3pre[k2]) in str(v1) and k1 != k2:
                            kloopEff[k1] = substitute(kloopEff[k1], (numZ3pre[k2], simplify(k_1loopEff[k2])))

                #get n-iter loop effect
                for k, v in kloopEff.items():
                    nloopEff[k] = simplify(substitute(kloopEff[k], (t, T)))

                # print('########################')
                # print(k_1loopEff)
                # print(kloopEff)
                # print(nloopEff)
                # print('########################')

                # 循环条件的变量替换
                # not satisfy condition N=0
                # N > 0 and k = 0
                # N > 0 and K > 0 satisfied
                # N > 0 and k > 0 unsatisfied
                for p in proList:
                    cond0 = cond0.replace(p, 'propZ3pre["' + p + '"]')
                    cond1 = cond1.replace(p, 'propZ3pre["' + p + '"]')
                    condt = condt.replace(p, 'proEff["' + p + '"]')
                    condT = condT.replace(p, 'proEff["' + p + '"]')

                for n in numList:
                    cond0 = cond0.replace(n, 'numZ3pre["' + n + '"]')
                    cond1 = cond1.replace(n, 'numZ3pre["' + n + '"]')
                    condt = condt.replace(n, 'kloopEff["' + n + '"]')
                    condT = condT.replace(n, 'nloopEff["' + n + '"]')

                cond0 = eval(cond0)
                cond1 = eval(cond1)
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
                # cond1 = simplify(cond1)

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
                LBAxiomEuqOne = And(t == 0, cond1, subLBaxiomOne)

                # N > 0 and K > 0
                LBAxiomOverOne = And(t > 0, condt, simplify(subLBaxiom))


                # N > 0 axioms - K = 0 or K > 0
                LBAxiomTempOverZero.extend ([ T > 0, Not(condT), ForAll(t, Implies(And(0 <= t, t < T),
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


def verifyRestrictedProgram(domain, GenCode, init, goal, actList, proList, numList):
    global actionList
    actionList = actList
    root = ''
    propInitZ3, propGoalZ3, numInitZ3, numGoalZ3 = generateZ3Variable(proList, numList, 'i', 'g')

    if init == '' or goal == '':
        init, goal = Switch.get(domain)(propInitZ3, propGoalZ3, numInitZ3, numGoalZ3)

    init = And(init)
    goal = And(goal)
    axiom = restrictedProgram2Logic(GenCode, proList, numList, root, propInitZ3, numInitZ3,propGoalZ3,numGoalZ3)
    states = []
    resultg = False
    resultt = False

    #
    print("------------------------------------------------------")
    print("---------------------trace axioms---------------------")
    print("------------------------------------------------------")
    print(axiom)


    # return False, states, states, states

    # print()
    # print("------------------------------------------------------")
    # print("-------------the result of verification---------------")
    # print("------------------------------------------------------")
    # print(f'init:  {init}')
    # print(f'goal:  {goal}')
    # print(f'axiom:  {axiom}')


    gaolAch = Not(Implies(And(axiom, init), goal))

    for p in propGoalZ3.values():
        axiom = Exists(p, axiom)
    for m in numGoalZ3.values():
        axiom = Exists(m, axiom)

    temAndExe = Not(Implies(init, axiom))

    # print(f'goalAch:  {gaolAch}')
    # print(f'teminate: {teminate}')

    print()

    # goalachevability
    sgoal = Solver()
    sgoal.add(gaolAch)
    if sgoal.check() == sat:
        # not achevable
        m = sgoal.model()
        # counter={}
        # for p in proList:
        #     counter[p]=m[eval(p[1:-1])]
        # for n in numList:
        #     print(n[1:-1])
        #     counter[n]=m[eval(n[1:-1])].as_long()
        print("Goal reachable Failed proven!!!!")
        print("The counter Example:")
        print(m)
        stateg = {}
        for n in m:
            for k1, v2 in propInitZ3.items():
                if str(n) == str(k1) + 'i':
                    stateg[k1] = m[n]
            for k2, v2 in numInitZ3.items():
                if str(n) == str(k2) + 'i':
                    stateg[k2] = m[n]

        states.append(stateg)

    else:
        resultg = True
        print("Goal reachable successful proven!!!!")
    sgoal.reset()

    print()

    # termination and executability

    terminateTest = []

    sterminate = Solver()
    sterminate.add(temAndExe)
    if sterminate.check() == sat:
        # not
        m = sterminate.model()
        # counter = {}
        # for p in proList:
        #     counter[p] = m[preproV[p]]
        # for n in numList:
        #     counter[n] = m[prenumV[n]].as_long()
        print("Termination and Executability Failed proven!!!!")
        print("The counter Example:")
        print(m)
        statet = {}
        # for n in m:
        #     if n in propInitZ3.values() or n in numInitZ3.values():
        #         terminateTest.append(n == m[n])

        for n in m:
            for k1, v2 in propInitZ3.items():
                if str(n) == k1 + 'i':
                    statet[k1] = m[n]
            # if str(n)[0:-1] not in propInitZ3.keys():
            #         statet[str(n)[0:-1]] = False;

            for k2, v2 in numInitZ3.items():
                if str(n) == k2 + 'i':
                    statet[k2] = m[n]

        states.append(statet)

    else:
        resultt = True
        print("Termination and Executability successful proven!!!!")
    sterminate.reset()

    # print('------------------states----------')
    # print(states)
    # print('------------------states----------')
    if resultg == True and resultt == True:
        return True, states
    else:
        return False, states
