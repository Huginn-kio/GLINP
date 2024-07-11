import copy
from z3 import *
from datastructure import Prog
from domain import Switch
from util import getCoff, getLinearTermInCondition,isCremental, generateZ3Variable, is2DArray
actionList = {}
iteN = 0
times=0
# translate conditional action to logic formulas
def action2Logic(act, propZ3pre, propZ3post, numZ3pre, numZ3post, proList, numList, preproV, prenumV):
    axioms = []
    effNums = set()
    effPros = set()
    preproV = propZ3post
    prenumV = numZ3post
    for f in act.preFormu:
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
        subaxioms, effPros, effNums = getcondEff(act, propZ3pre, propZ3post, numZ3pre, numZ3post, proList, numList,effPros, effNums)
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
        for p in subact.effect_pos:
            exp = propZ3post[p]
            condeffPros.add(p)
            effect.append(exp)
        for p in subact.effect_neg:
            exp = Not(propZ3post[p])
            condeffPros.add(p)
            effect.append(exp)
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
    return axioms, effPros, effNums

#prog程序，命题变量集，数值变量集，变量名前缀，输入命题Z3变量，输入数值Z3变量，输出命题Z3变量，输出数值Z3变量
def Program2Logic(program, proList, numList, root, preproV, prenumV, postproV, postnumV):
    global iteN, actionList
    axioms = []
    axiom = []
    iproV = preproV
    inumV = prenumV
    firstIproV = None
    firstInumV = None   
    if program is None:
        for p in proList:
            axioms.append(iproV[p] == postproV[p])
        for m in numList:
            axioms.append(inumV[m] == postnumV[m])
        axiom = And(axioms)
    propZ3pre, propZ3post, numZ3pre, numZ3post = generateZ3Variable(proList, numList, str(root) + str(0) + 'i',str(root) + str(0) + 'o')
    if isinstance(program,str):
        act = program
        axiomsNew, preproV, prenumV = action2Logic(actionList[act], propZ3pre, propZ3post, numZ3pre,numZ3post, proList, numList, preproV, prenumV)
        axioms += axiomsNew
    elif isinstance(program,Prog):
        if program.flag=='Seq':
            act = program.firstActions         
            axiomsNew, preproV, prenumV = action2Logic(act, propZ3pre, propZ3post, numZ3pre,numZ3post, proList, numList, preproV, prenumV)
            axioms += axiomsNew
            propZ3pre, propZ3post, numZ3pre, numZ3post = generateZ3Variable(proList, numList, str(root) + str(1) + 'i',str(root) + str(1) + 'o')
            axioms += axiomsNew
        elif program.flag=='Branch':
            print(123)
        elif program.flag=='Loop':
            print(123)
    return axiom

# #prog程序，命题变量集，数值变量集，变量名前缀，输入命题Z3变量，输入数值Z3变量，输出命题Z3变量，输出数值Z3变量
def Program2Logic(program, proList, numList, root, preproV, prenumV, postproV, postnumV):
    global iteN, actionList
    axioms = []
    axiom = []
    #重命名
    iproV = preproV
    inumV = prenumV
    firstIproV = None
    firstInumV = None

    for i in range(len(program)):
        #该子程序片段的输入和输出Z3变量
        propZ3pre, propZ3post, numZ3pre, numZ3post = generateZ3Variable(proList, numList, str(root) + str(i) + 'i',str(root) + str(i) + 'o')
        if(i == 0):
            firstInumV = numZ3pre
            firstIproV = propZ3pre
        interPro = preproV
        interNum = prenumV
        if program[i].flag == 'Seq':
            act = program[i].actionList[0]
            axiomsNew, preproV, prenumV = action2Logic(actionList[act], propZ3pre, propZ3post, numZ3pre,numZ3post, proList, numList, preproV, prenumV)
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
                subaxiom = Program2Logic(program[i].actionList, proList, numList,root + str(i), preproV, prenumV,propZ3post,numZ3post)
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
                subaxiomSat = Program2Logic(program[i].actionList, proList, numList,root + str(i), propZ3pre, numZ3pre,propZ3post,numZ3post)
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
                subLBaxioms, proEff, numEff = pseudoProgram2Logic(program[i].actionList, actionList, proList, numList,propZ3pre, propZ3post, numZ3pre, numZ3post, {}, {})
                t = Int('K' + str(iteN))
                T = Int('N' + str(iteN))
                iteN += 1
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
                for k1, v1 in kloopEff.items():               # x2 : x1_0i - 1
                    for k2, v2 in k_1loopEff.items():         # x1 : x1_0i - 2k + 2
                        # k1 is x2, k2 is x1, if x2 : x1_0i - 1 in kloopEff, it means numZ3pre(k2) (x1_0i) in v1 and k1 != k2,then we get kloopEff x2: x1_0i - 2k + 2 -1
                        if str(numZ3pre[k2]) in str(v1) and k1 != k2:
                            kloopEff[k1] = substitute(kloopEff[k1], (numZ3pre[k2], simplify(k_1loopEff[k2])))

                for k, v in kloopEff.items():
                    nloopEff[k] = simplify(substitute(kloopEff[k], (t, T)))
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
                lenNum = len(numList)
                lenPro = len(proList)
                lenVar = lenNum + lenPro
                if lenVar > 0:
                    subLBaxioms = subLBaxioms[0:-lenVar]
                subLBaxiom = And(subLBaxioms)
                subLBaxiomOne = And(subLBaxioms)
                for m in numList:
                    subLBaxiom = substitute(subLBaxiom, (numZ3pre[m], kloopEff[m]))
                for p in proList:
                    subLBaxiom = substitute(subLBaxiom, (propZ3pre[p], simplify(Not(Not(proEff[p])))))
                LBAxiomEuqZero = []
                LBAxiomTempOverZero = []
                LBAxiomEuqZero.append(Not(cond0))
                for p in proList:
                    LBAxiomEuqZero.append(propZ3post[p] == propZ3pre[p])
                    LBAxiomTempOverZero.append(propZ3post[p] == proEff[p])
                for m in numList:
                    LBAxiomEuqZero.append(numZ3post[m] == numZ3pre[m])
                    LBAxiomTempOverZero.append(numZ3post[m] == nloopEff[m])
                LBAxiomEuqZero = And(LBAxiomEuqZero)
                LBAxiomEuqOne = And(t == 0, cond1, subLBaxiomOne)
                LBAxiomOverOne = And(t > 0, condt, simplify(subLBaxiom))
                LBAxiomTempOverZero.extend ([ T > 0, Not(condT), ForAll(t, Implies(And(0 <= t, t < T),Or(LBAxiomEuqOne, LBAxiomOverOne)))])
                LBAxiomOverZero = And(cond0, Exists(T, And(LBAxiomTempOverZero)))
                finalAxiom = Or(LBAxiomEuqZero, LBAxiomOverZero)
                axioms.append(finalAxiom)
                preproV = propZ3post
                prenumV = numZ3post
        if (len(program) == 1):
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
                    for m in numList:
                        if (type(axioms[j]) is list):
                            for k in range(len(axioms[j])):
                                axioms[j][k] = substitute(axioms[j][k], (interNum[m], numZ3pre[m]))
                        else:
                            axioms[j] = substitute(axioms[j], (interNum[m], numZ3pre[m]))
                if is2DArray(axioms):
                    subAxiom = []
                    for k in range(len(axioms)):
                        if type(axioms[k]) is list:
                            subAxiom.append(And(axioms[k]))
                        else:
                            subAxiom.append(axioms[k])
                    axiom = And(subAxiom)
                else:
                    axiom = And(axioms)
                forget = []
                for p in propZ3pre:
                    forget.append(propZ3pre[p])
                for m in numZ3pre:
                    forget.append(numZ3pre[m])
                axiom = Exists(forget, axiom)
                axioms = []
                axioms.append(axiom)

        if(i == len(program)-1):
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


def verifyProgram(domain, GenCode, init, goal, actList, proList, numList):
    global actionList
    actionList = actList
    root = ''
    propInitZ3, propGoalZ3, numInitZ3, numGoalZ3 = generateZ3Variable(proList, numList, 'i', 'g')
    if init == '' or goal == '':
        init, goal = Switch.get(domain)(propInitZ3, propGoalZ3, numInitZ3, numGoalZ3)
    init = And(init)
    goal = And(goal)
    #prog程序，命题变量集，数值变量集，变量名前缀，输入命题Z3变量，输入数值Z3变量，输出命题Z3变量，输出数值Z3变量
    axiom = Program2Logic(GenCode, proList, numList, root, propInitZ3, numInitZ3,propGoalZ3,numGoalZ3)
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



# translate pseudo primitive program to logic formulas
def pseudoProgram2Logic(programList,actList,proList,numList,preproV, postproV, prenumV, postnumV,proEff,numEff):
    global times
    flag = 0
    axioms = []
    #第一次进入
    if times == 0:
        flag = 1
        for p in proList:
            proEff[p] = preproV[p]
        for n in numList:
            numEff[n] = prenumV[n]
    times += 1
    for i in range (len(programList)):
        if programList[i].flag == 'Seq':
            subAxioms,proEff,numEff = pseudoAction2Logic(actList[programList[i].actionList[0]],proList,numList,proEff,numEff)
            axioms += subAxioms
        if programList[i].flag == 'Loop':
            proTempEff = {}
            numTempEff = {}
            for p in proList:
                proTempEff[p] = preproV[p]
            for n in numList:
                numTempEff[n] = prenumV[n]
            subSeqAxioms,loopBodyproEff,loopBodynumEff = pseudoProgram2Logic(programList[i].actionList,actList,proList,numList,preproV, postproV, prenumV, postnumV, proTempEff,numTempEff)
            t = Int('k')
            T = ''
            cond = programList[i].strcondition
            condt = programList[i].strcondition
            numIncond = []
            changeNum = ''
            for n in numList:
                if n in cond:
                    numIncond.append(n)
            cond = getLinearTermInCondition(cond,numList)
            for k, v in numEff.items():
                cond = cond.replace(k, 'numEff["' + k + '"]')
            #循环体递增递减值 variable: int  i.e. x : 1  or -1 or 0
            loopEff = {}
            for n in numList:
                loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])
            # get N=e or N = -e
            for n in numIncond:
                if loopEff[n] == 1:
                    changeNum = n
                    coff = getCoff(n,condt)
                    if coff == 1:
                        T = simplify(-(e))
                    elif coff == -1:
                        T = simplify(e)
                if loopEff[n] == -1:
                    changeNum = n
                    coff = getCoff(n,condt)
                    if coff == 1:
                        T = simplify(e)
                    elif coff == -1:
                        T = simplify(-(e))
            inloopEff={}
            nloopEff={}
            for n in numEff:
                inloopEff[n] = simplify(numEff[n] + t * loopEff[n])
                nloopEff[n] = simplify(numEff[n] + T * loopEff[n])
            # 循环条件的变量替换
            for n in numList:
                condt = condt.replace(n, 'inloopEff["'+n+'"]')
            # condt = substitute(condt,(prenumV[changeNum], numEff[changeNum]))
            condt = eval(condt)
            condt = simplify(condt)
            # 循环体的前提的变量替换
            subSeqAxiom = simplify(And(subSeqAxioms))
            for n in numList:
                subSeqAxiom = substitute(subSeqAxiom,(prenumV[n],inloopEff[n]))
            for p in proList:
                subSeqAxiom = substitute(subSeqAxiom, (preproV[p], Not(Not(proEff[p]))))
            loopsubAxiom = And(T>=0, ForAll(t,Implies(And(0<=t,t<T), simplify(And(subSeqAxiom, condt)))))
            axioms.append(loopsubAxiom)
            for n in numList:
                numEff[n] = nloopEff[n]
    if flag == 1:
        for p in proList:
            axioms.append(simplify(postproV[p] == proEff[p]))
        for n in numList:
            axioms.append(simplify(postnumV[n] == numEff[n]))
        times = 0
    return axioms,proEff,numEff


def pseudoAction2Logic(act,proList,numList,lastproEff,lastnumEff):
    axioms = []
    proEff = copy.deepcopy(lastproEff)
    numEff = copy.deepcopy(lastnumEff)
    for p in act.preFormu:
        if int(p.right) == 0:
            exp = Not(lastproEff[p.left])
        else:
            exp = lastproEff[p.left]
        axioms.append(exp)
    for n in act.preMetric:
        if isinstance(n,list):
            orAxioms = []
            for l in n:
                if l.op == '=':
                    l.op = '=='
                if l.right in numList:
                    exp = eval('lastnumEff["' + l.left + '"]' + l.op + 'lastnumEff["' + l.right + '"]')
                else:
                    exp = eval('lastnumEff["' + l.left + '"]' + l.op + l.right)
                orAxioms.append(exp)
            axioms.append(Or(orAxioms))
        else:
            if n.op == '=':
                n.op = '=='
            if n.right in numList:
                exp = eval('lastnumEff["' + n.left + '"]' + n.op + 'lastnumEff["' + n.right + '"]')
            else:
                exp = eval('lastnumEff["' + n.left + '"]' + n.op  + n.right )
            axioms.append(exp)
    for pp in act.effect_pos:
        proEff[pp] = True
    for pn in act.effect_neg:
        proEff[pn] = False
    for formu in act.effect_Metric:
        if formu.op == 'increase':
            numEff[formu.left] = eval('lastnumEff["' + formu.left + '"]' + '+' + formu.right)
        elif formu.op == 'decrease':
            numEff[formu.left] = eval('lastnumEff["' + formu.left + '"]' + '-' + formu.right)
        elif formu.op == 'assign':
            right = formu.right
            for n in numList:
                right = right.replace(n,"lastnumEff['" + n + "']")
            right = eval(right)
            numEff[formu.left] = right
    return axioms,proEff,numEff

