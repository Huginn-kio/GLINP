from z3 import *

# check whether program is a pseudo primitive program
from util import generateZ3Variable, getCoff, uncondAct2Logic, getLinearTermInCondition, verifyTEAndG


def isPseudo(GenCode, actionList, proList, numList):
    if GenCode is None:
        return True

    # no choice
    if GenCode.flag == 'IF' or GenCode.flag == 'IFe':  # if-else
        # print("PP contains IF")
        return False

    # seq
    elif GenCode.flag == 'Seq':  #seq
        fir = GenCode.firstActions
        firDet = True
        if type(fir) == str:
            act = actionList[fir]
            if len(act.subAction) != 0:
                # print("PP contains conditional effect")
                return False
        else:
            firDet = isPseudo(fir,actionList,proList,numList)

        sec = GenCode.secondActions
        secDet = True
        if type(sec) == str:
            act = actionList[sec]
            if len(act.subAction) != 0:
                # print("PP contains conditional effect")
                return False
        else:
            secDet = isPseudo(sec,actionList,proList,numList)
        
        return firDet and secDet

    # loop 
    elif GenCode.flag == 'Loop':
        # check the loop body
        fir = GenCode.firstActions
        firDet = True
        if type(fir) == str:
            # no selective action
            act = actionList[fir]
            if len(act.subAction) != 0:
                return False
        else:
            # nested loop
            return False

        sec = GenCode.secondActions
        secDet = True
        if type(sec) == str:
            act = actionList[sec]
            if len(act.subAction) != 0:
                # print("PP contains conditional effect")
                return False
        else:
            secDet = isPseudo(sec, actionList, proList, numList)
        
        #loop body
        if (firDet and secDet) == False:  
            return False

        # 排除一部分非线性while条件
        elif GenCode.condition == 'False' or GenCode.condition == 'True':
            # print("Loop condition %s is not sat" % GenCode.strcondition)
            return False


        # 排除一部分非线性while条件
        elif GenCode.condition.count('And') > 0 or GenCode.condition.count(
                'Or') > 0 or GenCode.condition.count('not') > 0:
            # print("Loop condition %s is not sat" %GenCode.strcondition)
            return False

        # 判断条件是否线性，是否-1，num是否incremental。pro是否不变，
        else:
            fir = GenCode.firstActions
            
            preproV, postproV, prenumV, postnumV = generateZ3Variable(proList, numList, 'i', 'o')
            subSeqAxioms1, loopBodyproEff1, loopBodynumEff2 = pseudoProgram2Logic(fir, actionList, proList,numList,
                                                                               preproV, prenumV)

            sec = GenCode.secondActions
            subSeqAxioms2, loopBodyproEff, loopBodynumEff = pseudoProgram2Logic(sec, actionList, proList, numList,
                                                                                loopBodyproEff1, loopBodynumEff2)
            loopEff = {}
    
            # check static prop
            for k, v in loopBodyproEff.items():
                if v == True or v == False:
                    # print("Loop body prop %s is not static" %k)
                    return False

            condition = GenCode.condition

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
            effInloop = {}
            for n in numList:
                loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])
                # 变化非整数
                if is_int_value(loopEff[n]) == False:
                    # print("Loop body numeric vars %s are not c-incremental" %n)
                    return False

                if n in numIncond:
                    if loopEff[n] == 1 or loopEff[n] == -1:
                        effInloop[n] = loopEff[n]

            if len(effInloop) != 1:
                # print("Loop body more than one w in condition")
                return False

            var = list(effInloop.keys())[0]  # get the effect modify value

            # print('-----------------------')
            # print(condition)
            # for n in numIncond:
            #     co = getCoff(n, condition)
            #     print(f'{n}:  {co}')
            # print('----------------------')

            coff = getCoff(var, condition)
            if (abs(coff) == 1):
                # print("Cw's coff in loop condition  is sat")
                return True
            else:
                # print("Cw's coff in loop condition  is not sat")
                return False

    else:
        # print('incorrect input sort')
        return False

# translate pseudo primitive program to logic formulas
def pseudoProgram2Logic(GenCode, actionList, proList, numList, preproV, prenumV):
    axioms = []

    proEff = copy.deepcopy(preproV)
    numEff = copy.deepcopy(prenumV)

    # print('---------------------------------------------')
    # print(preproV)
    # print(postproV)
    # print(prenumV)
    # print(postnumV)
    # print(proEff)
    # print(numEff)
    # print('---------------------------------------------')
    if GenCode is None:
        return axioms, proEff, numEff

    elif type(GenCode) == str:
        act = actionList[GenCode]
        axioms, proEff, numEff = uncondAct2Logic(act, proList, numList, preproV, prenumV)
    else:
        if GenCode.flag == 'Seq':
            fir = GenCode.firstActions
            subAxioms, subProEff, subNumEff = pseudoProgram2Logic(fir, actionList, proList, numList, preproV, prenumV)
            axioms += subAxioms
            
            sec = GenCode.secondActions
            subAxioms, proEff, numEff = pseudoProgram2Logic(sec, actionList, proList, numList, subProEff, subNumEff)
            axioms += subAxioms
            
        if GenCode.flag == 'Loop':
            subSeqAxioms = []
            fir = GenCode.firstActions
    
            preproV, postproV, prenumV, postnumV = generateZ3Variable(proList, numList, 'i', 'o')
            subSeqAxioms1, loopBodyproEff1, loopBodynumEff2 = pseudoProgram2Logic(fir, actionList, proList, numList,
                                                                                  preproV, prenumV)

            sec = GenCode.secondActions
            subSeqAxioms2, loopBodyproEff, loopBodynumEff = pseudoProgram2Logic(sec, actionList, proList, numList,
                                                                                loopBodyproEff1, loopBodynumEff2)

            subSeqAxioms += subSeqAxioms1
            subSeqAxioms += subSeqAxioms2
            # print('coooocoocococococoooc')
            # print(subSeqAxioms)
            # print(loopBodynumEff)
            # print(loopBodyproEff)
            # print('cocococococococococo')

            # cope with precondition
            t = Int('k')
            T = ''
            cond = GenCode.condition
            condt = GenCode.condition

            # get vars in condition
            numIncond = []
            changeNum = ''
            for n in numList:
                if n in cond:
                    numIncond.append(n)

            # get linear term e
            cond = getLinearTermInCondition(cond, numList)
            for k, v in numEff.items():
                cond = cond.replace(k, 'numEff["' + k + '"]')
            e = eval(cond)
            # print(e)
            # print(simplify(-(e)))
            # print(type(e))

            # 循环体递增递减值 variable: int  i.e. x : 1  or -1 or 0
            loopEff = {}
            for n in numList:
                loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])

            # get N=e or N = -e
            for n in numIncond:
                if loopEff[n] == 1:
                    changeNum = n
                    coff = getCoff(n, condt)
                    if coff == 1:
                        T = simplify(-(e))
                    elif coff == -1:
                        T = simplify(e)
                if loopEff[n] == -1:
                    changeNum = n
                    coff = getCoff(n, condt)
                    if coff == 1:
                        T = simplify(e)
                    elif coff == -1:
                        T = simplify(-(e))
            # print('N: ', T)

            # print('------loopefff------------')
            # print(loopEff)
            # print('------loopefff------------')
            # +K
            inloopEff = {}
            nloopEff = {}

            for n in numEff:
                if not loopEff[n].__eq__(0):
                    inloopEff[n] = simplify(numEff[n] + t * loopEff[n])
                    nloopEff[n] = numEff[n] + T * loopEff[n]
                else:
                    inloopEff[n] = numEff[n]
                    nloopEff[n] = numEff[n]
                eff = simplify(nloopEff[n] - prenumV[n])
                if not eff.__eq__(0):
                    nloopEff[n] = prenumV[n] + eff
                else:
                    nloopEff[n] = prenumV[n]

            # print("################")
            # print(nloopEff)
            # 循环条件的变量替换
            for n in numList:
                condt = condt.replace(n, 'inloopEff["' + n + '"]')

            # condt = substitute(condt,(prenumV[changeNum], numEff[changeNum]))
            condt = eval(condt)
            condt = simplify(condt)

            # 循环体的前提的变量替换
            subSeqAxiom = simplify(And(subSeqAxioms))
            for n in numList:
                subSeqAxiom = substitute(subSeqAxiom, (prenumV[n], inloopEff[n]))

            for p in proList:
                subSeqAxiom = substitute(subSeqAxiom, (preproV[p], Not(Not(proEff[p]))))

            # 生成公理
            loopsubAxiom = And(T >= 0, ForAll(t, Implies(And(0 <= t, t < T), simplify(And(subSeqAxiom, condt)))))

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
    return axioms, proEff, numEff


# verify pseudo primitive program
def verifyPseudoProgram(domain, GenCode, actionList, proList, numList):
    propInitZ3, propGoalZ3, numInitZ3, numGoalZ3 = generateZ3Variable(proList, numList, 'i', 'g')
    axioms, proEff, numEff = pseudoProgram2Logic(GenCode, actionList, proList, numList, propInitZ3, numInitZ3)
    for p in proList:
        axioms.append(simplify(propGoalZ3[p] == proEff[p]))

    for n in numList:
        axioms.append(simplify(numGoalZ3[n] == numEff[n]))
    print(axioms)
    axiom = simplify(And(axioms))

    return verifyTEAndG(domain, axiom, propInitZ3, numInitZ3, propGoalZ3, numGoalZ3)
