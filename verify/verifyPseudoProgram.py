from generate.datastructure import Program
from verify.domain import Switch
from utils.util import getCoff, getLinearTermInCondition, generateZ3Variable, uncondAct2Logic, verifyTEAndG
from z3 import *

# check whether program is a pseudo primitive program
def isPseudo(GenCode, actionList, proList, numList):
    if type(GenCode) == list:  # list type
        for program in GenCode:
            if isPseudo(program, actionList, proList, numList) == False:
                return False
        return True

    elif type(GenCode) == Program:  # one program
        # no choice
        if GenCode.flag == 'IF' or GenCode.flag == 'IFe':  # if-else
            # print("PP contains IF")
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

            if isPseudo(GenCode.actionList, actionList, proList, numList) == False:  # check the loop body
                return False

                # 排除一部分非线性while条件
            elif GenCode.strcondition == 'False' or GenCode.strcondition == 'True':
                # print("Loop condition %s is not sat" % GenCode.strcondition)
                return False


            # 排除一部分非线性while条件
            elif GenCode.strcondition.count('And') > 0 or GenCode.strcondition.count(
                    'Or') > 0 or GenCode.strcondition.count('not') > 0:
                # print("Loop condition %s is not sat" %GenCode.strcondition)
                return False

            # 判断条件是否线性，是否-1，num是否incremental。pro是否不变，
            else:
                preproV, postproV, prenumV, postnumV = generateZ3Variable(proList, numList, 'i', 'o')
                subSeqAxioms, loopBodyproEff, loopBodynumEff = pseudoProgram2Logic(GenCode.actionList, actionList,proList, numList,
                                                                                   preproV, postproV, prenumV, postnumV,
                                                                                   )
                loopEff = {}

                # check static prop
                for k, v in loopBodyproEff.items():
                    if v == True or v == False:
                        # print("Loop body prop %s is not static" %k)
                        return False

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
times=0
def pseudoProgram2Logic(programList,actList,proList,numList, preproV, postproV, prenumV, postnumV):
    global times
    axioms = []

    times += 1

    proEff = {}
    numEff = {}

    for p in proList:
        proEff[p] = preproV[p]

    for n in numList:
        numEff[n] = prenumV[n]

    # print('---------------------------------------------')
    # print(preproV)
    # print(postproV)
    # print(prenumV)
    # print(postnumV)
    # print(proEff)
    # print(numEff)
    # print('---------------------------------------------')

    for i in range (len(programList)):
        if programList[i].flag == 'Seq':
            # action ——> logic formula
            # return:
            #   subAxioms: the axioms about predictions of action
            #   proEff, numEff: the propositional and numeric effect about action — a dictionary of the form — num: numi+1(z3variable)

            # print('-----------------')
            # print('---------1-------')
            # print(numEff)

            subAxioms,proEff,numEff = uncondAct2Logic(actList[programList[i].actionList[0]],proList,numList,proEff,numEff)
            axioms += subAxioms
            # print('+++++++++++++++++++++++++++++++')
            # print(axioms)
            # print('--')
            # print(proEff)
            # print('---')
            # print(numEff)
            # print('++++++++++++++++++++++++++++++++')

        if programList[i].flag == 'Loop':
            # loop statement ——> logic formula

            subSeqAxioms,loopBodyproEff,loopBodynumEff = pseudoProgram2Logic(programList[i].actionList,actList,proList,numList,preproV, postproV, prenumV, postnumV)

            # print('coooocoocococococoooc')
            # print(subSeqAxioms)
            # print(loopBodynumEff)
            # print(loopBodyproEff)
            # print('cocococococococococo')

            # cope with precondition
            t = Int('k')
            T = ''
            cond = programList[i].strcondition
            condt = programList[i].strcondition


            # get vars in condition
            numIncond = []
            changeNum = ''
            for n in numList:
                if n in cond:
                    numIncond.append(n)

            # get linear term e
            cond = getLinearTermInCondition(cond,numList)
            for k, v in numEff.items():
                cond = cond.replace(k, 'numEff["' + k + '"]')
            e = eval(cond)
            # print(e)
            # print(simplify(-(e)))
            # print(type(e))

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
            # print('N: ', T)

            # print('------loopefff------------')
            # print(loopEff)
            # print('------loopefff------------')
            # +K
            inloopEff={}
            nloopEff={}

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

            #生成公理
            loopsubAxiom = And(T>=0, ForAll(t,Implies(And(0<=t,t<T), simplify(And(subSeqAxiom, condt)))))

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

    if times == 1:
        #程序最顶层
        for p in proList:
            axioms.append(simplify(postproV[p] == proEff[p]))

        for n in numList:
            axioms.append(simplify(postnumV[n] == numEff[n]))

    times -= 1

    return axioms,proEff,numEff

# verify pseudo primitive program
def verifyPseudoProgram(domain,GenCode,actionList,proList,numList):
    propInitZ3, propGoalZ3, numInitZ3, numGoalZ3 = generateZ3Variable(proList, numList, 'i', 'g')
    axiom, proEff, numEff = pseudoProgram2Logic(GenCode, actionList, proList, numList, propInitZ3, propGoalZ3, numInitZ3,
                                           numGoalZ3)
    axiom = simplify(And(axiom))
    return verifyTEAndG(domain, axiom, propInitZ3, numInitZ3, propGoalZ3, numGoalZ3)









