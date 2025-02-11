import copy
from collections import deque

from datastructure import Program
from domain import Switch
from util import getCoff, getLinearTermInCondition, isCremental, generateZ3Variable
from z3 import *

times=0

# check whether program is a pseudo primitive program
def isPseudo(GenCode, actList, proList, numList):
    if type(GenCode) == list:  # list type
        for program in GenCode:
            if isPseudo(program, actList, proList, numList) == False:
                return False
        return True

    elif type(GenCode) == Program:  # one program
        # no choice
        if GenCode.flag == 'IF' or GenCode.flag == 'IFe':  # if-else
            # print("PP contains IF")
            return False

        # action
        elif GenCode.flag == 'Seq':  # action seq
            act = actList[GenCode.actionList[0]]
            if len(act.subAction) != 0:
                # print("PP contains conditional effect")
                return False
            else:
                return True

        # loop
        elif GenCode.flag == 'Loop':

            if isPseudo(GenCode.actionList, actList, proList, numList) == False:  # check the loop body
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
                subSeqAxioms, loopBodyproEff, loopBodynumEff = pseudoProgram2Logic(GenCode.actionList, actList,proList, numList,
                                                                                   preproV, postproV, prenumV, postnumV,
                                                                                   {}, {})
                loopEff = {}

                # check static prop
                for k, v in loopBodyproEff.items():
                    if v == True or v == False:
                        # print("Loop body prop %s is not static" %k)
                        return False

                condition = GenCode.strcondition  # fix bug 1, Momo007

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
                    # print("Loop body more than one Cw in condition")
                    return False


                var = list(effInloop.keys())[0]  # get the effect modify value

                # print('-----------------------')
                # print(condition)
                for n in numIncond:
                    co = getCoff(n, condition)
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

            subAxioms,proEff,numEff = pseudoAction2Logic(actList[programList[i].actionList[0]],proList,numList,proEff,numEff)
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

            proTempEff = {}
            numTempEff = {}
            for p in proList:
                proTempEff[p] = preproV[p]

            for n in numList:
                numTempEff[n] = prenumV[n]

            subSeqAxioms,loopBodyproEff,loopBodynumEff = pseudoProgram2Logic(programList[i].actionList,actList,proList,numList,preproV, postproV, prenumV, postnumV, proTempEff,numTempEff)

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

    if flag == 1:
        #程序最顶层
        for p in proList:
            axioms.append(simplify(postproV[p] == proEff[p]))

        for n in numList:
            axioms.append(simplify(postnumV[n] == numEff[n]))

        times = 0

    return axioms,proEff,numEff


# translate unditional action to logic formulas
def pseudoAction2Logic(act,proList,numList,lastproEff,lastnumEff):
    axioms = []
    proEff = copy.deepcopy(lastproEff)
    numEff = copy.deepcopy(lastnumEff)

    # print('--------213123------')
    # print(lastnumEff)
    # # print(lastproEff)
    # print('--------2312312------')

    #proPre
    for p in act.preFormu:
        # print('+++++++++++++++++++++++++++')
        # print(f'{p.left} +  {p.op} + {p.right}')
        if int(p.right) == 0:
            exp = Not(lastproEff[p.left])
        else:
            exp = lastproEff[p.left]
        axioms.append(exp)

    #numPre
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


    #proEff
    for pp in act.effect_pos:
        proEff[pp] = True

    for pn in act.effect_neg:
        proEff[pn] = False

    #numEff
    for formu in act.effect_Metric:
        # print(f'{formu.left} {formu.op} {formu.right}')
        if formu.op == 'increase':
            numEff[formu.left] = eval('lastnumEff["' + formu.left + '"]' + '+' + formu.right)
        elif formu.op == 'decrease':
            numEff[formu.left] = eval('lastnumEff["' + formu.left + '"]' + '-' + formu.right)
        elif formu.op == 'assign':
            right = formu.right
            # print(right)
            for n in numList:
                right = right.replace(n,"lastnumEff['" + n + "']")
            right = eval(right)
            # print(right)
            numEff[formu.left] = right

    # print('------------numEFFF-------')
    # print(lastnumEff)
    # print(numEff)
    # print('------------numEFFFF-------')
    return axioms,proEff,numEff


# verify pseudo primitive program
def verifyPseudoProgram(GLINP,program,init,goal,actList,proList,numList):

    preproV, postproV, prenumV, postnumV = generateZ3Variable(proList, numList, 'i', 'o')
    init, goal = Switch.get(GLINP)(preproV, postproV, prenumV, postnumV)
    init = And(init)
    goal = And(goal)
    axiom,proEff,numEff = pseudoProgram2Logic(program,actList,proList,numList,preproV, postproV, prenumV, postnumV,{},{})
    # print(axiom)
    axiom = simplify(And(axiom))
    s = Solver()

    s.add(axiom)
    #print(s.check())

    #print()
    #print()
    #print('########################## verify ##################################')
    #print(f'init:  {init}')
    #print(f'goal:  {goal}')
    #print(f'axiom:  {axiom}')
    gaolAch = simplify(Not(Implies(And(axiom,init),goal)))


    for k, v in postproV.items():
        axiom = Exists(v, axiom)
    for k, v in postnumV.items():
        axiom = Exists(v, axiom)

    teminate = simplify(Not(Implies(init,axiom)))
    #print(f'goalAch:  {gaolAch}')
    #print(f'teminate: {teminate}')

    print()

    #goalachevability
    sg = Solver()
    sg.add(gaolAch)
    if sg.check() == sat:
        # not achevable
        m = sg.model()
        # counter={}
        # for p in proList:
        #     counter[p]=m[eval(p[1:-1])]
        # for n in numList:
        #     print(n[1:-1])
        #     counter[n]=m[eval(n[1:-1])].as_long()
        print("Goal reachable Failed proven!!!!")
        print("The counter Example:")
        print(m)

    else:
        print("Goal reachable successful proven!!!!")

    print()

    #termination and executability
    st = Solver()
    st.add(teminate)
    if st.check() == sat:
        # not
        m = st.model()
        # counter = {}
        # for p in proList:
        #     counter[p] = m[preproV[p]]
        # for n in numList:
        #     counter[n] = m[prenumV[n]].as_long()
        print("Termination and Executability Failed proven!!!!")
        print("The counter Example:")
        print(m)

    else:
        print("Termination and Executability successful proven!!!!")
        return 0









