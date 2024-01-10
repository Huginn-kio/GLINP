import copy

from datastructure import Action, NumExpression, State
from enumrate import Enumrate
from parsePddl.pythonpddl import pddlDomain
from parsePddl.pythonpddl import pddlProblem
from parsePddl.pythonpddl.pddlDomain import Action as ActOUT
from datastructure import Program

actionList={}
book={}
ProBook={}
phi=1

# get action list
def getActionList(domainfile):
    dom = pddlDomain.parseDomainAndProblem(domainfile)
    for atom in dom.actions:
        tmp = Action()
        tmp.name = atom.name.upper()

        for pos in atom.get_eff(True):
            tmp.effect_pos.add(pos.asPDDL())

        for neg in atom.get_eff(False):
            tmp.effect_neg.add(neg.asPDDL())

        for item in atom.eff:
            if type(item) is not ActOUT and item.op in ['increase', 'decrease', 'assign']:
                tmpE = NumExpression(item.op, item.subformulas[0].asPDDL(), item.subformulas[1].asPDDL())
                tmp.effect_Metric.append(tmpE)

        for formula in atom.pre.subformulas:
            if (formula.op in ['>', '<', '=', '>=', '<=']):

                s = formula.subformulas[1].asPDDL()
                s = s.replace(".0", "")
                if "+" in s or "-" in s:
                    s = s[1:-1]
                    s = s.split(" ");
                    s = s[1] + s[0] + s[2]
                tmpE = NumExpression(formula.op, formula.subformulas[0].asPDDL(), s)
                tmp.preMetric.append(tmpE)
            else:
                if formula.op == "not":
                    tmpE = NumExpression("=", formula.subformulas[0].asPDDL(), "0")
                    tmp.preFormu.append(tmpE)
                elif formula.op == "or":
                    strList = []
                    strFormula = formula.asPDDL()
                    if (strFormula.find("or")):
                        strFormula = strFormula[3:-1]
                        strList = strFormula.split();
                        # print(strList)
                        for i in range(len(strList)):
                            if strList[i][0] == '(' and strList[i][-1] == ')':
                                pass
                            elif strList[i][0] == '(':
                                strList[i] = strList[i][1:]
                            elif strList[i][-1] == ')':
                                strList[i] = strList[i][:-1]

                        # print('##############or List#############')
                        # print(strList)
                        # print('##############or List#############')
                        orList = []
                        for i in range(len(strList) // 3):
                            orOneList = strList[i * 3:i * 3 + 3]
                            if orOneList[2][-2:] == ".0":
                                orOneList[2] = orOneList[2][:-2]
                            tmpE = NumExpression(orOneList[0], orOneList[1], orOneList[2])
                            orList.append(tmpE)
                        tmp.preMetric.append(orList)


                else:
                    tmpE = NumExpression("=", formula.subformulas[0].asPDDL(), "1")
                    tmp.preFormu.append(tmpE)

        k = 0
        for items in atom.eff:
            if type(items) is ActOUT:
                subtmp = Action()

                for formula in items.pre.subformulas:
                    if (formula.op in ['>', '<', '=', '>=', '<=']):

                        s = formula.subformulas[1].asPDDL()
                        if "+" in s or "-" in s:
                            s = s[1:-1]
                            s = s.split(" ")
                            s = s[1] + s[0] + s[2]
                        tmpE = NumExpression(formula.op, formula.subformulas[0].asPDDL(), s)
                        subtmp.preMetric.append(tmpE)
                    else:
                        if formula.op == "not":
                            tmpE = NumExpression("=", formula.subformulas[0].asPDDL(), "0")
                        else:
                            tmpE = NumExpression("=", formula.subformulas[0].asPDDL(), "1")
                        subtmp.preFormu.append(tmpE)

                for pos in items.get_eff(True):
                    subtmp.effect_pos.add(pos.asPDDL())

                for neg in items.get_eff(False):
                    subtmp.effect_neg.add(neg.asPDDL())

                for item in items.eff:
                    if type(item) is not ActOUT and item.op in ['increase', 'decrease', 'assign']:
                        tmpE = NumExpression(item.op, item.subformulas[0].asPDDL(), item.subformulas[1].asPDDL())
                        subtmp.effect_Metric.append(tmpE)
                tmp.subAction.append(subtmp)
                subtmp.name = str(atom.name.upper() + str(k))
                actionList[subtmp.name] = subtmp
                k = k + 1
        actionList[atom.name.upper()] = tmp
    return actionList


# get init state
def getInitState(problemfileSet):
    init=[]
    # get initial states - init
    # get Probook - propositional variables
    for problemfile in problemfileSet:
        prob= pddlProblem.parseDomainAndProblem(problemfile)
        estado_objetivo = State([])
        k=0
        for atom in prob.initialstate:
            # print('initial state:', atom.asPDDL())          #FExpression   op,subexps
            if isinstance(atom,pddlProblem.Formula):        #Formula       subformulas, op, is_effect, is_numeric
                # print('proposition: ', atom.subformulas[0].asPDDL())
                ProBook[atom.subformulas[0].asPDDL()]=k     #proposition
                k=k+1
                if atom.op=="not":
                    estado_objetivo.add_predicate(atom.subformulas[0].asPDDL(),0)
                else :
                    estado_objetivo.add_predicate(atom.subformulas[0].asPDDL(),1)
            else:
                # print('numeric expression: ', atom.subexps[0].asPDDL(), atom.op, atom.subexps[1].asPDDL())
                tmpE=NumExpression(atom.op,atom.subexps[0].asPDDL(),atom.subexps[1].asPDDL())
                estado_objetivo.add_numExpress(tmpE)
        init.append(copy.deepcopy(estado_objetivo))
    # get book - numeric variables
    if len(problemfileSet)!=0:
        for i in range(len(estado_objetivo.numExpress)):
            # print('expression: ', estado_objetivo.numExpress[i].left, estado_objetivo.numExpress[i].op, estado_objetivo.numExpress[i].right)
            book[estado_objetivo.numExpress[i].left]=i
    return init


# input: state of class State, action of class Operator
def is_applicable(state, action):
    numState=state.numExpress
    numAction=copy.deepcopy(action.preMetric)
    for atom in numState:
        i=0
        while i <  len(numAction):
            if isinstance(numAction[i], list):
                j = 0
                while j <  len(numAction[i]):
                    numAction[i][j].left=numAction[i][j].left.replace(atom.left,atom.right)
                    numAction[i][j].right=numAction[i][j].right.replace(atom.left,atom.right)
                    j=j+1
            else:
                numAction[i].left=numAction[i].left.replace(atom.left,atom.right)
                numAction[i].right=numAction[i].right.replace(atom.left,atom.right)
            i=i+1
    Exp="True "
    for item in action.preFormu:
        if(state.predicates[item.left] is None or state.predicates[item.left]!=int(item.right)):
            return False
    for m in numAction:
        if isinstance(m, list):
            orAxioms = 'False '
            for n in m:
                if n.op == "=":
                    n.op = "=="
                orAxioms+=" or "+n.left+n.op+n.right
            Exp+=" and ("+orAxioms+")"
        else:
            if m.op == "=":
                m.op = "=="
            Exp+=" and "+m.left+m.op+m.right
    #print(Exp)
    if(eval(Exp)):
        return True
    else:
        return False


# update state with the action
def apply_action(state, action):
    state_ret = copy.deepcopy(state)
    # update propositional variable
    state_ret.add_predicates(action.effect_pos)
    state_ret.remove_predicates(action.effect_neg)
    #update numeric variable
    state_ret.update_metric(action.effect_Metric)
    #update state with conditional effect
    for act in action.subAction:
        if is_applicable(state,actionList[act.name]):
            state_ret=apply_action(state_ret,actionList[act.name])
    return state_ret


# judge if it is a simple loop
def isSimpleLoop(GenCode):
    for atom in GenCode.actionList: # string or program
        # not simple loop or if
        if(isinstance(atom,Program) and atom.flag!='Seq'):
            return False
    return True


# judge if it matches done
def ifMatchDone(GenCode, start):
    if start >= len(GenCode):
        return True
    for atom in GenCode[start:]: # string or program
        if(isinstance(atom,Program) and atom.flag == 'Seq'):
            return False
    return True

#GenCode：程序骨架
#init：初始状态集
#exam：规划解集合
#isroot：初始化是0，回溯到0代表不需要回溯了
# to execute and collect the states
def excuteModelProgress(GenCode,init,exam,is_root):
    #hasExecute：表示子结构是否执行
    hasExecute=False

    # print('flag: ', len(GenCode), GenCode[0].flag)
    # one time per state
    for i in range(len(init)):
        j=0
        # runline：表示运行到规划解的具体索引
        runline=0
        runExam=init[i].copy()
        #runExam.printState()
        tmpGenCode = copy.deepcopy(GenCode)
        runStateslist=[]
        #是否已经进入过If结构
        IfExecute=False
        #seq和Loop执行后的状态,IF和IFe执行前状态
        SeqAndLoop_State=''
        #20221206
        # if(is_root==0):
        #     print("--------i--------:"+str(i))
        #runStateslist.append({'State': copy.deepcopy(runExam), 'RegexIndex': 0, 'CaseIndex':0})
        while j < len(GenCode) and runline < len(exam[i]):
            # loop or if statement which is not simple
            #print(exam[i])
            # 嵌套结构（if结构且前面的结构未成功匹配、多层循环结构）
            if((GenCode[j].flag=="Loop" or (GenCode[j].flag=="IF" and IfExecute==False)) and isSimpleLoop(GenCode[j])==False):
                #print(1)
                #上一轮是否匹配成功
                lastExcute=False
                #本轮是否匹配成功
                contExecute=True
                #保存运行前程序状态
                preState=''
                # 本轮匹配成功且规划解未匹配完，继续尝试匹配
                while contExecute==True and runline<len(exam[i]):
                    # 临时深拷贝当前程序状态
                    preState=copy.deepcopy(runExam)
                    preGenCode_al=copy.deepcopy(GenCode[j].actionList)
                    preGenCode = copy.deepcopy(GenCode)
                    # prerunline=runline
                    #pState(preState)
                    #1.san,2.two.
                    # return subProgram with example, the number of action sequence that has been used, ruccrent state, symbol that says whether succeed
                    # 对嵌套结构进行递归匹配，返回（收集好的程序结构及数据集、成功匹配的规划解长度、运行后的结果程序状态、是否匹配成功标识）
                    GenCode[j].actionList,runline1,runExam,contExecute=excuteModelProgress(GenCode[j].actionList,[runExam],[exam[i][runline:]],is_root+1)
                    #print("The final res:"+str(contExecute))
                    #res=runExam
                    # subRegex accepts the subsequence --- this state is added in the positive state
                    #匹配成功
                    if(contExecute):
                        lastExcute=True
                        hasExecute=True
                        inputs={}
                        #add 20221206
                        runStateslist.append({'State': preState, 'RegexIndex': j, 'CaseIndex':runline, 'preGenCode':preGenCode})
                        for atom in preState.numExpress:
                            inputs[atom.left]=float(atom.right)
                        for (key,value) in preState.predicates.items():
                            inputs[key]=True if float(value)==1.0 else False
                        GenCode[j].examPos.add(copy.deepcopy(preState))
                        runline=runline+runline1
                    else:
                        GenCode[j].actionList=preGenCode_al
                        runExam=preState
                        hasExecute = lastExcute
                        # if res=='':
                        #     return GenCode,0,'',hasExecute
                        #return GenCode,0,runExam,hasExecute
                        break
                    # IF结构只需要一轮匹配
                    if GenCode[j].flag == "IF":
                        break
                    #print("current line:"+str(runline))
                #最后一层循环程序状态或者一开始就匹配不了的程序状态或者IF不匹配的程序状态
                if (GenCode[j].flag == "Loop"):
                    IfExecute= False
                    GenCode[j].examNeg.add(copy.deepcopy(runExam))
                    SeqAndLoop_State = runExam
                elif (GenCode[j].flag == "IF" and contExecute == False):
                    IfExecute = False
                    GenCode[j].examNeg.add(copy.deepcopy(preState))
                    SeqAndLoop_State = preState
                else:
                    IfExecute= True
                    SeqAndLoop_State = preState
                j=j+1
                #print("index"+str(j)+"   line:"+str(runline))

            # simple loop or simple if or seq statement ----
            else:
                step=len(GenCode[j].actionList)
                pattern = "".join(exam[i][runline:runline + step])  # obtain action sequence π
                #simple loop - Loop body is Seq
                if(GenCode[j].flag=="Loop"):
                    IfExecute= False
                    loopBody=''
                    isCanApply=True
                    for atom in GenCode[j].actionList:
                        loopBody+=atom.actionList[0]
                    if(loopBody==pattern):
                        GenCode[j].examPos.add(copy.deepcopy(runExam))
                        #add 20221206
                        runStateslist.append({'State': copy.deepcopy(runExam), 'RegexIndex': j, 'CaseIndex':runline,'preGenCode':copy.deepcopy(GenCode)})
                        for item in GenCode[j].actionList:
                            if is_applicable(runExam,actionList[item.actionList[0]]):
                                #runExam.printState()
                                runExam=apply_action(runExam, actionList[item.actionList[0]])
                                #runExam.printState()
                                hasExecute=True
                            else:
                                isCanApply=False
                                break
                        if isCanApply==True:
                            runline=runline+step
                        else:
                            GenCode[j].examNeg.add(copy.deepcopy(runExam))
                            j=j+1
                    else:
                        GenCode[j].examNeg.add(copy.deepcopy(runExam))
                        j=j+1
                    SeqAndLoop_State = runExam

                # simple if  - if body is Seq
                #
                elif(GenCode[j].flag=="IF" and IfExecute==False):
                    ifBody=''
                    isCanApply=True
                    #runExam.printState()
                    #PrintProgram(GenCode[j].actionList,0)
                    for atom in GenCode[j].actionList:
                        ifBody+=atom.actionList[0]                                        # obtain regex sequence r1
                    # check whether action sequence in exam == action sequence in ifBody
                    # if YES, add recurrent state to exampos of condition of if statement
                    tmp_runExam = copy.deepcopy(runExam)
                    tmp_GenCode = copy.deepcopy(GenCode)
                    tmp_runline = runline
                    if(ifBody==pattern):                                                  # r1 accept π ?
                        #runExam.printState()
                        #print(GenCode[j].examPos)
                        #add 20221206
                        #PrintProgram(GenCode,0)

                        tmp_j=j
                        for item in GenCode[j].actionList:
                            if is_applicable(runExam,actionList[item.actionList[0]]):
                                runExam=apply_action(runExam, actionList[item.actionList[0]]) # get the following state after performing the action sequence
                                # print('------following states--------------')
                                # for formula123 in runExam.numExpress:
                                #     print(formula123.left, formula123.op, formula123.right)
                                # print('------following states--------------')
                            else:
                                isCanApply=False
                                break
                        if isCanApply==True:
                            runStateslist.append(
                                {'State': tmp_runExam, 'RegexIndex': tmp_j, 'CaseIndex': tmp_runline,
                                 'preGenCode':tmp_GenCode })
                            GenCode[j].examPos.add(copy.deepcopy(tmp_runExam))
                            hasExecute=True
                            IfExecute=True
                            j=j+1
                            runline=runline+step
                        else:
                            GenCode[j].examNeg.add(copy.deepcopy(tmp_runExam))
                            j=j+1
                    else:                                                               #r1 not accept π
                        GenCode[j].examNeg.add(copy.deepcopy(runExam))
                        j=j+1
                    SeqAndLoop_State = tmp_runExam
                # simple empty if - if body is emptyAction
                elif(GenCode[j].flag=="IFe" and IfExecute==False):
                    #print("1.IFe")
                    runStateslist.append({'State': copy.deepcopy(runExam), 'RegexIndex': j, 'CaseIndex':runline,'preGenCode':copy.deepcopy(GenCode)})
                    GenCode[j].examPos.add(copy.deepcopy(runExam))
                    j=j+1
                    IfExecute=True
                    SeqAndLoop_State = runExam
                # simple seq
                elif(GenCode[j].flag=="Seq"):
                    seqBody=GenCode[j].actionList[0]
                    IfExecute=False
                    isCanApply=True
                    #print(pattern)
                    #print(seqBody)
                    if(seqBody==pattern):
                        for item in GenCode[j].actionList:
                            if is_applicable(runExam,actionList[item]):
                                #print("squence++++++")
                                #runExam.printState()
                                runExam=apply_action(runExam, actionList[item])
                                hasExecute=True
                                #runExam.printState()
                            else:
                                isCanApply=False
                                break
                        if isCanApply==True:
                            j=j+1
                            runline=runline+step
                        else:
                            hasExecute=False
                            #return tmpGenCode,runline,'',hasExecute
                            if len(runStateslist)>0:
                                inputs={}
                                #print(runStateslist)
                                backState=runStateslist[-1]
                                runExam=backState['State']
                                j=backState['RegexIndex']+1
                                runline=backState['CaseIndex']
                                GenCode=backState['preGenCode']
                                IfExecute=False
                                for atom in runExam.numExpress:
                                    inputs[atom.left]=float(atom.right)
                                for (key,value) in runExam.predicates.items():
                                    inputs[key]=True if float(value)==1.0 else False
                                GenCode[j-1].examNeg.add(copy.deepcopy(runExam))
                                runStateslist.pop()
                                hasExecute=True
                            else:
                                break
                    else:
                        hasExecute=False
                        #return tmpGenCode,runline,'',hasExecute
                        if len(runStateslist)>0:
                            inputs={}
                            #print(runStateslist)
                            backState=runStateslist[-1]
                            runExam=backState['State']
                            j=backState['RegexIndex']+1
                            runline=backState['CaseIndex']
                            GenCode=backState['preGenCode']
                            IfExecute=False
                            for atom in runExam.numExpress:
                                inputs[atom.left]=float(atom.right)
                            for (key,value) in runExam.predicates.items():
                                inputs[key]=True if float(value)==1.0 else False
                            GenCode[j-1].examNeg.add(copy.deepcopy(runExam))
                            runStateslist.pop()
                            hasExecute=True
                        else:
                            break
                    SeqAndLoop_State = runExam
                else:
                    # if结构，并且已经前面有结构匹配到IfExecute==True
                    if ((GenCode[j].flag in ("IF", "IFe") and IfExecute == True)):
                        #把之前状态代入到当前结构的反状态（不是当前状态），因为后续是取前面if语句条件的取反并集，这一块逻辑已经覆盖，无需
                        GenCode[j].examNeg.add(copy.deepcopy(SeqAndLoop_State))
                    j=j+1
                #是否回溯到根节点，
            #print("isroot:"+str(is_root)+";runline:"+str(runline)+";len(exam[i]):"+str(len(exam[i]))+";j:"+str(j)+"; len(GenCode):"+str( len(GenCode)))
            if (runline<len(exam[i]) and j == len(GenCode)) and( hasExecute==False or is_root==0 ):
                hasExecute=False
                inputs={}
                #print(runStateslist)
                while len(runStateslist)>0 and j==len(GenCode):
                    IfExecute=False
                    backState=runStateslist[-1]
                    runExam=backState['State']
                    j=backState['RegexIndex']+1
                    runline=backState['CaseIndex']
                    GenCode=backState['preGenCode']
                    #print('888888888rico888888888888888888888')
                    #PrintProgram(GenCode,0)
                    for atom in runExam.numExpress:
                        inputs[atom.left]=float(atom.right)
                    for (key,value) in runExam.predicates.items():
                        inputs[key]=True if float(value)==1.0 else False
                    GenCode[j-1].examNeg.add(copy.deepcopy(runExam))
                    runStateslist.pop()
                    hasExecute=True
        if(j < len(GenCode) and GenCode[j].flag == "Loop"):
            GenCode[j].examNeg.add(copy.deepcopy(runExam))
        if(j < len(GenCode) and runline==len(exam[i]) and ifMatchDone(GenCode,j) == False):
            hasExecute=False
        if(j < len(GenCode) and runline==len(exam[i]) and ifMatchDone(GenCode,j) == True):
            temp = j
            while temp < len(GenCode):
                if GenCode[temp].flag in ('IF','IFe'):
                    GenCode[temp].examNeg.add(copy.deepcopy(SeqAndLoop_State))
                else:
                    GenCode[temp].examNeg.add(copy.deepcopy(runExam))
                temp += 1

    if hasExecute == False:
            GenCode = copy.deepcopy(tmpGenCode)
            runline = 0
    else:
        for j in range(len(GenCode)):
            for item in GenCode[j].examPos:
                inputs={}
                for atom in item.numExpress:
                    inputs[atom.left]=float(atom.right)
                for (key,value) in item.predicates.items():
                    inputs[key]=True if float(value)==1.0 else False
                GenCode[j].example.append({'Input': inputs, 'Output': True})
            GenCode[j].examPos.clear()
            for item in GenCode[j].examNeg:
                inputs={}
                for atom in item.numExpress:
                    inputs[atom.left]=float(atom.right)
                for (key,value) in item.predicates.items():
                    inputs[key]=True if float(value)==1.0 else False
                GenCode[j].example.append({'Input': inputs,'Output': False})
            GenCode[j].examNeg.clear()
    # print('Nested: ',GenCode[0].example, runline, runExam.numExpress[0].right, hasExecute)
    return GenCode,runline,runExam,hasExecute


def PrintProgram1(GenProgram, depth):
    i = 0
    start = False
    endif = False
    prestr = ''
    for i in range(depth):
        prestr += ' '

    for i in range(len(GenProgram)):
        if GenProgram[i].flag in ('IF', 'IFe') and (
                (i < len(GenProgram) - 1 and GenProgram[i + 1].flag not in ('IF', 'IFe')) or i == len(GenProgram) - 1):
            endif = True
        hasNext = ';' if i < len(GenProgram) - 1 else ''
        if (GenProgram[i].flag == 'Seq'):
            for j in range(len(GenProgram[i].actionList)):
                if j < len(GenProgram[i].actionList) - 1:
                    print(prestr + GenProgram[i].actionList[j] + ';')
                else:
                    print(prestr + GenProgram[i].actionList[j] + hasNext)
            start = False
            endif = False
            # print("Seq"+str(length))
        elif (GenProgram[i].flag == 'IFe'):
            cond = str(GenProgram[i].condition)
            if start == False:
                print(prestr + "if " + GenProgram[i].strcondition + " then")
            elif start == True and endif == False:
                print(prestr + "elif " + GenProgram[i].strcondition + " then")
            else:
                print(prestr + "else ")
            print(prestr + prestr + '    EMPTYaction')
            if start == False and endif == True:
                print(prestr + "fi" + hasNext)
            elif start == True and endif == False:
                True
            elif start == False and endif == False:
                True
            else:
                print(prestr + "fi" + hasNext)
            start = True

        elif (GenProgram[i].flag == 'IF'):
            cond = str(GenProgram[i].condition)
            if start == False:
                print(prestr + "if " + GenProgram[i].strcondition + " then")
            elif start == True and endif == False:
                print(prestr + "elif " + GenProgram[i].strcondition + " then")
            else:
                print(prestr + "else ")
            # for j in GenProgram[i].example:
            #     print(j)
            PrintProgram1(GenProgram[i].actionList, depth + 4)
            # print("IF"+str(length))
            if start == False and endif == True:
                print(prestr + "fi" + hasNext)
            elif start == True and endif == False:
                True
            elif start == False and endif == False:
                True
            else:
                print(prestr + "fi" + hasNext)
            start = True

        elif (GenProgram[i].flag == 'Loop'):
            cond = str(GenProgram[i].condition)
            print(prestr + "while " + GenProgram[i].strcondition + " do")
            # for j in GenProgram[i].example:
            #     print(j)
            PrintProgram1(GenProgram[i].actionList, depth + 4)
            start = False
            endif = False
            # print("LOOP"+str(length))
            print(prestr + "od" + hasNext)


def PrintProgram2(GenProgram,length,depth):
    global phi
    i=0
    start=False
    endif=False
    prestr=''
    for i in range(depth):
        prestr+=' '

    for i in range(len(GenProgram)):
        if GenProgram[i].flag in ('IF','IFe') and ((i<len(GenProgram)-1 and GenProgram[i+1].flag not in ('IF','IFe')) or i==len(GenProgram)-1):
            endif=True
        hasNext = ';' if i< len(GenProgram)-1 else ''
        if(GenProgram[i].flag=='Seq'):
            length=length+1
            for j in range(len(GenProgram[i].actionList)):
              if j< len(GenProgram[i].actionList)-1:
                print(prestr+GenProgram[i].actionList[j]+';')
              else:
                print(prestr+GenProgram[i].actionList[j]+hasNext)
            start=False
            endif=False
            # print("Seq"+str(length))
        elif(GenProgram[i].flag=='IFe'):
            cond=str(GenProgram[i].condition)
            if(GenProgram[i].strcondition=="phi" and endif==False):
              GenProgram[i].strcondition+=str(phi)
              phi+=1
            length=length+len(str(cond).split(" "))+1+str(cond).count('And')+cond.count('Not')+cond.count('Or')
            if start==False:
              print(prestr+"if "+GenProgram[i].strcondition+" then")
            elif start==True and endif==False:
              print(prestr+"elif "+GenProgram[i].strcondition+" then")
            else:
              print(prestr+"else ")
            print(prestr+prestr+'    EMPTYaction')
            if start==False and endif==True:
              print(prestr+"fi"+hasNext)
            elif start==True and endif==False:
              True
            elif start==False and endif==False:
              True
            else:
              print(prestr+"fi"+hasNext)
            start=True

        elif(GenProgram[i].flag=='IF'):
            cond=str(GenProgram[i].condition)
            length=length+len(str(cond).split(" "))+1+str(cond).count('And')+cond.count('Not')+cond.count('Or')
            if(GenProgram[i].strcondition=="phi" and endif==False):
              GenProgram[i].strcondition+=str(phi)
              phi+=1
            if start==False:
                  print(prestr+"if "+GenProgram[i].strcondition+" then")
            elif start==True and endif==False:
              print(prestr+"elif "+GenProgram[i].strcondition+" then")
            else:
              print(prestr+"else ")
            # for j in GenProgram[i].example:
            #     print(j)
            length=PrintProgram2(GenProgram[i].actionList,length,depth+4)
            # print("IF"+str(length))
            if start==False and endif==True:
                  print(prestr+"fi"+hasNext)
            elif start==True and endif==False:
              True
            elif start==False and endif==False:
                  True
            else:
              print(prestr+"fi"+hasNext)
            start=True

        elif(GenProgram[i].flag=='Loop'):
            cond=str(GenProgram[i].condition)
            length=length+len(str(cond).split(" "))+1+str(cond).count('And')+cond.count('Not')+cond.count('Or')
            if(GenProgram[i].strcondition=="phi"):
              GenProgram[i].strcondition+=str(phi)
              phi+=1
            print(prestr+"while "+GenProgram[i].strcondition+" do")
            # for j in GenProgram[i].example:
            #     print(j)
            length=PrintProgram2(GenProgram[i].actionList,length,depth+4)
            start=False
            endif=False
            # print("LOOP"+str(length))
            print(prestr+"od"+hasNext)
    if  len(GenProgram)>1:
        length=length+len(GenProgram)-1
    return length


def PrintNoElseProgram(GenProgram, length, depth):
    global phi
    i = 0
    prestr = ''
    for i in range(depth):
        prestr += ' '

    for i in range(len(GenProgram)):

        hasNext = ';' if i < len(GenProgram) - 1 else ''

        # seq
        if (GenProgram[i].flag == 'Seq'):
            length = length + 1
            for j in range(len(GenProgram[i].actionList)):
                if j < len(GenProgram[i].actionList) - 1:
                    print(prestr + GenProgram[i].actionList[j] + ';')
                else:
                    print(prestr + GenProgram[i].actionList[j] + hasNext)
            # print("Seq"+str(length))

        # ife
        elif (GenProgram[i].flag == 'IFe'):
            cond = str(GenProgram[i].condition)
            if (GenProgram[i].strcondition == "phi"):
                GenProgram[i].strcondition += str(phi)
                phi += 1
            length = length + len(str(cond).split(" ")) + 1 + str(cond).count('And') + cond.count('Not') + cond.count(
                'Or')

            print(prestr + "if " + GenProgram[i].strcondition + " then")
            print(prestr + prestr + '    EMPTYaction')
            print(prestr + "fi" + hasNext)

        # if
        elif (GenProgram[i].flag == 'IF'):
            cond = str(GenProgram[i].condition)
            length = length + len(str(cond).split(" ")) + 1 + str(cond).count('And') + cond.count('Not') + cond.count(
                'Or')
            if (GenProgram[i].strcondition == "phi"):
                GenProgram[i].strcondition += str(phi)
                phi += 1
            print(prestr + "if " + GenProgram[i].strcondition + " then")
            length = PrintNoElseProgram(GenProgram[i].actionList, length, depth + 4)
            print(prestr + "fi" + hasNext)

        # loop
        elif (GenProgram[i].flag == 'Loop'):
            cond = str(GenProgram[i].condition)
            length = length + len(str(cond).split(" ")) + 1 + str(cond).count('And') + cond.count('Not') + cond.count(
                'Or')
            if (GenProgram[i].strcondition == "phi"):
                GenProgram[i].strcondition += str(phi)
                phi += 1
            print(prestr + "while " + GenProgram[i].strcondition + " do")
            # for j in GenProgram[i].example:
            #     print(j)
            length = PrintProgram2(GenProgram[i].actionList, length, depth + 4)
            # print("LOOP"+str(length))
            print(prestr + "od" + hasNext)
    if len(GenProgram) > 1:
        length = length + len(GenProgram) - 1
    return length


# 将原本的GenCode转化为if...else嵌套形式
def GenCode2GenCodeWithElse(GenProgram):
    GenCode = []
    i = 0
    while i < len(GenProgram):
        if (GenProgram[i].flag in ('Seq', 'Loop')):
            GenCode.append(copy.deepcopy(GenProgram[i]))
            i = i + 1
        elif (GenProgram[i].flag in ('IF', "IFe")):
            lastIfIndex = i
            while lastIfIndex < len(GenProgram):
                if GenProgram[lastIfIndex].flag not in ('IF', "IFe"):
                    break
                else:
                    lastIfIndex = lastIfIndex + 1

            IfCode = copy.deepcopy(GenProgram[i])
            GenCode.append(IfCode)
            # if else if else number >=3 then i is if and [i+1,lastIfIndex-1] is elif
            if i + 1 < lastIfIndex - 1:
                ElseAction = GenCode2GenCodeWithElse(GenProgram[i + 1:lastIfIndex])
                ElseCode = Program('Else', ElseAction)
            else:
                ElseCode = copy.deepcopy(GenProgram[i + 1])
                ElseCode.flag = 'Else' if GenProgram[i + 1].flag != 'IFe' else 'ElseE'
            GenCode.append(ElseCode)
            # lastIfIndex is the next not if and then we do not need to add 1 for i
            i = lastIfIndex
    return GenCode


def PrintProgramWithElse(GenProgram, length, depth):
    global phi
    i = 0
    start = False
    endif = False
    prestr = ''
    for i in range(depth):
        prestr += ' '
    for i in range(len(GenProgram)):
        if GenProgram[i].flag in ('IF', 'IFe', 'Else', 'ElseE') and (
                (i < len(GenProgram) - 1 and GenProgram[i + 1].flag not in ('IF', 'IFe', 'Else', 'ElseE')) or i == len(
            GenProgram) - 1):
            endif = True
        hasNext = ';' if i < len(GenProgram) - 1 else ''
        if (GenProgram[i].flag == 'Seq'):
            length = length + 1
            for j in range(len(GenProgram[i].actionList)):
                if j < len(GenProgram[i].actionList) - 1:
                    print(prestr + GenProgram[i].actionList[j] + ';')
                else:
                    print(prestr + GenProgram[i].actionList[j] + hasNext)
            start = False
            endif = False
            # print("Seq"+str(length))
        elif (GenProgram[i].flag in ('IF', 'Else', 'IFe', 'ElseE')):
            cond = str(GenProgram[i].condition)
            length = length + len(str(cond).split(" ")) + 1 + str(cond).count('And') + cond.count('Not') + cond.count(
                'Or')
            if (GenProgram[i].strcondition == "phi" and endif == False):
                GenProgram[i].strcondition += str(phi)
                phi += 1
            if GenProgram[i].flag in ('IF', 'IFe'):
                print(prestr + "if " + GenProgram[i].strcondition + " then")
            else:
                print(prestr + "else ")
                # for j in GenProgram[i].example:
            #     print(j)
            if GenProgram[i].flag in ('IF', 'Else'):
                length = PrintProgramWithElse(GenProgram[i].actionList, length, depth + 4)
            else:
                print(prestr + prestr + '    EMPTYaction')
            # print("IF"+str(length))
            if endif == True:
                print(prestr + "fi" + hasNext)
            start = True
        elif (GenProgram[i].flag == 'Loop'):
            cond = str(GenProgram[i].condition)
            length = length + len(str(cond).split(" ")) + 1 + str(cond).count('And') + cond.count('Not') + cond.count(
                'Or')
            if (GenProgram[i].strcondition == "phi"):
                GenProgram[i].strcondition += str(phi)
                phi += 1
            print(prestr + "while " + GenProgram[i].strcondition + " do")
            # for j in GenProgram[i].example:
            #     print(j)
            length = PrintProgramWithElse(GenProgram[i].actionList, length, depth + 4)
            start = False
            endif = False
            # print("LOOP"+str(length))
            print(prestr + "od" + hasNext)
    if len(GenProgram) > 1:
        length = length + len(GenProgram) - 1
    return length


# according to gencode to collect the state and generate the condition
def complete(GenCode,domainfile,problemfile,planExamples):
    # 1. get action list
    actionList=getActionList(domainfile)
    # 2. get the initial state
    init=getInitState(problemfile)
    # 3. execute the plan and collect the states
    GenCode, runline, runExam, hasExecute = excuteModelProgress(GenCode, init, planExamples, 0)
    # 4. generate the condition
    variables = []
    variablesP = []
    for atom in ProBook.keys():
        variablesP.append(atom)
    for atom in book.keys():
        variables.append(atom)
    print("\n1. Tracking the trace of performing solution to collect positive state and negative state as follows:")
    PrintProgram1(GenCode, 0)
    Enumrate(GenCode, variables, variablesP, True)
    return GenCode, actionList, variablesP, variables