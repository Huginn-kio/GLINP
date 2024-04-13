import copy
import re
from enumrate import Enumrate
from util import replace_first,replace_last,custom_match
from datastructure import Action, NumExpression, State,Prog
from parsePddl.pythonpddl import pddlDomain,pddlProblem
from parsePddl.pythonpddl.pddlDomain import Action as ActOUT
actionList={}
book={}
ProBook={}
actionToLetter={}
letterToAction={}
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

# 简化生成程序，1.把无效的false结构去除；2.把无效的空If结构去除
def simplifyGenCode(GenProgram):
    i = 0
    while i < len(GenProgram):
        if (isinstance(GenProgram[i], str) == False and GenProgram[i].flag not in ('Seq')):
            simplifyGenCode(GenProgram[i].actionList)
            if str(GenProgram[i].condition) == 'False' or (
                    str(GenProgram[i].condition) == 'True' and GenProgram[i].flag == 'IFe'):
                del (GenProgram[i])
            else:
                i = i + 1
        else:
            i = i + 1
    j = 0
    n_IF = 0
    while j < len(GenProgram):
        if (isinstance(GenProgram[j], str) == False and GenProgram[j].flag in ('IF', 'IFe')):
            n_IF = n_IF + 1
        else:
            if n_IF == 1:
                GenProgram[j - 1].flag = 'Seq'
            n_IF = 0
        j = j + 1

    return GenProgram

#将结构格式（NumExpression形式）转化为eval可执行的字符串格式
def collectActionFormulaRecur(expr):
    res=''
    #print(expr.op)
        ##Metric
    if (expr.op in ['>', '<', '=', '>=', '<=']):
        if expr.op=='=':
            sign='=='
        else:
            sign=expr.op
        # if isinstance(expr.left,str) is False:
        #      print(expr.left.subformulas[0].asPDDL())
        res = expr.left+ sign+ expr.right
    elif "not" == expr.op:
        res = "not("+collectActionFormulaRecur(expr.left)+")"
    elif "and" == expr.op:
        res = "("+collectActionFormulaRecur(expr.left)+" and "+collectActionFormulaRecur(expr.right)+")"
    elif "or" == expr.op:
        res = "("+collectActionFormulaRecur(expr.left)+" or "+collectActionFormulaRecur(expr.right)+")"
    ##Propostion and ComplexFormula
    elif expr.op is None or expr.op == '':
        res = "("+expr.left+'==1'+")"
    #print(res)
    return res

# input: state of class State, action of class Operator
def is_applicable(state, action):
    #print(action.name)
    finalFormula='True'
    numState=state.numExpress
    numAction=copy.deepcopy(action.preMetric)
    preOp=''
    formula1=[]
    formula2=[]
    # or judge -R
    if len(action.preMetric)>0 and isinstance(action.preMetric[0],list):
        preOp='or'
        for metric in action.preMetric[0]:
            formula1.append(collectActionFormulaRecur(metric))
    else:
        preOp = 'and'
        for metric in action.preMetric:
           formula1.append(collectActionFormulaRecur(metric))
    merticFormula=(" "+preOp+" ").join(formula1)
    for prop in action.preFormu:
       formula2.append(collectActionFormulaRecur(prop))
    propFormula=(" "+preOp+" ").join(formula2)
    if merticFormula!="" and propFormula!="":
        finalFormula=merticFormula+ " "+preOp+" "+ propFormula
    elif merticFormula=="" and propFormula!="":
        finalFormula=propFormula
    elif propFormula=="" and merticFormula!="":
        finalFormula=merticFormula
    else:
        finalFormula='True'
    #print(len(propFormula))
    #print(len(merticFormula))
    #print("before~~~"+finalFormula)
    for atom in numState:
        finalFormula=finalFormula.replace(atom.left,str(atom.right))
    for atom in state.predicates.keys():
        finalFormula=finalFormula.replace(atom,str(state.predicates[atom]))
    #print("after~~~"+finalFormula)
    #print("result~~~"+str(eval(finalFormula)))
    if(eval(finalFormula)):
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

def stateTransition(plan_char,state):
    runState=state
    plan=StringToPlan(plan_char)
    for act in plan:
        if is_applicable(runState,actionList[act]):
            #runExam.printState()
            runState=apply_action(runState, actionList[act])
            #runExam.printState()
        else:
            return False,state 
    state=runState
    return True,state

def SymFormula(genPlan):
    for item in genPlan.examPos:
        inputs={}
        for atom in item.numExpress:
            inputs[atom.left]=float(atom.right)
        for (key,value) in item.predicates.items():
            inputs[key]=True if float(value)==1.0 else False
        genPlan.example.append({'Input': inputs, 'Output': True})

    for item in genPlan.examNeg:
        inputs={}
        for atom in item.numExpress:
            inputs[atom.left]=float(atom.right)
        for (key,value) in item.predicates.items():
            inputs[key]=True if float(value)==1.0 else False
        genPlan.example.append({'Input': inputs,'Output': False})
    condition=Enumrate(genPlan.example,variables, variablesP)
    return condition

def planToString(plan):
    plan_char=''
    for p in plan:
        plan_char+=actionToLetter[p]
    return plan_char

def StringToPlan(letters):
    plan=[]
    for l in letters:
        plan.append(letterToAction[l])
    return plan

def traversalPlanToFindSplitPoint(plan_char,r1,r2,start):
    i=start
    while i<len(plan_char)-1:
        isR1Match=custom_match(re.compile(r1),str(plan_char[0:i]),2)
        isR2Match=custom_match(re.compile(r2),str(plan_char[i:]),2)
        if(isR1Match and isR2Match):
            return i 
        i=i+1
    return -1

def complete(genPlan, state_plans):
    if genPlan is None or isinstance(genPlan,str):
        return genPlan 
    elif genPlan.flag=='Branch':
        Omega1=list()
        Omega2=list()
        for pair in state_plans:
            state=pair[0]
            plan=pair[1]
            plan_char=planToString(plan)
            firstAbbrChar=genPlan.firstAbbrChar if genPlan.firstAbbrChar is not None and  genPlan.firstAbbrChar!='#' else ''
            secondAbbrChar=genPlan.secondAbbrChar if genPlan.secondAbbrChar is not None and genPlan.secondAbbrChar!='#' else '' 
            r1=genPlan.firstActions.regex if isinstance(genPlan.firstActions,Prog) else '('+firstAbbrChar+')'
            r2=genPlan.secondActions.regex if isinstance(genPlan.secondActions,Prog) else '('+secondAbbrChar+')'
            planInR1,planInR2=plan_char,plan_char
            isR1Match=custom_match(re.compile(r1), plan_char,2)
            matchInR1Plan=isR1Match.group(1) if isR1Match else None
            isR2Match=custom_match(re.compile(r2),plan_char,2)
            matchInR2Plan=isR2Match.group(1) if isR2Match else None
            if isR1Match:
                isR1Applicable,runR1State=stateTransition(matchInR1Plan,state)
            if isR2Match:
                isR2Applicable,runR2State=stateTransition(matchInR2Plan,state)
            if(isR1Match and isR1Applicable):
                #需要在对可执行性进行验证
                genPlan.examPos.add(copy.deepcopy(state))
                Omega1.append((state,plan))
            elif (isR2Match and isR2Applicable):
                genPlan.examNeg.add(copy.deepcopy(state))
                Omega2.append((state,plan))
            else:
                print("BOOM!!!!")
                return genPlan
        genPlan.firstActions=complete(genPlan.firstActions, Omega1)
        genPlan.secondActions=complete(genPlan.secondActions, Omega2)
        genPlan.condition=SymFormula(genPlan)
    elif genPlan.flag=='Loop':
        Omega1=list()
        Omega2=list()
        r1=genPlan.regex
        r2=str(r1[1:-2])+replace_last(r1,'*','{1,}')
        firstAbbrChar=genPlan.firstAbbrChar if genPlan.firstAbbrChar is not None else ''
        secondAbbrChar=genPlan.secondAbbrChar if genPlan.secondAbbrChar is not None else ''
        subFirstActR1=genPlan.firstActions.regex if isinstance(genPlan.firstActions,Prog) else '('+firstAbbrChar+')'
        subSecindActR2= genPlan.secondActions.regex if isinstance(genPlan.secondActions,Prog) else '('+secondAbbrChar+')'
        lastRoundr1='('+str(r1[1:-2])+')'
        for pair in state_plans:
            state=pair[0]
            plan=pair[1]
            plan_char=planToString(plan)
            planInR1,planInR2,restR2Plan=plan_char,plan_char,plan_char
            isR1Match=custom_match(re.compile(r1), planInR1,2)
            matchInR1Plan=isR1Match.group(1) if isR1Match else None
            isR1Applicable,runR1State=stateTransition(matchInR1Plan,state)
            while(restR2Plan!=''):
                isR2Match=custom_match(re.compile(r2),planInR2,2)
                matchInR2Plan=isR2Match.group(1) if isR2Match else None  
                restR2Plan=replace_first(matchInR2Plan, '', planInR2) if isR2Match else restR2Plan
                if matchInR2Plan:
                    isR2Applicable,runR2State=stateTransition(matchInR2Plan,state)  
                isMatchlastRoundR1,islastRoundR1Applicable=False,False                
                if  not matchInR2Plan:
                    isMatchlastRoundR1=custom_match(re.compile(lastRoundr1),planInR2,2)
                    matchInlastRoundR1Plan=isMatchlastRoundR1.group(1) if isMatchlastRoundR1 else None
                    restR2Plan=replace_first(matchInlastRoundR1Plan, '', restR2Plan) 
                    planInR2=restR2Plan
                    islastRoundR1Applicable,runlastRoundR1State=stateTransition(matchInlastRoundR1Plan,state)    
                if(isR1Match and isR1Applicable and ((isR2Match and isR2Applicable) or (isMatchlastRoundR1 and islastRoundR1Applicable))):          
                    genPlan.examPos.add(copy.deepcopy(state))
                    subPlan=matchInR2Plan if matchInR2Plan else matchInlastRoundR1Plan
                    isSubPlanR1Match=custom_match(re.compile(subFirstActR1),subPlan,2)
                    matchInsubPlanR1Plan=isSubPlanR1Match.group(1) if isSubPlanR1Match else None 
                    restSubPlanR1Plan=replace_first(matchInsubPlanR1Plan, '', subPlan) if isSubPlanR1Match  else subPlan
                    isR2Applicable,runsubPlanR1State=stateTransition(matchInsubPlanR1Plan,state)  
                    issubPlanR2Match=custom_match(re.compile(subSecindActR2),restSubPlanR1Plan,2)
                    matchInsubPlanR2Plan=issubPlanR2Match.group(1) if issubPlanR2Match else None
                    subR1Plan=StringToPlan(matchInsubPlanR1Plan)
                    subR2Plan=StringToPlan(matchInsubPlanR2Plan)
                    Omega1.append((state,subR1Plan))
                    Omega2.append((runsubPlanR1State,subR2Plan))
                    state=runlastRoundR1State if  not matchInR2Plan else runR2State
                    planInR2=restR2Plan
                else:
                    break
                if restR2Plan=='':
                    genPlan.examNeg.add(copy.deepcopy(state))
        genPlan.firstActions=complete(genPlan.firstActions, Omega1)
        genPlan.secondActions=complete(genPlan.secondActions, Omega2)
        genPlan.condition=SymFormula(genPlan)              
    elif genPlan.flag=='Seq':
        Omega1=list()
        Omega2=list()
        firstAbbrChar=genPlan.firstAbbrChar if genPlan.firstAbbrChar is not None else ''
        secondAbbrChar=genPlan.secondAbbrChar if genPlan.secondAbbrChar is not None else ''
        r1=genPlan.firstActions.regex if isinstance(genPlan.firstActions,Prog) else '('+firstAbbrChar+')'
        r2=genPlan.secondActions.regex if isinstance(genPlan.secondActions,Prog) else '('+secondAbbrChar+')'
        r=r1+r2
        for pair in state_plans:
            state=pair[0]
            plan=pair[1]
            plan_char=planToString(plan)
            planInR1,planInR2,planInR=plan_char,plan_char,plan_char
            isRMatch=custom_match(re.compile(r),planInR,2)
            isR1Match=custom_match(re.compile(r1),planInR,2)
            matchInR1Plan=isRMatch.group(1) if isRMatch else None
            r1MatchPlan=StringToPlan(matchInR1Plan)
            restR1Plan=replace_first(matchInR1Plan, '', planInR)
            isR1Applicable,runR1State=stateTransition(matchInR1Plan,state)
            planInR2=restR1Plan
            isR2Match=custom_match(re.compile(r2),restR1Plan,2)
            matchInR2Plan=isR2Match.group(1) if isR2Match else None
            restR2Plan=replace_first(matchInR2Plan, '', restR1Plan)
            r2MatchPlan=StringToPlan(matchInR2Plan)
            isR2Applicable,runR2State=stateTransition(matchInR2Plan,runR1State)
            if(isRMatch and isR1Match and isR1Applicable and isR2Match and isR2Applicable and restR2Plan==''):
                Omega1.append((state,r1MatchPlan))
                Omega2.append((runR1State,r2MatchPlan))
            else:
                start=1
                while(start<len(plan)-1):
                    splitPoint=traversalPlanToFindSplitPoint(plan,r1,r2,start)
                    if splitPoint!=-1:
                        isSpliteR1Applicable,runSpliteR1State=stateTransition(plan[0:splitPoint],state)
                        isSpliteR2Applicable,runSpliteR2State=stateTransition(plan[splitPoint:],runSpliteR1State)
                        if isSpliteR1Applicable and isSpliteR2Applicable:
                            r1SpliteMatchPlan=StringToPlan(plan[0:splitPoint])
                            r2SpliteMatchPlan=StringToPlan(plan[splitPoint:])
                            Omega1.append((state,r1SpliteMatchPlan))
                            Omega2.append((runSpliteR1State,r2SpliteMatchPlan))
                            break
                        else:
                            start=splitPoint
                    else:
                        break
                return genPlan
        genPlan.firstActions=complete(genPlan.firstActions, Omega1)
        genPlan.secondActions=complete(genPlan.secondActions, Omega2)
    else:
        True
    return genPlan

# according to gencode to collect the state and generate the condition
def completeMain(GenProgram,domainfile,problemfile,planExamples, actionToLetterList, letterToActionList):
    # 1. get action list
    global actionToLetter
    global letterToAction
    global variables
    global variablesP
    actionList=getActionList(domainfile)
    actionToLetter=actionToLetterList
    letterToAction=letterToActionList
    # 2. get the initial state
    init=getInitState(problemfile)
    # 3. execute the plan and collect the states
    omega=list(zip(init, planExamples))
    # 4. generate the condition
    variables = []
    variablesP = []
    for atom in ProBook.keys():
        variablesP.append(atom)
    for atom in book.keys():
        variables.append(atom)
    print("\n1. Tracking the trace of performing solution to collect positive state and negative state as follows:")
    GenProgram= complete(GenProgram, omega)
    return GenProgram,actionList, variablesP, variables

