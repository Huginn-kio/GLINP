import re
from collections import deque
from z3 import *
from verify.domain import Switch

# some common methods

def generateZ3Variable(proList, numList, pre, post):
    propZ3pre = {}
    propZ3post = {}
    numZ3pre = {}
    numZ3post = {}
    for item in proList:
        propZ3pre[str(item)] = Bool(str(item) + pre) # pro: num    Bool('num')
        propZ3post[str(item)] = Bool(str(item) + post)
    for item in numList:
        numZ3pre[str(item)] = Int(str(item) + pre)
        numZ3post[str(item)] = Int(str(item) + post)
    return propZ3pre, propZ3post, numZ3pre, numZ3post

def isCremental(exp,num):
    exp1 = substitute(exp,(num,num+1))
    if simplify(exp1 == exp) == True:
        return True
    else:
        return False

def getVariableFromFormula(formula):
    return re.findall(r"(\([\d\w]*\)\d?[io]?)", formula.__repr__())

def getCoff(var, condition):
    # global strList
    p = var
    strList = condition.split()
    # print(strList)
    symbs = deque()
    vars = deque()
    for str in strList:
        # print("########")
        # print("vars:", vars)
        # print("symbs:", symbs)
        if is_number(str):  # 原始数字保持不变加入
            # print("add num:", str)
            vars.append(str)
        elif str == "*" or str == "+" or str == "-" or str == "!=":
            if len(symbs) == 0:
                symbs.append(str)
            elif lessLevel(symbs[-1], str):
                symbs.append(str)
            else:
                #
                while len(symbs) > 0 and lessLevel(symbs[-1], str) == False:
                    v2 = vars.pop()
                    v1 = vars.pop()
                    op = symbs.pop()
                    t1 = isinstance(v1, int)
                    t2 = isinstance(v2, int)
                    if t1 and t2:  # both int
                        vars.append(cal(v1, v2, op))
                    elif t1:  # only t1 is int, ignore anoter
                        if (v2 == "#"):
                            vars.append(v1)
                        elif is_number(v2) and op == "*":
                            vars.append(cal(v1, int(v2), op))
                        else:
                            vars.append(v1)
                    elif t2:
                        if (v1 == "#"):
                            if op == '-':
                                vars.append(-v2)
                            else:
                                vars.append(v2)
                        elif is_number(v1) and op == "*":
                            vars.append(cal(int(v1), v2, op))
                        else:
                            vars.append(v2)
                    else:
                        vars.append("#")
                symbs.append(str)
        else:
            if (str.find(p) != -1):
                if (str[0] == "-"):
                    vars.append(-1)
                else:
                    vars.append(1)
            else:
                vars.append("#")
    while len(symbs) != 0:
        # print("########")
        # print("vars:", vars)
        # print("symbs:", symbs)
        v2 = vars.pop()
        v1 = vars.pop()
        op = symbs.pop()
        if op == "!=":
            if v1 == "#":
                v1 = 0
            elif v2 == "#":
                v2 = 0
        t1 = isinstance(v1, int)
        t2 = isinstance(v2, int)
        if t1 and t2:  # both int
            vars.append(cal(v1, v2, op))
        elif t1:  # only t1 is int, ignore anoter
            if (v2 == "#"):
                vars.append(v1)
            elif is_number(v2) and op == "*":
                vars.append(cal(v1, int(v2), op))
            else:
                vars.append(v1)
        elif t2:
            if (v1 == "#"):
                if op == '-':
                    vars.append(-v2)
                else:
                    vars.append(v2)
            elif is_number(v1) and op == "*":
                vars.append(cal(int(v1), v2, op))
            else:
                vars.append(v2)
        else:
            vars.append("#")
    # print("vars[0]:", vars[0])
    return vars[0]

def is_number(s):
    try:  # 如果能运行float(s)语句，返回True（字符串s是浮点数）
        float(s)
        return True
    except ValueError:  # ValueError为Python的一种标准异常，表示"传入无效的参数"
        pass  # 如果引发了ValueError这种异常，不做任何事情（pass：不做任何事情，一般用做占位语句）
    try:
        import unicodedata  # 处理ASCii码的包
        unicodedata.numeric(s)  # 把一个表示数字的字符串转换为浮点数返回的函数
        return True
    except (TypeError, ValueError):
        pass
    return False

def getLevel(str):
    if str == "!=":
        return 0
    elif str == "*":
        return 4
    elif str == "+" or str == "-":
        return 3
    else:
        assert (0)
        return -1


def lessLevel(op1, op2):
    l1 = getLevel(op1)
    l2 = getLevel(op2)
    if l1 < l2:
        return True
    else:  # pop
        return False


def cal(a, b, op):
    if op == "+":
        return a + b
    elif op == "-":
        return a - b
    elif op == "*":
        return a * b
    elif op == "!=":
        return a - b
    else:
        assert (0)
        return -1

def getLinearTermInCondition(cond,numList):
    #deal with a + b != c
    condproV, condproV, condnumV, condnumV = generateZ3Variable([], numList, '', '')
    for n in numList:
        cond = cond.replace(n, 'condnumV["' + n + '"]')
    cond = eval(cond)
    # print('pre: ', cond)
    cond = simplify(Not(cond), arith_lhs=True)
    cond = str(cond)
    # print(cond)
    conds = cond.split('==')
    # print(conds)
    conds[1] = conds[1].strip()
    # print(conds[1])
    if conds[1] == '0':
        cond = conds[0] + '+ ' +  conds[1]
    else:
        cond = conds[0] + '+ ' + '-' + conds[1]
    # print('post: ', cond)
    return cond

def is2DArray(a):
    for i in range(len(a)):
        if type(a[i]) is list:
            return True;
    return False;


#check whether program is acyclic

nodeIndex = {}
visit = []
stack = []
cyclePath = []
edgeTo = {}
g = []
maxDepth = 0
isDAG = True

def isAcyclic(numList, loopBodynumEff, prenumV):
    clearNodeIndex()
    initGraph(len(numList))
    for n in numList:
        loopBodynumEff[n] = simplify(loopBodynumEff[n])
    for n in numList:
        cur = prenumV[n].__repr__()
        eff = simplify(loopBodynumEff[n] - prenumV[n])
        ia = getNodeIndex(cur)
        if not is_int_value(eff) :
            varList = getVariableFromFormula(loopBodynumEff[n]);
            for item in varList:
                if not item.__eq__(cur):
                    ib = getNodeIndex(item)
                    addEdge(ia, ib)
                # print("add edge %d %s -> %d %s" %(ia,cur,ib,item))

    # print("Graph is following:")
    # printGraph()
    # print("#################")
    return checkDAG(len(numList));

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

#unconditional action to axiom
def uncondAct2Logic(act,proList,numList,lastproEff,lastnumEff):
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

# unconditional action with multiple last effect
def uncondAct2LogicWithMulLastEff(act,proList,numList,lastproEff,lastnumEff):
    axioms = []
    proEff = {}
    numEff = {}
    effCount = 1
    for n in numList:
        effCount =  max(len(lastnumEff[n]) , effCount)

    if effCount > 1:
        for n in numList:
            numEff[n] = []
        for p in proList:
            proEff[p] = []

    for i in range(effCount):
        lastproEffTemp = {}
        lastnumEffTemp = {}
        for n in numList:
            lastnumEffTemp[n] = lastnumEff[n][i]
        for p in proList:
            lastproEffTemp[n] = lastproEff[n][i]
        axiomsTemp,proEffTemp,numEffTemp = uncondAct2Logic(act, proList, numList, lastnumEffTemp, lastproEffTemp)
        if effCount > 1:
            axioms.append(axiomsTemp)
        else:
            axioms += axiomsTemp
        for n in numList:
            if effCount > 1:
                numEff[n].append(numEffTemp[n])
            else:
                numEff[n] = numEffTemp[n]
        for p in proList:
            if effCount > 1:
                proEff[p].append(proEffTemp[p])
            else:
                proEff[p] = proEffTemp[p]

    return axioms, proEff, numEff

# conditional action to logic formulas
def condAct2Logic(act, propZ3pre, propZ3post, numZ3pre, numZ3post, proList, numList):
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

#verify goal-achievability and teminating and executability properties
def verifyTEAndG(domain, axiom, propInitZ3, numInitZ3, propGoalZ3, numGoalZ3):
    states = []
    resultg = False
    resultt = False

    init, goal = Switch.get(domain)(propInitZ3, propGoalZ3, numInitZ3, numGoalZ3)

    init = And(init)
    goal = And(goal)

    # print("------------------------------------------------------")
    # print("---------------------trace axioms---------------------")
    # print("------------------------------------------------------")
    # print(axiom)

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

def getSortedNumV(numList,loopBodynumEff,prenumV):
    loopEff = {}
    cIncNums = {}
    vIncNums = {}
    linNums = {}
    for n in numList:
        loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])
        cur = prenumV[n].__repr__()
        if is_int_value(loopEff[n]) == True:
            # print("c-incremental:",prenumV[n].__repr__()+" = "+loopBodynumEff[n].__repr__())
            cIncNums[n] = loopEff[n]
        else:
            # linear by contain it self
            # print("linear:",prenumV[n].__repr__()+" = "+loopBodynumEff[n].__repr__())
            varList = getVariableFromFormula(loopBodynumEff[n]);
            # print(varList)
            if cur in varList:
                vIncNums[n] = loopEff[n]
            else:
                linNums[n] = loopBodynumEff[n]
    return cIncNums, vIncNums, linNums

def isContainChoice(GenCode) :
    for p in GenCode:
        if p.flag == 'IF':
            return True
    return False

def simplifyGenCode(GenCode) :
    i = 0
    while i < len(GenCode):
        if GenCode[i].flag == 'IFe' or ((GenCode[i].flag == 'IF' or GenCode[i].flag == 'Loop') and (GenCode[i].strcondition == 'False' or GenCode[i].strcondition == 'True')):
            del GenCode[i]
        else:
            if GenCode[i].flag != 'Seq':
                simplifyGenCode(GenCode[i].actionList)
            i += 1;