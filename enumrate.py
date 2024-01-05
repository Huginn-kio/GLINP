# -*- coding: utf-8 -*
from z3 import *
import sys
import re
import time

start = time.process_time()


def Add(a, b):
    return a + b


def Sub(a, b):
    return a - b


def Inc(a):
    a = a + 1
    return a


def Dec(a):
    a = a - 1
    return a


def Mod(a, b):
    # if a>=0:
    return a % b


# def z3Mod(a,b):
#     return If(a>=0,a%b,-(a%b))

def Ge(a, b):
    return a >= b


def Gt(a, b):
    return a > b


def Equal(a, b):
    return a == b


def Unequal(a, b):
    return a != b


def OR(a, b):
    return (a or b)


def z3OR(a, b):
    return Or(a, b)


def AND(a, b):
    return (a and b)


def z3AND(a, b):
    return And(a, b)


def NOT(a):
    return (not a)


def z3NOT(a):
    return Not(a)


def Zero():
    return 0


def One():
    return 1


# def ITE(a,b,c):
#    if(a):
#        return b
#    else:
#        return c

# def z3ITE(a,b,c):
#    return If(a,b,c)

def Two():
    return 2


def Seven():
    return 7


def Three():
    return 3


def Four():
    return 4


def Five():
    return 5


# def ModTest(a,b,c):
#    return a%b==c

vocabulary = [{'Input': ['Int', 'Int'], 'Output': 'Int', 'Function_name': 'Add', 'arity': 2},
              {'Input': ['Int', 'Int'], 'Output': 'Int', 'Function_name': 'Sub', 'arity': 2},
              {'Input': ['Int'], 'Output': 'Int', 'Function_name': 'Inc', 'arity': 1},
              {'Input': ['Int'], 'Output': 'Int', 'Function_name': 'Dec', 'arity': 1},
              {'Input': ['Int', 'Int'], 'Output': 'Bool', 'Function_name': 'Equal', 'arity': 2},
              {'Input': ['Int', 'Int'], 'Output': 'Bool', 'Function_name': 'Unequal', 'arity': 2},
              # {'Input': ['Int', 'Int'], 'Output': 'Int', 'Function_name': 'Mod','arity':2},
              # {'Input': ['Int','Int'], 'Output': 'Bool', 'Function_name': 'Ge','arity':2},
              {'Input': ['Int', 'Int'], 'Output': 'Bool', 'Function_name': 'Gt', 'arity': 2},
              # {'Input': ['Int', 'Int'], 'Output': 'Bool', 'Function_name': 'Unequal', 'arity': 2},
              {'Input': ['Bool', 'Bool'], 'Output': 'Bool', 'Function_name': 'OR', 'arity': 2},
              {'Input': ['Bool', 'Bool'], 'Output': 'Bool', 'Function_name': 'AND', 'arity': 2},
              {'Input': ['Bool'], 'Output': 'Bool', 'Function_name': 'NOT', 'arity': 1},
              {'Input': [], 'Output': 'Int', 'Function_name': 'Zero', 'arity': 0},
              # {'Input': [], 'Output': 'Int', 'Function_name': 'Three', 'arity': 0},
              # {'Input': [], 'Output': 'Int', 'Function_name': 'Four', 'arity': 0},
              {'Input': [], 'Output': 'Int', 'Function_name': 'One', 'arity': 0},
              # {'Input': [], 'Output': 'Int', 'Function_name': 'Five', 'arity': 0},
              # {'Input': [], 'Output': 'Int','Function_name': 'Two', 'arity': 0},
              # {'Input': ['Bool','Int','Int'],'Output':'Int','Function_name':'ITE','arity':3},
              # {'Input': [], 'Output': 'Int','Function_name': 'Seven', 'arity': 0},
              # {'Input': ['Int','Int','Int'],'Output':'Bool','Function_name':'ModTest','arity':3}
              ]
Goal = {'value': [], 'type': ''}
FunExg = {'Add': Add, 'Sub': Sub, 'Inc': Inc, 'Dec': Dec, 'Ge': Ge, 'Three': Three, 'Four': Four,
          'Gt': Gt, 'OR': OR, 'AND': AND, 'NOT': NOT, 'Equal': Equal,
          'Unequal': Unequal, 'Zero': Zero, 'One': One, 'Two': Two, 'Five': Five, 'Seven': Seven}
Z3FunExg = {'Add': Add, 'Sub': Sub, 'Inc': Inc, 'Dec': Dec, 'Ge': Ge, 'Three': Three, 'Four': Four,
            'Gt': Gt, 'OR': z3OR, 'AND': z3AND, 'NOT': z3NOT, 'Equal': Equal,
            'Unequal': Unequal, 'Zero': Zero, 'One': One, 'Two': Two, 'Five': Five, 'Seven': Seven}
Var = []
VarP = []
MapstrM = []


def initial(variables, pvariables):
    cnt = 65
    k = 0
    for var in variables:
        v = chr(cnt) + str(30 + k % 10)
        v1 = v + '1'
        z3v = Int(v)
        z3v1 = Int(v1)
        FunExg[v] = z3v
        FunExg[v1] = z3v1
        Z3FunExg[v] = z3v
        Z3FunExg[v1] = z3v1
        MapstrM.append([v, var])
        Var.append([z3v, z3v1, v])
        cnt = cnt + 1
        k = k + 1
    for var in pvariables:
        v = chr(cnt) + str(30 + k % 10)
        v1 = v + '1'
        z3v = Bool(v)
        z3v1 = Bool(v1)
        FunExg[v] = z3v
        FunExg[v1] = z3v1
        Z3FunExg[v] = z3v
        Z3FunExg[v1] = z3v1
        MapstrM.append([v, var])
        VarP.append([z3v, z3v1, v])
        cnt = cnt + 1
        k = k + 1


def Solveit(Code, Goal):
    count = len(Code.example)
    if count < 1:
        return [False, False]
    # print("count:",count)
    SigSet = []
    ExpSet = []
    SizeOneExps = []
    SizeOneExps.append(
        {'Input': [], 'Output': 'Int', 'Expression': 'Zero', 'z3Expression': [Zero(), Zero()], 'arity': 0, 'size': 1})
    SizeOneExps.append(
        {'Input': [], 'Output': 'Int', 'Expression': 'One', 'z3Expression': [One(), One()], 'arity': 0, 'size': 1})
    for atom in Var:
        SizeOneExps.append(
            {'Input': ['Int'], 'Output': 'Int', 'Expression': atom[2], 'z3Expression': [atom[0], atom[1]], 'arity': 1,
             'size': 1})
    for atom in VarP:
        SizeOneExps.append(
            {'Input': ['Bool'], 'Output': 'Bool', 'Expression': atom[2], 'z3Expression': [atom[0], atom[1]], 'arity': 1,
             'size': 1})
    for i in SizeOneExps:
        Goal1 = []
        if (i['arity'] == 0):
            for num in range(count):
                Goal1.append(FunExg[i['Expression']]())
            if Goal1 not in SigSet:
                SigSet.append(Goal1)
                i['Output_data'] = Goal1
                ExpSet.append(i)
                if Goal1 == Goal['value'] and i['Output'] == Goal['type']:
                    return i['z3Expression']
        else:
            for atom in MapstrM:
                if i['Expression'] == atom[0]:
                    for j in Code.example:
                        O = j['Input'][atom[1]]
                        Goal1.append(O)
                    if Goal1 not in SigSet:
                        SigSet.append(Goal1)
                        i['Output_data'] = Goal1
                        ExpSet.append(i)
                        if Goal1 == Goal['value'] and i['Output'] == Goal['type']:
                            return i['z3Expression']

    for i in vocabulary:
        if (i['arity'] == 1):
            for j in ExpSet:
                if j['size'] == 1:
                    Goal1 = []
                    TempExp = ''
                    if (i['Input'][0] == j['Output']):
                        TempExp = i['Function_name'] + '(' + j['Expression'] + ')'
                        z3TempExp1 = Z3FunExg[i['Function_name']](j['z3Expression'][0])
                        z3TempExp2 = Z3FunExg[i['Function_name']](j['z3Expression'][1])
                        # print(j['Output_data'])
                        for k in j['Output_data']:
                            O = FunExg[i['Function_name']](k)
                            Goal1.append(O)
                        if Goal1 not in SigSet:
                            SigSet.append(Goal1)
                            ExpSet.append(
                                {'Input': i['Input'], 'Output': i['Output'], 'Expression': TempExp,
                                 'z3Expression': [z3TempExp1, z3TempExp2], 'arity': i['arity'],
                                 'size': 2, 'Output_data': Goal1})
                        if Goal1 == Goal['value'] and i['Output'] == Goal['type']:
                            return [z3TempExp1, z3TempExp2]
    i = 3
    while (True):
        temporarySet = []
        for f in vocabulary:
            m = f['arity']
            if (m == 1):
                for j in ExpSet:
                    try:
                        Goal1 = []
                        TempExp = ''
                        if ((j['size'] == i - 1) and (f['Input'] == j['Output'])):
                            TempExp = f['Function_name'] + '(' + j['Expression'] + ')'
                            z3TempExp1 = Z3FunExg[f['Function_name']](j['z3Expression'][0])
                            z3TempExp2 = Z3FunExg[f['Function_name']](j['z3Expression'][1])
                            for k in j['Output_data']:
                                O = FunExg[f['Function_name']](k)
                                Goal1.append(O)
                            if Goal1 not in SigSet:
                                SigSet.append(Goal1)
                                ExpSet.append({'Input': f['Input'], 'Output': f['Output'],
                                               'Expression': TempExp, 'z3Expression': [z3TempExp1, z3TempExp2],
                                               'arity': f['arity'], 'size': i, 'Output_data': Goal1})
                            if Goal1 == Goal['value'] and f['Output'] == Goal['type']:
                                return [z3TempExp1, z3TempExp2]
                    except ZeroDivisionError:
                        pass
                    continue
            elif (m == 2):
                for num1 in range(1, i - 1):
                    for num2 in range(1, i - 1):
                        if (num1 + num2 == i - 1):
                            for choose1 in ExpSet:
                                if (choose1['size'] == num1):
                                    for choose2 in ExpSet:
                                        if (choose2['size'] == num2):
                                            if ((f['Input'][0] == choose1['Output']) and (
                                                    f['Input'][1] == choose2['Output'])):
                                                try:
                                                    Goal1 = []
                                                    TempExp = ''
                                                    TempExp = f['Function_name'] + '(' + choose1['Expression'] + ',' + \
                                                              choose2['Expression'] + ')'
                                                    z3TempExp1 = Z3FunExg[f['Function_name']](
                                                        choose1['z3Expression'][0], choose2['z3Expression'][0])
                                                    z3TempExp2 = Z3FunExg[f['Function_name']](
                                                        choose1['z3Expression'][1], choose2['z3Expression'][1])
                                                    for k, h in zip(choose1['Output_data'], choose2['Output_data']):
                                                        O = FunExg[f['Function_name']](k, h)
                                                        Goal1.append(O)
                                                    if Goal1 not in SigSet:
                                                        SigSet.append(Goal1)
                                                        ExpSet.append(
                                                            {'Input': f['Input'], 'Output': f['Output'],
                                                             'Expression': TempExp,
                                                             'z3Expression': [z3TempExp1, z3TempExp2],
                                                             'arity': f['arity'], 'size': i, 'Output_data': Goal1})
                                                    # print(SigSet)
                                                    if Goal1 == Goal['value'] and f['Output'] == Goal['type']:
                                                        return [z3TempExp1, z3TempExp2]
                                                except ZeroDivisionError:
                                                    pass
                                                continue
            elif (m == 3):
                if (f['Function_name'] == 'ModTest'):
                    # print('!!!!!!!!!!!!!!!!!!')
                    for num1 in range(1, i - 1):
                        for num2 in range(1, i - 1):
                            for num3 in range(1, i - 1):
                                if (num1 + num2 + num3 == i - 1):
                                    for choose1 in ExpSet:
                                        if (choose1['size'] == num1):
                                            for choose2 in ExpSet:
                                                if (choose2['size'] == num2):
                                                    for choose3 in ExpSet:
                                                        if (choose3['size'] == num3 and choose3['arity'] == 0):
                                                            if ((f['Input'][0] == choose1['Output']) and (
                                                                    f['Input'][1] == choose2['Output']) and (
                                                                    f['Input'][2] == choose3['Output'])):
                                                                try:
                                                                    Goal1 = []
                                                                    TempExp = ''
                                                                    TempExp = f['Function_name'] + '(' + choose1[
                                                                        'Expression'] + ',' + choose2[
                                                                                  'Expression'] + ',' + choose3[
                                                                                  'Expression'] + ')'
                                                                    z3TempExp1 = Z3FunExg[f['Function_name']](
                                                                        choose1['z3Expression'][0],
                                                                        choose2['z3Expression'][0],
                                                                        choose3['z3Expression'][0])
                                                                    z3TempExp2 = Z3FunExg[f['Function_name']](
                                                                        choose1['z3Expression'][1],
                                                                        choose2['z3Expression'][1],
                                                                        choose3['z3Expression'][1])
                                                                    for k, h, g in zip(choose1['Output_data'],
                                                                                       choose2['Output_data'],
                                                                                       choose3['Output_data']):
                                                                        O = FunExg[f['Function_name']](k, h, g)
                                                                        Goal1.append(O)
                                                                    if Goal1 not in SigSet:
                                                                        SigSet.append(Goal1)
                                                                        ExpSet.append(
                                                                            {'Input': f['Input'], 'Output': f['Output'],
                                                                             'Expression': TempExp,
                                                                             'z3Expression': [z3TempExp1, z3TempExp2],
                                                                             'arity': f['arity'], 'size': i,
                                                                             'Output_data': Goal1})
                                                                    if Goal1 == Goal['value'] and f['Output'] == Goal[
                                                                        'type']:
                                                                        return [z3TempExp1, z3TempExp2]
                                                                except ZeroDivisionError:
                                                                    pass
                                                                continue
                else:
                    for num1 in range(1, i - 1):
                        for num2 in range(1, i - 1):
                            for num3 in range(1, i - 1):
                                if (num1 + num2 + num3 == i - 1):
                                    for choose1 in ExpSet:
                                        if (choose1['size'] == num1):
                                            for choose2 in ExpSet:
                                                if (choose2['size'] == num2):
                                                    for choose3 in ExpSet:
                                                        if (choose3['size'] == num3):
                                                            if ((f['Input'][0] == choose1['Output']) and (
                                                                    f['Input'][1] == choose2['Output']) and (
                                                                    f['Input'][2] == choose3['Output'])):
                                                                try:
                                                                    Goal1 = []
                                                                    TempExp = ''
                                                                    TempExp = f['Function_name'] + '(' + choose1[
                                                                        'Expression'] + ',' + choose2[
                                                                                  'Expression'] + ',' + choose3[
                                                                                  'Expression'] + ')'
                                                                    z3TempExp1 = Z3FunExg[f['Function_name']](
                                                                        choose1['z3Expression'][0],
                                                                        choose2['z3Expression'][0],
                                                                        choose3['z3Expression'][0])
                                                                    z3TempExp2 = Z3FunExg[f['Function_name']](
                                                                        choose1['z3Expression'][1],
                                                                        choose2['z3Expression'][1],
                                                                        choose3['z3Expression'][1])
                                                                    for k, h, g in zip(choose1['Output_data'],
                                                                                       choose2['Output_data'],
                                                                                       choose3['Output_data']):
                                                                        O = FunExg[f['Function_name']](k, h, g)
                                                                        Goal1.append(O)
                                                                    if Goal1 not in SigSet:
                                                                        SigSet.append(Goal1)
                                                                        ExpSet.append(
                                                                            {'Input': f['Input'], 'Output': f['Output'],
                                                                             'Expression': TempExp,
                                                                             'z3Expression': [z3TempExp1, z3TempExp2],
                                                                             'arity': f['arity'], 'size': i,
                                                                             'Output_data': Goal1})
                                                                    if Goal1 == Goal['value'] and f['Output'] == Goal[
                                                                        'type']:
                                                                        return [z3TempExp1, z3TempExp2]
                                                                except ZeroDivisionError:
                                                                    pass
                                                                continue
        i = i + 1



def isSimpleLoop(GenCode):
    for atom in GenCode.actionList:
        if (atom.flag != 'Seq'):
            return False
    return True


def Enumrate(GenCode, variables, variablesP, flag):
    k = 0
    IFeCond = ''
    IFeIndex = -1
    start = False
    isnowEnterIf = False
    if (flag == True):
        initial(variables, variablesP)
    while k < len(GenCode):
        if start == False and (GenCode[k].flag == "IFe" or GenCode[k].flag == "IF"):
            IFeCond = True
            start = True
            isnowEnterIf = True
        if ((GenCode[k].flag == "Loop" or GenCode[k].flag == "IF") and isSimpleLoop(GenCode[k]) == False):
            Goal = {'value': [], 'type': ''}
            for i in GenCode[k].example:
                Goal['value'].append(i['Output'])
            Goal['type'] = 'Bool'
            e = Solveit(GenCode[k], Goal)
            GenCode[k].condition = e[0]
            str1 = str(e[0])
            for atom in MapstrM:
                str1 = str1.replace(atom[0], atom[1])
            GenCode[k].strcondition = str1
            Enumrate(GenCode[k].actionList, [], [], False)
            # 对IF的条件进行补全(对Solveit枚举得到的公式，与前面所有已经生成的非空动作的条件集合取反，再取并集)
            if GenCode[k].flag == "IF":
                # 主要是收集IFeCond和合并前IF分支条件做特殊处理，该程序不满足以下条件时（1.第一个IF分支结构 ;  2.该程序为第二个IF分支结构，同时上一个分支结构为空动作且为第一个分支结构)
                if not (isnowEnterIf == True or ((isnowEnterIf == False and GenCode[k - 1].flag == 'IFe') and (
                        (k - 2 >= 0 and GenCode[k - 2].flag not in ('IFe', 'IF')) or (k - 2 < 0)))):
                    GenCode[k].condition = z3.simplify(And(Not(IFeCond), e[0]))
                    str1 = str(z3.simplify(And(Not(IFeCond), e[0])))
                    for atom in MapstrM:
                        str1 = str1.replace(atom[0], atom[1])
                    GenCode[k].strcondition = str1
                    IFeCond = And(IFeCond, e[0])
                else:
                    IFeCond = e[0]
            # IF结构已遍历完，触发对IFe的条件进行补全，并将start从True置为False
            elif start == True and GenCode[k].flag == "Loop":
                GenCode[IFeIndex].condition = z3.simplify(Not(IFeCond))
                str1 = str(z3.simplify(Not(IFeCond)))
                for atom in MapstrM:
                    str1 = str1.replace(atom[0], atom[1])
                GenCode[IFeIndex].strcondition = str1
                start = False
        elif (GenCode[k].flag == "Loop"):
            Goal = {'value': [], 'type': ''}
            for i in GenCode[k].example:
                Goal['value'].append(i['Output'])
            Goal['type'] = 'Bool'
            e = Solveit(GenCode[k], Goal)
            GenCode[k].condition = e[0]
            str1 = str(e[0])
            for atom in MapstrM:
                str1 = str1.replace(atom[0], atom[1])
            GenCode[k].strcondition = str1
            if start == True:
                GenCode[IFeIndex].condition = z3.simplify(Not(IFeCond))
                str1 = str(z3.simplify(Not(IFeCond)))
                for atom in MapstrM:
                    str1 = str1.replace(atom[0], atom[1])
                GenCode[IFeIndex].strcondition = str1
            start = False
        elif (GenCode[k].flag == "IF"):
            Goal = {'value': [], 'type': ''}
            for i in GenCode[k].example:
                Goal['value'].append(i['Output'])
            Goal['type'] = 'Bool'
            e = Solveit(GenCode[k], Goal)
            # 该程序为第一个IF分支结构 或   该程序为第二个IF分支结构，同时上一个分支结构为空动作且为第一个分支结构
            if isnowEnterIf == True or ((isnowEnterIf == False and GenCode[k - 1].flag == 'IFe') and (
                    (k - 2 >= 0 and GenCode[k - 2].flag not in ('IFe', 'IF')) or (k - 2 < 0))):
                GenCode[k].condition = e[0]
                str1 = str(e[0])
                for atom in MapstrM:
                    str1 = str1.replace(atom[0], atom[1])
                GenCode[k].strcondition = str1
            else:
                # 20230716
                GenCode[k].condition = z3.simplify(And(Not(IFeCond), e[0]))
                str1 = str(z3.simplify(And(Not(IFeCond), e[0])))
                for atom in MapstrM:
                    str1 = str1.replace(atom[0], atom[1])
                GenCode[k].strcondition = str1
            IFeCond = And(IFeCond, e[0])

        elif (GenCode[k].flag == "IFe"):
            IFeIndex = k
        # seq and start flags the front has if
        else:
            if start == True:
                GenCode[IFeIndex].condition = z3.simplify(Not(IFeCond))
                str1 = str(z3.simplify(Not(IFeCond)))
                for atom in MapstrM:
                    str1 = str1.replace(atom[0], atom[1])
                GenCode[IFeIndex].strcondition = str1
            start = False
        isnowEnterIf = False
        k = k + 1
    if start == True and IFeIndex != -1:
        GenCode[IFeIndex].condition = z3.simplify(Not(IFeCond))
        str1 = str(z3.simplify(Not(IFeCond)))
        for atom in MapstrM:
            str1 = str1.replace(atom[0], atom[1])
        print(len(GenCode))
        GenCode[IFeIndex].strcondition = str1
    return GenCode


