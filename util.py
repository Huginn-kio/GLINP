from collections import deque
from z3 import *
import re

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

def replace_first(pattern, repl, string):
    # 使用maxsplit=1确保只替换第一个匹配
    return re.sub(pattern, repl, string, count=1)

def replace_last(text, old, new):
    """
    在文本中替换最后一个匹配的字符串。
    参数:
    text -- 原始字符串
    old -- 需要被替换的子字符串
    new -- 新的字符串，用于替换旧的字符串
    返回:
    修改后的字符串
    """
    # 找到最后一个old的位置
    start_idx = text.rfind(old)
    # 如果没有找到匹配，直接返回原始字符串
    if start_idx == -1:
        return text
    # 构造新的字符串
    return text[:start_idx] + new + text[start_idx + len(old):]

def custom_match(pattern, string, matchCount=2,flags=0):
    match_obj = re.match(pattern, string, flags)
    if not match_obj:
        return None
    # 获取正则表达式模式
    regex = match_obj.re.pattern  
    # 修改正则表达式模式，确保循环至少匹配两次
    modified_regex = regex.replace('*', '{'+str(matchCount)+',}')
    # 重新编译修改后的正则表达式
    modified_pattern = re.compile(modified_regex, flags)  
    # 使用修改后的正则表达式进行匹配
    return modified_pattern.match(string)

def lcs(str1, str2):
    sm = difflib.SequenceMatcher()
    sm.set_seqs(str1, str2)
    matching_blocks = [str1[m.a:m.a+m.size] for m in sm.get_matching_blocks()]
    return "".join(matching_blocks)
