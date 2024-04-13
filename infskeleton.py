import copy
import difflib
import re
from functools import reduce
#from util import lcs
from datastructure import Item, Prog
from constant import emptyAction,emptyActionName,emptyRegex,MIN_CHAR,MAX_CHAR,MIN_LARGE_CHAR,MAX_LARGE_CHAR

# map the letter (cd)* to the ABC...
letterToNestList={}
# map the ABC... to the letter (cd)*
nestToLetterList={}
# the empty action

phi=1

def lcs(str1, str2):
    sm = difflib.SequenceMatcher()
    sm.set_seqs(str1, str2)
    matching_blocks = [str1[m.a:m.a+m.size] for m in sm.get_matching_blocks()]
    return "".join(matching_blocks)

# regex just includes the lowercase letter
def printRegex1(RegexSet):
    res = []
    for Regex in RegexSet:
        str = ''
        for item in Regex:
            str+=item.name
        res.append(str)
    return res

# regex includes the Uppercase letter
def printRegex2(RegexSet):
    res = []
    for Regex in RegexSet:
        str = ''
        for item in Regex:
            if(item.flag == 'S'):
                str+=item.name
            else:
                str+=item.symbol
        res.append(str)
    return res

# regex does not include the repeated regex
def printNoRepeatedRegex(RegexStr):
    res = []
    for regex in RegexStr:
        if regex not in res:
            res.append(regex)
    return res

def getLoopBody(Regex, start, end):
    """
    :param Regex: a list of Item such as [Item('a','a','S'),Item('b','b','S'),Item('a','a','S'),Item('b','b','S')]
    :param start: the start position of the loop
    :param end: the end position of the loop
    :return: the body of the loop
    """
    # to get the name of the [start,end) loop
    s = ''
    for i in range(start, end):
        s += Regex[i].name
    return s

def combine(Regex,start,end,size):
    """
    :param Regex: a list of Item such as [Item('a','a','S'),Item('b','b','S'),Item('a','a','S'),Item('b','b','S')]
    :param start: the start position of the loop
    :param end: the end position of the loop
    :param size: the length of the repeated part of the plan
    """
    loopBody = []
    loopName = ''
    flag = 'L'
    # to get the body of the repeated part of the plan
    i = start
    while(i < start + size):
        if(Regex[i].flag == 'S'):
            loopBody.append(Regex[i])
            loopName += Regex[i].name
        else:
            loopBody.append(Regex[i].body)
            loopName += Regex[i].symbol
            # if the loop body is a sequence of single action then it is a loop else it is a nest loop such as (d(c)*)*
            flag = 'C'
        i = i + 1
    # to del the original repeated part of the plan
    del(Regex[start:end])
    newname = '(' + loopName + ')*'
    if newname not in letterToNestList.keys():
        letterToNestList[newname] = chr(65+len(letterToNestList))
        nestToLetterList[chr(65+len(nestToLetterList))] = newname
    newitem = Item(loopBody,newname,flag)
    newitem.symbol = letterToNestList[newname]
    # to insert the new repeated part of the plan
    Regex.insert(start,newitem)
    return Regex

# just for single loop
def isAlign(regex,i):
    """
    :param regex: a list of loop Item list  such as (dacb)*d and (acbd)*
    :param i: the cur position of the loop in the loop regex such as (dacb)*d the index of (dacb)* is 0
    """
    # to get the body of the loop
    loop_pattern = ''
    startl = 0
    while(startl<len(regex[i].body) and regex[i].body[startl].flag == 'S'):
        loop_pattern += regex[i].body[startl].name
        startl += 1
    # print("loop_pattern:",loop_pattern)
    # to get the single action sequence after the loop
    after_pattern = ''
    starta = i+1
    while(starta<len(regex) and regex[starta].flag == 'S'):
        after_pattern += regex[starta].name
        starta += 1
    # print("after_pattern:",after_pattern)
    # to get the common part of the loop body and the single action sequence after the loop
    k = 0
    while(k<len(loop_pattern) and k<len(after_pattern) and loop_pattern[k] == after_pattern[k]):
        k += 1
    # if they have common part
    if(k>0):
        pos=k
        for l in range(1,k+1):
            str1 = regex[i].name[1:1 + l]
            str2 = regex[i].name[1 + l:-2]
            newbody = '(' + str2 + str1 + ')*'
            if(newbody in letterToNestList.keys()):
                pos=l
                break
        # below is not satisfied (dacb)*da and (acbd)*
        # to get the new name of the loop
        # str1 = regex[i].name[1:1+k]  # the first part of the loop body
        # str2 = regex[i].name[1+k:-2] # the second part of the loop body
        # newbody = '(' + str2 + str1 + ')*'
        # Flase to represent that the loop is not align; k to represent the length of the common part; newbody to represent the new name of the loop
        return False,pos,newbody
    else:
        return True,0,''

def indentifyRegex(ItemPlan):
    """
        ItemPlan: a list of Item list such as [[Item('a','a','S'),Item('b','b','S')],[Item('a','a','S'),Item('b','b','S')]]
        return: a list of regex such as ['ab','ab']
    """
    regexSet = []
    # every Item in ItemPlan is a list of Item which stands for a plan such as [Item('a','a','S'),Item('b','b','S')]
    for Regex in ItemPlan:
        # the length of the repeated part of the plan
        size = 1
        # the length of the repeated part of the plan must be less than half of the length of the plan
        while(size<=len(Regex)/2):
            # the start position of the plan
            i = 0
            # the start position of the plan must be less than the length of the plan
            while(i<len(Regex)):
                l = len(Regex)
                j = i
                # [j,j+size) ... [j,j+(n-1)*size) is the repeated part of the plan
                n = 2
                while(j+n*size<=l and getLoopBody(Regex,j,j+size) == getLoopBody(Regex,j+(n-1)*size,j+n*size)):
                    n = n + 1
                # if the repeated part of the plan is more than 2 times, then we can combine them
                if(n>2):
                    # [j,j+(n-1)*size) is the repeated part of the plan
                    combine(Regex,j,j+(n-1)*size,size)
                # to get the next start position of the plan
                i = i + 1
            size = size + 1
        # to get the regex of the plan
        regexSet.append(Regex)

    return regexSet

# just for single loop
# regex need to be modified if it can be aligned
def alignRegex(regexSet):
    R_regexSet = []
    for regex in regexSet:
        for i in range(len(regex)):
            # only loop body can be aligned
            if(regex[i].flag == 'L'):
                # to judge whether the loop is aligned
                res,pos,newbody = isAlign(regex,i)
                # print(res,pos,newbody)
                # if the loop is not aligned and the newbody is in the letterToNestList then we can align the loop
                if(res == False and newbody in letterToNestList.keys()):
                    temp = copy.deepcopy(regex[i])
                    temp.body = temp.body[pos:] + temp.body[:pos]
                    temp.name = newbody
                    temp.symbol = letterToNestList[newbody]
                    del(regex[i])
                    regex.insert(i+pos,temp)
        # to get the aligned regex
        R_regexSet.append(regex)
    return R_regexSet

# regex needn't to be modified
def alternateRegex(unrepeatedRegex,commonRegex):
    AlterSubRegex = []
    i = 0
    # to add altersubregex for every commonRegex such as commonRegex is A and unrepeatedRegex is [dA,A] then we can add []A[] and to fill the [] with unrepeatedRegex
    while i <= len(commonRegex):
        AlterSubRegex.append([])
        i += 1
    # to foreach the unrepeatedRegex to fill the [] with unrepeatedRegex
    # use two pointer to foreach the unrepeatedRegex and the commonRegex
    for regex in unrepeatedRegex:
        l1 = 0
        l2 = 0
        subregex = ''
        # to handle the common part
        while(l1<len(regex) and l2<len(commonRegex)):
            if(regex[l1] == commonRegex[l2]):
                if subregex != '':
                    if subregex not in AlterSubRegex[l2]:
                        AlterSubRegex[l2].append(subregex)
                    subregex = ''
                else:
                    if emptyAction not in AlterSubRegex[l2]:
                        AlterSubRegex[l2].append(emptyAction)
                l1 += 1
                l2 += 1
            else:
                subregex += regex[l1]
                l1 += 1
        # to handle the rested part of regex
        while(l1<len(regex)):
            subregex += regex[l1]
            l1 += 1
        # to handle the last regex
        if subregex != '' and subregex not in AlterSubRegex[l2]:
            AlterSubRegex[l2].append(subregex)
        elif subregex == '' and emptyAction not in AlterSubRegex[l2]:
            AlterSubRegex[l2].append(emptyAction)

    # to handle the only #
    for index in range(len(AlterSubRegex)):
        if( len(AlterSubRegex[index])==1 and AlterSubRegex[index][0] == emptyAction):
            AlterSubRegex[index].clear()

    return AlterSubRegex

def unionCommomAndAlterRegex(commonRegex,alterRegex):
    '''
    input:the common longest Regex list; the alter Regex list
    ouput:union  commonRegex  and alterRegex to RegexList; 
          e.g. [a,[A,#,a],A,[#,b],....] 
          where the item of Branch is list and the item of seq and loop is character。
    '''
    RegexList=[]
    for i in range(len(commonRegex)):
        if len(alterRegex[i])>0:
            RegexList.append(alterRegex[i])
        RegexList.append(commonRegex[i])
    #handel the last part of the alter structure
    if len(alterRegex[len(commonRegex)])>0:
        RegexList.append(alterRegex[len(commonRegex)])
    return RegexList


def GenerateRecursiveAlterStructure(RegexList, actionToLetterList, letterToActionList):
    firstActions,secondActions=None,None
    regex=r''
    firstAbbrChar=None
    secondAbbrChar=None
    if len(RegexList)==0:
        return None
    elif len(RegexList)==1:
        if len(RegexList[0])>1:
            firstActions=GenerateRecursiveSeqAndLoopStructure(RegexList[0], actionToLetterList, letterToActionList)  
            regex=firstActions.regex
        else:
            if (RegexList[0]>=MIN_CHAR and RegexList[0]<=MAX_CHAR) or (RegexList[0]==emptyAction):
                firstActions= letterToActionList[RegexList[0]]  if RegexList[0]!=emptyAction  else emptyActionName 
                firstAbbrChar=RegexList[0] if RegexList[0]!=emptyAction  else emptyAction
                regex=firstAbbrChar if RegexList[0]!=emptyAction  else emptyRegex
            if(RegexList[0]>=MIN_LARGE_CHAR and  RegexList[0]<=MAX_LARGE_CHAR):
                nestChar=nestToLetterList[RegexList[0]]
                firstActions=GenerateRecursiveSeqAndLoopStructure(nestChar, actionToLetterList, letterToActionList)  
                regex=firstActions.regex
        secondActions=None
        regex=regex+'|'+emptyRegex
    elif len(RegexList)==2:
        if len(RegexList[0])>1:
            firstActions=GenerateRecursiveSeqAndLoopStructure(RegexList[0], actionToLetterList, letterToActionList)
            regex+=firstActions.regex            
        else:
            if (RegexList[0]>=MIN_CHAR and RegexList[0]<=MAX_CHAR) or (RegexList[0]==emptyAction):
                firstActions=letterToActionList[RegexList[0]] if RegexList[0]!=emptyAction  else emptyActionName 
                firstAbbrChar=RegexList[0] if RegexList[0]!=emptyAction  else emptyAction
                regex=firstAbbrChar if RegexList[0]!=emptyAction  else emptyRegex
            if(RegexList[0]>=MIN_LARGE_CHAR and  RegexList[0]<=MAX_LARGE_CHAR):
                nestChar0=nestToLetterList[RegexList[0]]
                firstActions=GenerateRecursiveSeqAndLoopStructure(nestChar0, actionToLetterList, letterToActionList)
                regex+=firstActions.regex
        if len(RegexList[1])>1:
            secondActions=GenerateRecursiveSeqAndLoopStructure(RegexList[1], actionToLetterList, letterToActionList)  
            regex=regex+'|'+secondActions.regex 
        else:
            if (RegexList[1]>=MIN_CHAR and RegexList[1]<=MAX_CHAR)  or (RegexList[1]==emptyAction) :
                secondActions=letterToActionList[RegexList[1]] if RegexList[1]!=emptyAction  else emptyActionName 
                secondAbbrChar=RegexList[1] if RegexList[1]!=emptyAction  else emptyAction
                regex=regex+'|'+(secondAbbrChar if RegexList[1]!=emptyAction  else emptyRegex)
            if(RegexList[1]>=MIN_LARGE_CHAR and  RegexList[1]<=MAX_LARGE_CHAR):
                nestChar1=nestToLetterList[RegexList[1]]
                secondActions=GenerateRecursiveSeqAndLoopStructure(nestChar1, actionToLetterList, letterToActionList)  
                regex=regex+'|'+secondActions.regex        
    else:
        if len(RegexList[0])>1:
            firstActions=GenerateRecursiveSeqAndLoopStructure(RegexList[0], actionToLetterList, letterToActionList)
            regex+=firstActions.regex
        else:
            if (RegexList[0]>=MIN_CHAR and RegexList[0]<=MAX_CHAR)  or (RegexList[0]==emptyAction) :
                firstActions=letterToActionList[RegexList[0]]  if RegexList[0]!=emptyAction  else emptyActionName 
                firstAbbrChar=RegexList[0] if RegexList[0]!=emptyAction  else emptyAction
                regex=firstAbbrChar if RegexList[0]!=emptyAction  else emptyRegex
            if(RegexList[0]>=MIN_LARGE_CHAR and  RegexList[0]<=MAX_LARGE_CHAR):
                nestChar0=nestToLetterList[RegexList[0]]
                firstActions=GenerateRecursiveSeqAndLoopStructure(nestChar0, actionToLetterList, letterToActionList)
                regex+=firstActions.regex
        secondActions=GenerateRecursiveAlterStructure(RegexList[1:], actionToLetterList, letterToActionList)
        regex=regex+'|'+secondActions.regex
    regex='('+regex+')'
    return Prog('Branch',firstActions,secondActions,firstAbbrChar,secondAbbrChar,regex)

def GenerateRecursiveSeqAndLoopStructure(RegexList, actionToLetterList, letterToActionList):
    #delete the char:()*
    flag='Seq'
    regex=r''
    firstAbbrChar=None
    secondAbbrChar=None
    if len(RegexList)>3 and RegexList[0]=='(' and RegexList[-1]=='*' and RegexList[-2]==')':
      RegexList=RegexList[1:-2]
      flag='Loop'
    firstActions,secondActions=None,None
    if len(RegexList)==0:
        return None
    elif len(RegexList)==1:
        # if lowercase then it is a single action and marks the flag Seq
        if RegexList[0]>=MIN_CHAR and RegexList[0]<=MAX_CHAR:
            firstActions=letterToActionList[RegexList[0]]
            firstAbbrChar=RegexList[0]
            regex=firstAbbrChar
        if(RegexList[0]>=MIN_LARGE_CHAR and  RegexList[0]<=MAX_LARGE_CHAR):
            nestChar=nestToLetterList[RegexList[0]]
            firstActions=GenerateRecursiveSeqAndLoopStructure(nestChar, actionToLetterList, letterToActionList)
            regex=firstActions.regex
        secondActions=None
    elif len(RegexList)==2:
        if RegexList[0]>=MIN_CHAR and RegexList[0]<=MAX_CHAR:
            firstActions=letterToActionList[RegexList[0]]
            firstAbbrChar=RegexList[0]
            regex+=firstAbbrChar
        if(RegexList[0]>=MIN_LARGE_CHAR and  RegexList[0]<=MAX_LARGE_CHAR):
            nestChar0=nestToLetterList[RegexList[0]]
            firstActions=GenerateRecursiveSeqAndLoopStructure(nestChar0, actionToLetterList, letterToActionList)
            regex+=firstActions.regex
        if RegexList[1]>=MIN_CHAR and RegexList[1]<=MAX_CHAR:
            secondActions=letterToActionList[RegexList[1]]
            secondAbbrChar=RegexList[1]
            regex+=secondAbbrChar
        if(RegexList[1]>=MIN_LARGE_CHAR and  RegexList[1]<=MAX_LARGE_CHAR):
            nestChar1=nestToLetterList[RegexList[1]]
            secondActions=GenerateRecursiveSeqAndLoopStructure(nestChar1, actionToLetterList, letterToActionList)
            regex+=secondActions.regex
    else:
        if RegexList[0]>=MIN_CHAR and RegexList[0]<=MAX_CHAR:
            firstActions=letterToActionList[RegexList[0]]
            firstAbbrChar=RegexList[0]
            regex+=firstAbbrChar
        if(RegexList[0]>=MIN_LARGE_CHAR and  RegexList[0]<=MAX_LARGE_CHAR):
            nestChar0=nestToLetterList[RegexList[0]]
            firstActions=GenerateRecursiveSeqAndLoopStructure(nestChar0, actionToLetterList, letterToActionList)
            regex+=firstActions.regex
        secondActions=GenerateRecursiveSeqAndLoopStructure(RegexList[1:], actionToLetterList, letterToActionList)
        regex+=secondActions.regex
    if flag=='Loop':
        regex='('+regex+')*'
    regex='('+regex+')'
    return Prog(flag,firstActions,secondActions,firstAbbrChar,secondAbbrChar,regex)

# use common and alterRegex to generate the program
# 
def GenerateRecursiveProgram(RegexList, actionToLetterList, letterToActionList):
    firstActions,secondActions=None,None
    regex=r''
    firstAbbrChar=None
    secondAbbrChar=None
    if len(RegexList)==0:
        return None
    #只剩下最后1个元素
    elif len(RegexList)==1:
        if isinstance(RegexList[0],list):
            AtomActions=GenerateRecursiveAlterStructure(RegexList[0],actionToLetterList,letterToActionList)
            return AtomActions
        elif isinstance(RegexList[0],str):
            if RegexList[0]>=MIN_CHAR and RegexList[0]<=MAX_CHAR:
                firstActions=letterToActionList[RegexList[0]]
                firstAbbrChar=RegexList[0]
                regex=firstAbbrChar
                regex='('+regex+')'
                return Prog('Seq',firstActions,secondActions,firstAbbrChar,secondAbbrChar,regex)
            if(RegexList[0]>=MIN_LARGE_CHAR and  RegexList[0]<=MAX_LARGE_CHAR):
                nestChar0=nestToLetterList[RegexList[0]]
                AtomActions=GenerateRecursiveSeqAndLoopStructure(nestChar0, actionToLetterList, letterToActionList)
                return AtomActions  
    else:#剩下大于等于2个元素，需要
        if isinstance(RegexList[0],list):
            firstActions=GenerateRecursiveAlterStructure(RegexList[0],actionToLetterList,letterToActionList)
            regex=regex+'('+firstActions.regex+')'
        elif isinstance(RegexList[0],str):
            if RegexList[0]>=MIN_CHAR and RegexList[0]<=MAX_CHAR:
                firstActions=letterToActionList[RegexList[0]]
                firstAbbrChar=RegexList[0]
                regex=regex+'('+firstAbbrChar+')'
            if(RegexList[0]>=MIN_LARGE_CHAR and  RegexList[0]<=MAX_LARGE_CHAR):
                nestChar0=nestToLetterList[RegexList[0]]
                firstActions=GenerateRecursiveSeqAndLoopStructure(nestChar0, actionToLetterList, letterToActionList)
                regex=regex+'('+firstActions.regex+')'
        secondActions=GenerateRecursiveProgram(RegexList[1:], actionToLetterList, letterToActionList)
        regex=regex+'('+secondActions.regex+')'
        regex='('+regex+')'
        return Prog('Seq',firstActions,secondActions,firstAbbrChar,secondAbbrChar,regex)

def preorderTraversal(genPlan):
    expr=''
    if genPlan is None:
        return expr
    if isinstance(genPlan,str):
        return genPlan
    if genPlan.secondActions is not None:
        expr+='('
    expr+=preorderTraversal(genPlan.firstActions)
    if genPlan.flag=='Branch':
        expr+='|'
    elif genPlan.secondActions is not None:
        expr+=','
    expr+=preorderTraversal(genPlan.secondActions)
    if genPlan.secondActions is not None:
        expr+=')'
    if genPlan.flag=='Loop':
        expr+='*'
    return expr

def printOutProg(genPlan,length):
    expr=''
    if genPlan is None:
        return expr,length
    if isinstance(genPlan,str):
        return genPlan,length+1
    length = length + 1 + len(str(genPlan.condition).split(" ")) + 1 + str(genPlan.condition).count('And') + genPlan.condition.count('Not') + genPlan.condition.count('Or') if length!='condition' else 1
    subexpr,length=printOutProg(genPlan.firstActions,length)
    expr+=subexpr
    if genPlan.flag=='Branch':
        expr='if ' + str(genPlan.condition) +' then '+ expr + ' else '
        lastHalfOfBranch,length=printOutProg(genPlan.secondActions,length)
        lastHalfOfBranch=emptyAction if lastHalfOfBranch=='' else lastHalfOfBranch
        expr+=lastHalfOfBranch+' end' + '\n'
    elif genPlan.secondActions is not None:
        expr+='·'+'\n'
        subexpr,length=printOutProg(genPlan.secondActions,length)
        expr+=subexpr
    if genPlan.flag=='Loop':
        expr='while ' + str(genPlan.condition) +' do\n '+ expr + '\n od'
    return expr,length

def computeDepthOfProg(genPlan,depth):
    if genPlan is None or isinstance(genPlan,str):
        return depth
    if genPlan.flag=='Loop':
        depth=depth+1
    firstDepth=computeDepthOfProg(genPlan.firstActions,depth)
    secondDepth=computeDepthOfProg(genPlan.secondActions,depth)
    depth=firstDepth if firstDepth>secondDepth else secondDepth
    return depth

def FoldString(Regex):
    """
        ItemPlan: a list of Item list such as [[Item('a','a','S'),Item('b','b','S')],[Item('a','a','S'),Item('b','b','S')]]
        return: a list of regex such as ['ab','ab']
    """
    # the length of the repeated part of the plan
    size = 1
    # the length of the repeated part of the plan must be less than half of the length of the plan
    while(size<=len(Regex)/2):
        # the start position of the plan
        i = 0
        # the start position of the plan must be less than the length of the plan
        while(i<len(Regex)):
            l = len(Regex)
            j = i
            # [j,j+size) ... [j,j+(n-1)*size) is the repeated part of the plan
            n = 2
            while(j+n*size<=l and getLoopBody(Regex,j,j+size) == getLoopBody(Regex,j+(n-1)*size,j+n*size)):
                n = n + 1
            # if the repeated part of the plan is more than 2 times, then we can combine them
            if(n>2):
                # [j,j+(n-1)*size) is the repeated part of the plan
                combine(Regex,j,j+(n-1)*size,size)
            # to get the next start position of the plan
            i = i + 1
        size = size + 1
    return Regex

def printExamList(examList,actionToLetterList):
    plan=[]
    for exam in examList:
        plan_char=''
        for e in exam:
            plan_char+=e.name
        plan.append(plan_char)
    return plan

def infskeleton(ItemPlan, actionToLetterList, letterToActionList):
    global  phi
    print("\n the abbr char of example list:")
    print(printExamList(ItemPlan,actionToLetterList))
    regexSet = []
    # every Item in ItemPlan is a list of Item which stands for a plan such as [Item('a','a','S'),Item('b','b','S')]
    for Regex in ItemPlan:
        FoldRegex=FoldString(Regex)
        while(len(Regex)!=len(FoldRegex)):
            Regex=FoldRegex
            FoldRegex=FoldString(Regex)
        # to get the regex of the plan
        regexSet.append(FoldRegex)

    res1 = printRegex1(regexSet)
    res2 = printRegex2(regexSet)
    R_regexSet = alignRegex(regexSet)
    res3 = printRegex1(R_regexSet)
    res4 = printRegex2(R_regexSet)
    unrepeatedRegex = printNoRepeatedRegex(res4)

    print("\n1. The multiple lowercase letter representing by single uppercase letter as follows:")
    print(letterToNestList)
    print(nestToLetterList)
    print("\n2. Identification of Iteration Subregexes:")
    print(res1)
    print("\n3. Identification of Iteration Subregexes representing by Abbreviation:")
    print(res2)
    print("\n4. Alignment of Iteration Subregexes:")
    print(res3)
    print("\n5. Alignment of Iteration Subregexes representing by Abbreviation:")
    print(res4)
    print("\n6. Alignment of Iteration Subregexes representing by unrepeated Abbreviation:")
    print(unrepeatedRegex)
    commonRegex = ''

    if(len(unrepeatedRegex)>1):
        #the longest common string
        commonRegex = reduce(lcs,unrepeatedRegex)
        print("\n7.commonRegex:")
        print(commonRegex)
        alterRegex = alternateRegex(unrepeatedRegex,commonRegex)
        print("\n8. Identification of Alternation Subregexes:")
        print(alterRegex)
    else:
        commonRegex = unrepeatedRegex[0]
        print("\n7. There is only one unrepeatedRegex:")
        print(unrepeatedRegex)
        print("\n8. Identification of Alternation Subregexes:")
        alterRegex = [[] for k in range(len(unrepeatedRegex[0])+1)]
        print(alterRegex)

    RegexList=unionCommomAndAlterRegex(commonRegex,alterRegex)

    print(RegexList)
    # use commonRegex and A_regexSet to generate the Program Skeleton
    print('The regex List of program:')
    print(RegexList)
    GenProgram = GenerateRecursiveProgram(RegexList, actionToLetterList, letterToActionList)
    print("\n9. The Program Skeleton:")
    phi = 1
    print(preorderTraversal(GenProgram))
    print("\n10. The regex of Program:")
    print(GenProgram.regex)
    return GenProgram

if __name__ == "__main__":
    # ItemPlan = [[Item('b','b','S'),Item('a','a','S'),Item('b','b','S'),Item('a','a','S'),Item('b','b','S'),Item('a','a','S'),Item('c','c','S'),Item('c','c','S'),Item('c','c','S')]]
    # ItemPlan = [[Item('d','d','S'),Item('a','a','S'),Item('c','c','S'),Item('b','b','S'),Item('d','d','S'),Item('a','a','S'),Item('c','c','S'),Item('b','b','S'),Item('d','d','S')],[Item('a','a','S'),Item('c','c','S'),Item('b','b','S'),Item('d','d','S'),Item('a','a','S'),Item('c','c','S'),Item('b','b','S'),Item('d','d','S')]]
    # ItemPlan = [[Item('d', 'd', 'S'), Item('a', 'a', 'S'), Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S'),Item('a', 'a', 'S'), Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S'), Item('a', 'a', 'S')],[Item('a', 'a', 'S'), Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S'), Item('a', 'a', 'S'),Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S')]]
    # ItemPlan = [[Item('a', 'a', 'S'),Item('d', 'd', 'S'), Item('a', 'a', 'S'), Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S'),Item('a', 'a', 'S'), Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S'), Item('c', 'c', 'S')],[Item('a', 'a', 'S'), Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S'), Item('a', 'a', 'S'),Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S')]]
    # ItemPlan = [[Item('a', 'a', 'S'), Item('d', 'd', 'S'), Item('a', 'a', 'S'), Item('c', 'c', 'S'), Item('b', 'b', 'S'),Item('d', 'd', 'S'), Item('a', 'a', 'S'), Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S'),Item('a', 'a', 'S')],[Item('a', 'a', 'S'), Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S'), Item('a', 'a', 'S'),Item('c', 'c', 'S'), Item('b', 'b', 'S'), Item('d', 'd', 'S')]]


    # ItemPlan = [[Item('b', 'b', 'S'), Item('a', 'a', 'S')],[Item('a', 'a', 'S'),Item('b', 'b', 'S'), Item('b', 'b', 'S'),Item('a', 'a', 'S')],[Item('a', 'a', 'S')],[Item('a', 'a', 'S'),Item('b', 'b', 'S'), Item('b', 'b', 'S'),Item('a', 'a', 'S'),Item('b', 'b', 'S'), Item('b', 'b', 'S'),Item('a', 'a', 'S')],[Item('b', 'b', 'S'), Item('b', 'b', 'S'),Item('a', 'a', 'S')]]
    ItemPlan = [[Item('a', 'a', 'S'), Item('a', 'a', 'S'),Item('b', 'b', 'S'), Item('b', 'b', 'S'),Item('e', 'e', 'S'),Item('c', 'c', 'S'), Item('c', 'c', 'S'),Item('d', 'd', 'S'), Item('d', 'd', 'S')],
                [Item('a', 'a', 'S'), Item('a', 'a', 'S'),Item('b', 'b', 'S'), Item('b', 'b', 'S'),Item('f', 'f', 'S'),Item('c', 'c', 'S'), Item('c', 'c', 'S'),Item('d', 'd', 'S'), Item('d', 'd', 'S')],
                [Item('a', 'a', 'S'), Item('a', 'a', 'S'),Item('b', 'b', 'S'), Item('b', 'b', 'S'),Item('g', 'g', 'S'),Item('c', 'c', 'S'), Item('c', 'c', 'S'),Item('d', 'd', 'S'), Item('d', 'd', 'S')],
                [Item('a', 'a', 'S'), Item('a', 'a', 'S'),Item('b', 'b', 'S'), Item('b', 'b', 'S'),Item('h', 'h', 'S'),Item('c', 'c', 'S'), Item('c', 'c', 'S'),Item('d', 'd', 'S'), Item('d', 'd', 'S')],
                [Item('a', 'a', 'S'), Item('a', 'a', 'S'),Item('b', 'b', 'S'), Item('b', 'b', 'S'),Item('i', 'i', 'S'),Item('c', 'c', 'S'), Item('c', 'c', 'S'),Item('d', 'd', 'S'), Item('d', 'd', 'S')]]
    actionToLetterList = {'MOVEA': 'a', 'MOVEB': 'b','MOVEC': 'c','MOVED': 'd','MOVEE': 'e','MOVEF': 'f','MOVEG': 'g','MOVEH': 'h','MOVEI': 'i'}
    letterToActionList = {'a': 'MOVEA', 'b': 'MOVEB','c': 'MOVEC','d': 'MOVED','e': 'MOVEE','f': 'MOVEF','g': 'MOVEG','h': 'MOVEH','i': 'MOVEI'}
    genProgram=infskeleton(ItemPlan, actionToLetterList, letterToActionList)
    expr,length=printOutProg(genProgram,0)
    print(expr)
