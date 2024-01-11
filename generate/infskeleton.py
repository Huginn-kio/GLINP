import copy
import difflib
from functools import reduce
from generate.datastructure import Item, Program


# map the letter (cd)* to the ABC...
letterToNestList={}
# map the ABC... to the letter (cd)*
nestToLetterList={}
# the empty action
emptyAction='#'
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


# to print the program by using Program set
def PrintProgram(GenProgram,length,depth):
    global phi
    i=0
    start=False
    endif=False
    prestr=''
    # set the pre space
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
            length=PrintProgram(GenProgram[i].actionList,length,depth+4)
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
            length=PrintProgram(GenProgram[i].actionList,length,depth+4)
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
            length = PrintProgram(GenProgram[i].actionList, length, depth + 4)
            # print("LOOP"+str(length))
            print(prestr + "od" + hasNext)
    if len(GenProgram) > 1:
        length = length + len(GenProgram) - 1
    return length



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



# use common and alterRegex to generate the program
def GenerateProgram(commom,alterRegex, actionToLetterList, letterToActionList):
    if len(commom)>3 and commom[0]=='(' and commom[-1]=='*' and commom[-2]==')':
      commom=commom[1:-2]
    i=0
    GenProgram=[]
    while i <len(commom):
      # first to handle the alterRegex part
      for  j in range(len(alterRegex[i])):
          # empty action marks the flag IFe
          if alterRegex[i][j]==emptyAction:
            GenProgram.append(Program('IFe',emptyAction))
          else:
            # not empty action marks the flag IF and we can dfs to handle it recursively such as common is cur and alterRegex is [[]...[]] and collect the actionlist which is the Program set
            act_if=GenerateProgram(alterRegex[i][j],[[] for k in range(len(alterRegex[i][j])+1)], actionToLetterList, letterToActionList)
            GenProgram.append(Program('IF',act_if))
      # second to handle the common part
      # if lowercase then it is a single action and marks the flag Seq
      if commom[i]>='a' and commom[i]<='z':
        GenProgram.append(Program('Seq',[letterToActionList[commom[i]]]))
      # if uppercase then it is a nest and marks the flag Loop
      if(commom[i]>='A' and  commom[i]<='Z'):
        tmp=nestToLetterList[commom[i]]
        length=len(tmp)
        if len(tmp)>3 and tmp[0]=='(' and tmp[-1]=='*' and tmp[-2]==')':
          length-=3
        act_Loop=GenerateProgram(tmp,[[] for i in range(length+1)], actionToLetterList, letterToActionList)
        GenProgram.append(Program('Loop',act_Loop))
      i=i+1
    # to handle the last alterRegex part
    for  j in range(len(alterRegex[i])):
          if alterRegex[i][j]==emptyAction:
            GenProgram.append(Program('IFe',emptyAction))
          else:
            act_if=GenerateProgram(alterRegex[i][j],[[] for k in range(len(alterRegex[i][j])+1)], actionToLetterList, letterToActionList)
            GenProgram.append(Program('IF',act_if))
    # GenProgram is the program set which is the whole program or the part of program as actionlist
    return GenProgram





def infskeleton(ItemPlan, actionToLetterList, letterToActionList):
    global  phi

    regexSet = indentifyRegex(ItemPlan)
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
        commonRegex = reduce(lcs,unrepeatedRegex)
        print("\n7.commonRegex:")
        print(commonRegex)
        A_regexSet = alternateRegex(unrepeatedRegex,commonRegex)
        print("\n8. Identification of Alternation Subregexes:")
        print(A_regexSet)
    else:
        commonRegex = unrepeatedRegex[0]
        print("\n7. There is only one unrepeatedRegex:")
        print(unrepeatedRegex)
        print("\n8. Identification of Alternation Subregexes:")
        A_regexSet = [[] for k in range(len(unrepeatedRegex[0])+1)]
        print(A_regexSet)

    # use commonRegex and A_regexSet to generate the Program Skeleton

    GenProgram = GenerateProgram(commonRegex, A_regexSet, actionToLetterList, letterToActionList)

    print("\n9. The Program Skeleton:")
    phi = 1
    PrintNoElseProgram(GenProgram,0,0)

    return regexSet,R_regexSet,commonRegex,A_regexSet,GenProgram,letterToNestList,nestToLetterList




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
    infskeleton(ItemPlan, actionToLetterList, letterToActionList)