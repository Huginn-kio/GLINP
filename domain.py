def Arith(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(v1)'] == 0, numInitZ3['(v2)'] == 0, numInitZ3['(n)'] > 0]
    goal = [numGoalZ3['(v1)'] == numGoalZ3['(n)'], numGoalZ3['(v2)'] == numGoalZ3['(n)'] + numGoalZ3['(n)'] + 1]
    return Init, goal


def Chop(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(h)'] > 0]
    goal = [numGoalZ3['(h)'] == 0]
    return Init, goal


def ClearBlock(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(n)'] > 0, propInitZ3['(empty)'] == True]
    goal = [numGoalZ3['(n)'] == 0,propGoalZ3['(empty)'] == True]
    return Init, goal

def Corner_A(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(disr)'] >= 0, numInitZ3['(disl)'] >= 0, numInitZ3['(dist)'] >= 0, numInitZ3['(disb)'] >= 0]
    goal = [numGoalZ3['(disr)'] == 0, numGoalZ3['(dist)'] == 0]
    return Init, goal


def Corner_R(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(dectr)'] == True, propInitZ3['(dectl)'] == False, propInitZ3['(dectt)'] == False,
            propInitZ3['(dectb)'] == False, numInitZ3['(disr)'] >= 0, numInitZ3['(disl)'] >= 0, numInitZ3['(dist)'] >= 0,
            numInitZ3['(disb)'] >= 0]
    goal = [numGoalZ3['(disr)'] == 0,  numGoalZ3['(dist)'] == 0]
    return Init, goal

def Delivery(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(numd)'] > 0, numInitZ3['(numc)'] == 0, numInitZ3['(numt)'] == 0, numInitZ3['(cap)'] > 0]
    goal = [numGoalZ3['(numd)'] == 0,  numGoalZ3['(numt)'] == 0, propGoalZ3['(atd)'] == True]
    return Init, goal

def D_Return(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(visitlt)'] == False, propInitZ3['(visitrt)'] == False,
            propInitZ3['(visitrb)'] == False, numInitZ3['(disr)'] >= 0, numInitZ3['(disl)'] >= 0,
            numInitZ3['(dist)'] >= 0, numInitZ3['(disb)'] >= 0, numInitZ3['(startl)'] == numInitZ3['(disl)'],
            numInitZ3['(startt)'] == numInitZ3['(dist)']]
    goal = [numGoalZ3['(disl)'] == numGoalZ3['(startl)'], numGoalZ3['(dist)'] == numGoalZ3['(startt)'],
            propGoalZ3['(visitlt)'] == True, propGoalZ3['(visitrt)'] == True, propGoalZ3['(visitrb)'] == True]
    return Init, goal


def D_Return_R(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(visitlt)'] == False, propInitZ3['(visitrt)'] == False,
            propInitZ3['(visitrb)'] == False, propInitZ3['(dectr)'] == False, propInitZ3['(dectl)'] == True,
            propInitZ3['(dectt)'] == False, propInitZ3['(dectb)'] == False, numInitZ3['(disr)'] >= 0,
            numInitZ3['(disl)'] >= 0, numInitZ3['(dist)'] >= 0, numInitZ3['(disb)'] >= 0,
            numInitZ3['(startl)'] == numInitZ3['(disl)'], numInitZ3['(startt)'] == numInitZ3['(dist)']]
    goal = [numGoalZ3['(disl)'] == numGoalZ3['(startl)'], numGoalZ3['(dist)'] == numGoalZ3['(startt)'],
            propGoalZ3['(visitlt)'] == True, propGoalZ3['(visitrt)'] == True, propGoalZ3['(visitrb)'] == True]
    return Init, goal


def Gripper(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(na)'] > 0, numInitZ3['(nb)'] == 0, numInitZ3['(mc)'] == 0, numInitZ3['(me)'] > 0]
    goal = [propGoalZ3['(la)'] == True, numGoalZ3['(nb)'] > 0, numGoalZ3['(mc)'] == 0, numGoalZ3['(me)'] > 0, numGoalZ3['(na)'] == 0]
    return Init, goal

def Hall_A(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(visitlt)'] == False, propInitZ3['(visitrt)'] == False, propInitZ3['(visitlb)'] == False,
            propInitZ3['(visitrb)'] == False, numInitZ3['(disr)'] == 0, numInitZ3['(disl)'] >= 0,
            numInitZ3['(dist)'] >= 0, numInitZ3['(disb)'] >= 0, numInitZ3['(startl)'] == numInitZ3['(disl)'],
            numInitZ3['(startt)'] == numInitZ3['(dist)'] ]
    goal = [numGoalZ3['(disl)'] == numGoalZ3['(startl)'], numGoalZ3['(dist)'] == numGoalZ3['(startt)'],
            propGoalZ3['(visitlt)'] == True, propGoalZ3['(visitrt)'] == True, propGoalZ3['(visitrb)'] == True,
            propGoalZ3['(visitlb)'] == True]
    return Init, goal


def Hall_R(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(dectr)'] == False, propInitZ3['(dectl)'] == False, propInitZ3['(dectt)'] == False,
            propInitZ3['(dectb)'] == True, propInitZ3['(visitlt)'] == False, propInitZ3['(visitrt)'] == False,
            propInitZ3['(visitlb)'] == False, propInitZ3['(visitrb)'] == False, numInitZ3['(disr)'] == 0,
            numInitZ3['(disl)'] >= 0, numInitZ3['(dist)'] >= 0, numInitZ3['(disb)'] >= 0,
            numInitZ3['(startl)'] == numInitZ3['(disl)'], numInitZ3['(startt)'] == numInitZ3['(dist)']]
    goal = [numGoalZ3['(disl)'] == numGoalZ3['(startl)'], numGoalZ3['(dist)'] == numGoalZ3['(startt)'],
            propGoalZ3['(visitlt)'] == True, propGoalZ3['(visitrt)'] == True, propGoalZ3['(visitrb)'] == True,
            propGoalZ3['(visitlb)'] == True]
    return Init, goal


def PlaceBlock(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(empty)'] == True, propInitZ3['(heldX)'] == False, numInitZ3['(nx)'] > 0,
            numInitZ3['(ny)'] > 0, propInitZ3['(XOnY)'] == False]
    goal = [propGoalZ3['(XOnY)'] == True]
    return Init, goal

def Rewards(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(numr)'] > 0, numInitZ3['(dis)'] > 0, numInitZ3['(gap)'] > 0]
    goal = [numGoalZ3['(numr)'] == 0]
    return Init, goal


def Snow(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(lenw)'] > 0, numInitZ3['(lend)'] > 0, propInitZ3['(ond)'] == True]
    goal = [numGoalZ3['(lenw)'] == 0, numGoalZ3['(lend)'] == 0, propGoalZ3['(ond)'] == True]
    return Init, goal


def TestOn(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(nx)'] > 0, numInitZ3['(ny)'] > 0, propInitZ3['(stack)'] == False]
    goal = [ propGoalZ3['(stack)'] == True]
    return Init, goal


def Visitall(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(visitr)'] == False, propInitZ3['(visitl)'] == False, numInitZ3['(disr)'] > 0,
            numInitZ3['(disl)'] == 0, numInitZ3['(dist)'] == 0, numInitZ3['(disb)'] > 0, numInitZ3['(numr)'] == 0]
    goal = [numGoalZ3['(disb)'] + numGoalZ3['(dist)'] +1 == numGoalZ3['(numr)']]
    return Init, goal


def Visitall_R(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(visitr)'] == False, propInitZ3['(visitl)'] == False, propInitZ3['(dectl)'] == True,
            propInitZ3['(dectr)'] == False, propInitZ3['(dectt)'] == False, propInitZ3['(dectb)'] == False,
            numInitZ3['(disr)'] > 0, numInitZ3['(disl)'] == 0, numInitZ3['(dist)'] == 0, numInitZ3['(disb)'] > 0,
            numInitZ3['(numr)'] == 0]
    goal = [numGoalZ3['(disb)'] + numGoalZ3['(dist)'] == numGoalZ3['(numr)']]
    return Init, goal


def NestVar2(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] > 0, numInitZ3['(x2)'] > 0]
    goal = [numGoalZ3['(x1)'] == 0, numGoalZ3['(x2)'] == 0]
    return Init, goal


def NestVar3(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x)'] > 0, numInitZ3['(y)'] > 0, numInitZ3['(z)'] > 0]
    goal = [numGoalZ3['(x)'] == 0, numGoalZ3['(y)'] == 0, numGoalZ3['(z)'] == 0]
    return Init, goal


def NestVar4(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] > 0, numInitZ3['(x2)'] > 0, numInitZ3['(x3)'] > 0, numInitZ3['(x4)'] > 0]
    goal = [numGoalZ3['(x1)'] == 0, numGoalZ3['(x2)'] == 0, numGoalZ3['(x3)'] == 0, numGoalZ3['(x4)'] == 0]
    return Init, goal

def NestVar5(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] > 0, numInitZ3['(x2)'] > 0, numInitZ3['(x3)'] > 0, numInitZ3['(x4)'] > 0,
            numInitZ3['(x5)'] > 0]
    goal = [numGoalZ3['(x1)'] == 0, numGoalZ3['(x2)'] == 0, numGoalZ3['(x3)'] == 0, numGoalZ3['(x4)'] == 0,
            numGoalZ3['(x5)'] == 0]
    return Init, goal

def NestVar6(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] > 0, numInitZ3['(x2)'] > 0, numInitZ3['(x3)'] > 0, numInitZ3['(x4)'] > 0,
            numInitZ3['(x5)'] > 0, numInitZ3['(x6)'] > 0]
    goal = [numGoalZ3['(x1)'] == 0, numGoalZ3['(x2)'] == 0, numGoalZ3['(x3)'] == 0, numGoalZ3['(x4)'] == 0,
            numGoalZ3['(x5)'] == 0, numGoalZ3['(x6)'] == 0]
    return Init, goal

def NestVar7(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] > 0, numInitZ3['(x2)'] > 0, numInitZ3['(x3)'] > 0, numInitZ3['(x4)'] > 0,
            numInitZ3['(x5)'] > 0, numInitZ3['(x6)'] > 0, numInitZ3['(x7)'] > 0]
    goal = [numGoalZ3['(x1)'] == 0, numGoalZ3['(x2)'] == 0, numGoalZ3['(x3)'] == 0, numGoalZ3['(x4)'] == 0,
            numGoalZ3['(x5)'] == 0, numGoalZ3['(x6)'] == 0, numGoalZ3['(x7)'] == 0]
    return Init, goal

def NestVar8(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] > 0, numInitZ3['(x2)'] > 0, numInitZ3['(x3)'] > 0, numInitZ3['(x4)'] > 0,
            numInitZ3['(x5)'] > 0, numInitZ3['(x6)'] > 0, numInitZ3['(x7)'] > 0, numInitZ3['(x8)'] > 0]
    goal = [numGoalZ3['(x1)'] == 0, numGoalZ3['(x2)'] == 0, numGoalZ3['(x3)'] == 0, numGoalZ3['(x4)'] == 0,
            numGoalZ3['(x5)'] == 0, numGoalZ3['(x6)'] == 0, numGoalZ3['(x7)'] == 0, numGoalZ3['(x8)'] == 0]
    return Init, goal


def MNestVar2(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] >= 0, numInitZ3['(x2)'] >= 0]
    goal = [numGoalZ3['(x1)'] == 0]
    return Init, goal


def MNestVar3(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x)'] >= 0, numInitZ3['(y)'] >= 0, numInitZ3['(z)'] >= 0]
    goal = [numGoalZ3['(x)'] == 0]
    return Init, goal

def MNestVar4(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] >= 0, numInitZ3['(x2)'] >= 0, numInitZ3['(x3)'] >= 0, numInitZ3['(x4)'] >= 0]
    goal = [numGoalZ3['(x1)'] == 0]
    return Init, goal

def MNestVar5(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] >= 0, numInitZ3['(x2)'] >= 0, numInitZ3['(x3)'] >= 0, numInitZ3['(x4)'] >= 0,
            numInitZ3['(x5)'] >= 0]
    goal = [numGoalZ3['(x1)'] == 0]
    return Init, goal

def MNestVar6(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] >= 0, numInitZ3['(x2)'] >= 0, numInitZ3['(x3)'] >= 0, numInitZ3['(x4)'] >= 0,
            numInitZ3['(x5)'] >= 0, numInitZ3['(x6)'] >= 0]
    goal = [numGoalZ3['(x1)'] == 0]
    return Init, goal

def MNestVar7(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] >= 0, numInitZ3['(x2)'] >= 0, numInitZ3['(x3)'] >= 0, numInitZ3['(x4)'] >= 0,
            numInitZ3['(x5)'] >= 0, numInitZ3['(x6)'] >= 0, numInitZ3['(x7)'] >= 0]
    goal = [numGoalZ3['(x1)'] == 0]
    return Init, goal


def MNestVar8(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(x1)'] >= 0, numInitZ3['(x2)'] >= 0, numInitZ3['(x3)'] >= 0, numInitZ3['(x4)'] >= 0,
            numInitZ3['(x5)'] >= 0, numInitZ3['(x6)'] >= 0, numInitZ3['(x7)'] >= 0, numInitZ3['(x8)'] >= 0]
    goal = [numGoalZ3['(x1)'] == 0]
    return Init, goal

def Childsnack(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    #(numnsc==0,numnst==0,numgsc==0,numgst==0,numnw>=0,numgw>=0,numnw+numgw>0,numnb>=numnw,numnc>=numnw,numgb>=numgw,numgc>=numgw)
    Init = [numInitZ3['(numnsk)'] == 0,numInitZ3['(numnst)'] == 0,numInitZ3['(numgsk)'] == 0,numInitZ3['(numgst)'] == 0,
            numInitZ3['(numnc)'] >= 0,numInitZ3['(numgc)'] >= 0, numInitZ3['(numnc)'] + numInitZ3['(numgc)'] > 0,
            numInitZ3['(numnb)'] >= numInitZ3['(numnc)'],numInitZ3['(numni)'] >= numInitZ3['(numnc)'],
            numInitZ3['(numgb)'] >= numInitZ3['(numgc)'],numInitZ3['(numgi)'] >= numInitZ3['(numgc)'],
            propInitZ3['(atk)'] == True]
    goal = [numGoalZ3['(numnc)'] == 0,numGoalZ3['(numgc)'] == 0,propGoalZ3['(atk)'] == True]
    return Init, goal



def Barman(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(holding)'] == False, propInitZ3['(empty)'] == True,propInitZ3['(containIg1)'] == False,
            propInitZ3['(containIg2)'] == False, propInitZ3['(containCt)'] == False,
            numInitZ3['(numg)'] > 0, numInitZ3['(numig1)'] > 0, numInitZ3['(numig2)'] > 0, numInitZ3['(numct)'] > 0,
            numInitZ3['(numg)'] == numInitZ3['(numct)'], numInitZ3['(numig1)'] >= numInitZ3['(numct)'], numInitZ3['(numig2)'] >= numInitZ3['(numct)']
            ]
    goal = [propGoalZ3['(empty)'] == True, propGoalZ3['(holding)'] == False, numGoalZ3['(numct)'] == 0]
    return Init, goal

def Barman3(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(holding)'] == False, propInitZ3['(empty)'] == True,propInitZ3['(containIg1)'] == False,
            propInitZ3['(containIg2)'] == False,propInitZ3['(containIg3)'] == False, propInitZ3['(containCt)'] == False,
            numInitZ3['(numg)'] > 0, numInitZ3['(numig1)'] > 0, numInitZ3['(numig2)'] > 0, numInitZ3['(numig3)'] > 0, numInitZ3['(numct)'] > 0,
            numInitZ3['(numg)'] == numInitZ3['(numct)'], numInitZ3['(numig1)'] >= numInitZ3['(numct)'], numInitZ3['(numig2)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig3)'] >= numInitZ3['(numct)']
            ]
    goal = [propGoalZ3['(empty)'] == True, propGoalZ3['(holding)'] == False, numGoalZ3['(numct)'] == 0]
    return Init, goal

def Barman4(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(holding)'] == False, propInitZ3['(empty)'] == True,propInitZ3['(containIg1)'] == False,
            propInitZ3['(containIg2)'] == False,propInitZ3['(containIg3)'] == False,propInitZ3['(containIg4)'] == False, propInitZ3['(containCt)'] == False,
            numInitZ3['(numg)'] > 0, numInitZ3['(numig1)'] > 0, numInitZ3['(numig2)'] > 0, numInitZ3['(numig3)'] > 0, numInitZ3['(numig4)'] > 0,
            numInitZ3['(numct)'] > 0,numInitZ3['(numg)'] == numInitZ3['(numct)'], numInitZ3['(numig1)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig2)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig3)'] >= numInitZ3['(numct)'],numInitZ3['(numig4)'] >= numInitZ3['(numct)']
            ]
    goal = [propGoalZ3['(empty)'] == True, propGoalZ3['(holding)'] == False, numGoalZ3['(numct)'] == 0]
    return Init, goal

def Barman5(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(holding)'] == False, propInitZ3['(empty)'] == True,propInitZ3['(containIg1)'] == False,
            propInitZ3['(containIg2)'] == False,propInitZ3['(containIg3)'] == False,propInitZ3['(containIg4)'] == False,
            propInitZ3['(containIg5)'] == False, propInitZ3['(containCt)'] == False,
            numInitZ3['(numg)'] > 0, numInitZ3['(numig1)'] > 0, numInitZ3['(numig2)'] > 0, numInitZ3['(numig3)'] > 0, numInitZ3['(numig4)'] > 0,
            numInitZ3['(numig5)'] > 0, numInitZ3['(numct)'] > 0,numInitZ3['(numg)'] == numInitZ3['(numct)'], numInitZ3['(numig1)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig2)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig3)'] >= numInitZ3['(numct)'],numInitZ3['(numig4)'] >= numInitZ3['(numct)'],numInitZ3['(numig5)'] >= numInitZ3['(numct)']
            ]
    goal = [propGoalZ3['(empty)'] == True, propGoalZ3['(holding)'] == False, numGoalZ3['(numct)'] == 0]
    return Init, goal

def Barman6(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(holding)'] == False, propInitZ3['(empty)'] == True,propInitZ3['(containIg1)'] == False,
            propInitZ3['(containIg2)'] == False,propInitZ3['(containIg3)'] == False,propInitZ3['(containIg4)'] == False,
            propInitZ3['(containIg5)'] == False, propInitZ3['(containIg6)'] == False, propInitZ3['(containCt)'] == False,
            numInitZ3['(numg)'] > 0, numInitZ3['(numig1)'] > 0, numInitZ3['(numig2)'] > 0, numInitZ3['(numig3)'] > 0, numInitZ3['(numig4)'] > 0,
            numInitZ3['(numig5)'] > 0, numInitZ3['(numig6)'] > 0, numInitZ3['(numct)'] > 0,numInitZ3['(numg)'] == numInitZ3['(numct)'],
            numInitZ3['(numig1)'] >= numInitZ3['(numct)'], numInitZ3['(numig2)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig3)'] >= numInitZ3['(numct)'],numInitZ3['(numig4)'] >= numInitZ3['(numct)'], numInitZ3['(numig5)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig6)'] >= numInitZ3['(numct)']
            ]
    goal = [propGoalZ3['(empty)'] == True, propGoalZ3['(holding)'] == False, numGoalZ3['(numct)'] == 0]
    return Init, goal

def Barman7(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(holding)'] == False, propInitZ3['(empty)'] == True,propInitZ3['(containIg1)'] == False,
            propInitZ3['(containIg2)'] == False,propInitZ3['(containIg3)'] == False,propInitZ3['(containIg4)'] == False,
            propInitZ3['(containIg5)'] == False, propInitZ3['(containIg6)'] == False, propInitZ3['(containIg7)'] == False, propInitZ3['(containCt)'] == False,
            numInitZ3['(numg)'] > 0, numInitZ3['(numig1)'] > 0, numInitZ3['(numig2)'] > 0, numInitZ3['(numig3)'] > 0, numInitZ3['(numig4)'] > 0,
            numInitZ3['(numig5)'] > 0, numInitZ3['(numig6)'] > 0, numInitZ3['(numig7)'] > 0, numInitZ3['(numct)'] > 0,numInitZ3['(numg)'] == numInitZ3['(numct)'],
            numInitZ3['(numig1)'] >= numInitZ3['(numct)'], numInitZ3['(numig2)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig3)'] >= numInitZ3['(numct)'],numInitZ3['(numig4)'] >= numInitZ3['(numct)'], numInitZ3['(numig5)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig6)'] >= numInitZ3['(numct)'], numInitZ3['(numig7)'] >= numInitZ3['(numct)']
            ]
    goal = [propGoalZ3['(empty)'] == True, propGoalZ3['(holding)'] == False, numGoalZ3['(numct)'] == 0]
    return Init, goal

def Barman8(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(holding)'] == False, propInitZ3['(empty)'] == True,propInitZ3['(containIg1)'] == False,
            propInitZ3['(containIg2)'] == False,propInitZ3['(containIg3)'] == False,propInitZ3['(containIg4)'] == False,
            propInitZ3['(containIg5)'] == False, propInitZ3['(containIg6)'] == False, propInitZ3['(containIg7)'] == False,
            propInitZ3['(containIg8)'] == False, propInitZ3['(containCt)'] == False,
            numInitZ3['(numg)'] > 0, numInitZ3['(numig1)'] > 0, numInitZ3['(numig2)'] > 0, numInitZ3['(numig3)'] > 0, numInitZ3['(numig4)'] > 0,
            numInitZ3['(numig5)'] > 0, numInitZ3['(numig6)'] > 0, numInitZ3['(numig7)'] > 0, numInitZ3['(numig8)'] > 0, numInitZ3['(numct)'] > 0,
            numInitZ3['(numg)'] == numInitZ3['(numct)'], numInitZ3['(numig1)'] >= numInitZ3['(numct)'], numInitZ3['(numig2)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig3)'] >= numInitZ3['(numct)'],numInitZ3['(numig4)'] >= numInitZ3['(numct)'], numInitZ3['(numig5)'] >= numInitZ3['(numct)'],
            numInitZ3['(numig6)'] >= numInitZ3['(numct)'], numInitZ3['(numig7)'] >= numInitZ3['(numct)'], numInitZ3['(numig8)'] >= numInitZ3['(numct)']
            ]
    goal = [propGoalZ3['(empty)'] == True, propGoalZ3['(holding)'] == False, numGoalZ3['(numct)'] == 0]
    return Init, goal

def Corridor(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(loc)'] == 0,numInitZ3['(leng)'] > 0]
    goal = [numGoalZ3['(loc)'] == numGoalZ3['(leng)']]
    return Init, goal

def Floortile(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(visitr)'] == False, propInitZ3['(visitl)'] == False, numInitZ3['(disr)'] > 0,
            numInitZ3['(disl)'] == 0, numInitZ3['(dist)'] == 0, numInitZ3['(disb)'] > 0, numInitZ3['(numr)'] == 0]
    goal = [numGoalZ3['(disb)'] + numGoalZ3['(dist)']  + 1 == numGoalZ3['(numr)']]
    return Init, goal

def Grid(propInitZ3, propGoalZ3, numInitZ3, numGoalZ3):
    Init = [propInitZ3['(gotkey)'] == False, propInitZ3['(isopen)'] == False, numInitZ3['(xagt)'] == 0,
                numInitZ3['(yagt)'] == 0, numInitZ3['(width)'] > 0, numInitZ3['(height)'] > 0,
                numInitZ3['(xkey)'] == numInitZ3['(width)'], numInitZ3['(ykey)'] == 0,
                numInitZ3['(xlock)'] == numInitZ3['(width)'], numInitZ3['(ylock)'] == numInitZ3['(height)']]
    goal = [propGoalZ3['(gotkey)'] == True, propGoalZ3['(isopen)'] == True, numGoalZ3['(xagt)'] == 0,
                numGoalZ3['(yagt)'] == numGoalZ3['(height)']]
    return Init, goal

def Hiking(propInitZ3, propGoalZ3, numInitZ3, numGoalZ3):
    Init = [numInitZ3['(numsight)'] > 0, propInitZ3['(athn)'] == False,propInitZ3['(atwn)'] == False,propInitZ3['(attn)'] == False, propInitZ3['(tentup)'] == False,
                propInitZ3['(traveled)'] == False, propInitZ3['(energetic)'] == True]
    goal = [numGoalZ3['(numsight)'] == 0]
    return Init, goal

def Intrusion(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(numcon)'] == 0, numInitZ3['(numbrk)'] == 0,numInitZ3['(numcln)'] == 0,numInitZ3['(numgained)'] == 0, numInitZ3['(numdown)'] == 0,numInitZ3['(numstl)'] == 0,numInitZ3['(numhost)'] > 0]
    goal = [numGoalZ3['(numstl)'] == numGoalZ3['(numhost)']]
    return Init, goal


def Lock(propInitZ3, propGoalZ3, numInitZ3, numGoalZ3):
    Init = [propInitZ3['(gotk)'] == False, propInitZ3['(opened)'] == False, numInitZ3['(mid)'] > 0,numInitZ3['(loc)'] == numInitZ3['(mid)'],numInitZ3['(xkey)'] == numInitZ3['(mid)']+numInitZ3['(mid)'] ]
    goal = [ propGoalZ3['(opened)'] == True]
    return Init, goal


def Nomystery(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(nump)'] > 0, numInitZ3['(numc)'] == 0,  propInitZ3['(atg)'] == False]
    goal = [numGoalZ3['(numc)'] == 0, propGoalZ3['(atg)'] == True]
    return Init, goal


def Spanner(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [numInitZ3['(dist)'] > 0, numInitZ3['(numn)'] > 0, numInitZ3['(nums)'] > 0,
            numInitZ3['(dist)'] == numInitZ3['(nums)'] , numInitZ3['(nums)'] >= numInitZ3['(numn)'], numInitZ3['(numc)'] == 0,propInitZ3['(empty)'] == False]
    goal = [numGoalZ3['(dist)'] == 0, numGoalZ3['(numn)'] == 0]
    return Init, goal



# def Baking(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
#     Init = [propInitZ3['(isegginpan)'] == False, propInitZ3['(isflourinpan)'] == False, propInitZ3['(ismixed)'] == False, propInitZ3['(isatoven)'] == False,propInitZ3['(isbaked)'] == False, propInitZ3['(clean)'] == True,numInitZ3['(numcake)'] > 0]
#     goal = [propGoalZ3['(clean)'] == True,  numGoalZ3['(numcake)'] == 0]
#     return Init, goal

def Baking(propInitZ3,propGoalZ3,numInitZ3,numGoalZ3):
    Init = [propInitZ3['(inep)'] == False, propInitZ3['(infp)'] == False, propInitZ3['(mixed)'] == False, propInitZ3['(inpo)'] == False,propInitZ3['(baked)'] == False, propInitZ3['(clean)'] == True,numInitZ3['(numcake)'] > 0]
    goal = [propGoalZ3['(clean)'] == True,  numGoalZ3['(numcake)'] == 0]
    return Init, goal

def Miconic(propInitZ3, propGoalZ3, numInitZ3, numGoalZ3):
    Init = [numInitZ3['(curf)'] == 1, numInitZ3['(topf)'] > 1, numInitZ3['(numf)'] > 0, numInitZ3['(nume)'] == 0,
                numInitZ3['(numt)'] == 0, numInitZ3['(cap)'] > 0]
    goal = [numGoalZ3['(curf)'] == 1, numGoalZ3['(nume)'] == 0, numGoalZ3['(numf)'] == 0]
    return Init, goal

Switch = {'Arith':Arith,'Baking':Baking,'Chop':Chop,'ClearBlock':ClearBlock,'Delivery':Delivery,'Floortile':Floortile,'Grid':Grid,'Gripper':Gripper,
          'Corner-A':Corner_A,'Corner-R':Corner_R,'Corridor':Corridor,'Hall-A':Hall_A,'Hall-R':Hall_R,'Hiking':Hiking,'Intrusion':Intrusion,'Lock':Lock,'PlaceBlock': PlaceBlock,
          'D-Return':D_Return,'D-Return-R':D_Return_R,'Rewards': Rewards,'Snow':Snow,'Spanner':Spanner,'Childsnack':Childsnack,
          'TestOn':TestOn,'Visitall':Visitall,'visitall-R':Visitall_R,
          'Barman':Barman, 'Barman3':Barman3, 'Barman4':Barman4,'Barman5':Barman5,'Barman6':Barman6,'Barman7':Barman7,'Barman8':Barman8,
          'NestVar2':NestVar2, 'NestVar3':NestVar3,'NestVar4':NestVar4,'NestVar5':NestVar5,'NestVar6':NestVar6,'NestVar7':NestVar7, 'NestVar8':NestVar8,
          'Nomystery':Nomystery,'Miconic':Miconic,'MNestVar2':MNestVar2, 'MNestVar3':MNestVar3, 'MNestVar4':MNestVar4, 'MNestVar5':MNestVar5, 'MNestVar6':MNestVar6, 'MNestVar7':MNestVar7, 'MNestVar8':MNestVar8}