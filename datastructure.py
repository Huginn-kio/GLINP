import copy


class Item:
  def __init__(self, body, name,flag):
      # body stands for the nested loop
      # body is letter if flag is 'S' such as 'a'
      # body is Item List if flag is 'L' or 'C'
      self.body = body
      # name stands for the name of the current
      # name is letter if flag is 'S'
      # name is ()* if flag is 'L'
      self.name = name
      # flag stands for the type of the current
      # flag is 'S' if the current is a single action
      # flag is 'L' if the current is a loop
      # flag is 'C' if the current is a nested loop
      # flag is 'B' if the current is a if-else
      self.flag = flag
      # symbol stands for the symbol of the current
      # symbol is '' if flag is 'S'
      # symbol is Letter if flag is 'L' such as 'A'
      self.symbol =''


# class Program:
#     def __init__(self,flag,actionList,condition="condition"):
#         self.flag=flag
#         self.actionList=actionList
#         self.condition=condition
#         self.strcondition="phi"
#         self.examPos=set()
#         self.examNeg=set()
#         self.example=[]


class Prog:
    def __init__(self,flag,firstActions,secondActions,firstAbbrChar,secondAbbrChar,regex,condition="condition"):
        self.flag=flag #value: Branch,Seq,Loop
        self.firstActions=firstActions #Prog, String(the name of action)
        self.secondActions=secondActions #Prog, String(the name of action)
        self.firstAbbrChar=firstAbbrChar #Prog, String(the name of action)
        self.secondAbbrChar=secondAbbrChar #Prog, String(the name of action)
        self.condition=condition
        self.regex=regex #The  combine  regex of firstActions and  regex of secondActions
        self.examPos=set()
        self.examNeg=set()
        self.example=[]


class State:
    def __init__(self,numExpress=[],predicates={}):
        self.predicates = predicates
        self.numExpress = numExpress
        self.key=0
    def printState(self):
        print(self.predicates)
        for item in self.numExpress:
            print("("+item.op+" "+item.left+" "+item.right+")")
    def add_predicate(self,predicate,value):
        self.predicates[predicate]=value
    def __eq__(self, value):
        return self.numExpress == value.numExpress and self.predicates == value.predicates
    def __hash__(self):
        return hash(self.key)
    def add_predicates(self,predicate_set):
        for atom in  predicate_set:
            self.predicates[atom]=1

    def add_numExpress(self,numExpress):
        self.numExpress.append(numExpress)

    def add_numExpresss(self,numExpress_set):
        self.numExpress.update(numExpress_set)

    def remove_predicates(self, predicate_set):
        for atom in  predicate_set:
            self.predicates[atom]=0
    def update_metric(self,metric_set1):
        j=0
        metric_set=copy.deepcopy(metric_set1)
        while j<len(metric_set):
            i=0
            while i < len(self.numExpress):
                metric_set[j].right= metric_set[j].right.replace(self.numExpress[i].left,self.numExpress[i].right)
                i=i+1
            j=j+1

        for atom in metric_set:
            try:
                Exp=""
                i=0
                while i<len(self.numExpress):
                    if self.numExpress[i].left==atom.left:
                        break
                    i=i+1
                if(atom.op=="increase"):
                    Exp=self.numExpress[i].right+"+"+atom.right
                    self.numExpress[i].right=str(eval(Exp))
                elif(atom.op=="decrease"):
                    Exp=self.numExpress[i].right+"-"+atom.right
                    self.numExpress[i].right=str(eval(Exp))
                elif(atom.op=="assign"):
                    self.numExpress[i].right=str(eval(atom.right))
            except Exception:
                continue
    def copy(self):
        ret = State()
        ret.predicates=self.predicates
        ret.numExpress=self.numExpress
        return ret


class Action:
    def __init__(self):
        self.name = ""
        self.preFormu = []
        self.preMetric = []
        self.effect_pos = set()
        self.effect_neg=set()
        self.effect_Metric =[]
        self.subAction=[]
    def add_predicate(self,predicate):
        self.preFormu.add(predicate)


class NumExpression:
    def __init__(self,op,subleft,subright):
        self.op = op
        self.left = subleft
        self.right = subright
    def __eq__(self,tmp):
        return self.op == tmp.op and self.left == tmp.left and float(self.right) == float(tmp.right)
    def __str__(self):
        return  self.left+" "+self.op+" "+self.right