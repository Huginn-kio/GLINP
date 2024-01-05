class TypedArg:
    def __init__(self,arg_name, arg_type = None):
        self.arg_name = arg_name
        self.arg_type = arg_type
    def asPDDL(self):
        if self.arg_type is None:
            return self.arg_name
        else:
            return self.arg_name + " - " + self.arg_type


# map(function, iterable, ...)
# function: function that is applied to each item of iterable
# lambda: anonymous function
# such as map(lambda x: 2*x, [1, 2, 3, 4]) = [2, 4, 6, 8]
class TypedArgList:
    def __init__(self, args):
        self.args = args
    def asPDDL(self):
        return " ".join(map(lambda x: x.asPDDL(), self.args))


# parse like this: site material - object
# arg_type : object
# arg_name : site material
def parseTypeNameList(tnl):
    args = []
    arg_name = ""
    arg_type = "<NONE>"
    for arg in tnl.singleTypeNameList():
        arg_type = arg.r_type().getText()
        for arg_context in arg.name():
            arg_name = arg_context.getText()
            args.append(TypedArg(arg_name, arg_type))
    for arg_context in tnl.name():
        arg_name = arg_context.getText()
        args.append(TypedArg(arg_name))
    return TypedArgList(args)


class ConstantNumber:
    def __init__(self, val):
        self.val = val
    def asPDDL(self):
        return str(self.val)
    def __eq__(self, other):
        return isinstance(other, ConstantNumber) and self.val == other.val


def parseConstantNumber(number):
    return ConstantNumber(float(number.getText()))


# fhead represents a fluent with name and args
class FHead:
    """ represents a functional symbol and terms, e.g.,  (f a b c)"""
    def __init__(self, name, args):
        self.name = name
        self.args = args
    def asPDDL(self):
        if self.args.asPDDL()=="":
            return "(" + self.name + ")"
        else:
            return "(" + self.name + " " + self.args.asPDDL() + ")"


# FExpression represents a fluent expression
class FExpression:
    """ represents a functional / numeric expression"""
    def __init__(self, op, subexps):
        self.op = op
        self.subexps = subexps
    def asPDDL(self):
        return "(" + self.op + " " + " ".join(map(lambda x: x.asPDDL(), self.subexps))  + ")"


# predicate represents a predicate with name and args
class Predicate:
    def __init__(self, name, args):
        self.name = name
        self.args = args
    def asPDDL(self):
        if self.args.asPDDL()=="":
            return "(" + self.name + ")"
        else:
            return "(" + self.name + " " + self.args.asPDDL() + ")"
    def asPDDLwithouBracket(self):
        if self.args.asPDDL()=="":
            return self.name
        else:
            return self.name


# formula represents a predicate/fluent expression which subformulas represent a expression except the operator
class Formula:
    """ represented a goal description (atom / negated atom / and / or)"""
    def __init__(self, subformulas, op=None, is_effect=False, is_numeric=False):
        self.subformulas = subformulas
        self.op = op
        self.is_effect = is_effect
        self.is_numeric = is_numeric
    def get_predicates(self, positive):
        """ returns positive or negative predicates in this goal description"""
        if self.op is None and positive:
            assert len(self.subformulas) == 1
            return [self.subformulas[0]]
        elif self.op == "not" and not positive:
            assert len(self.subformulas) == 1
            return [self.subformulas[0]]
        elif self.op == "and":
            l = []
            for s in self.subformulas:
                l = l + s.get_predicates(positive)
            return l
        elif self.op == "or":
            raise Exception("Don't know how to handle disjunctive condition " + str(self.subformulas))
        return []
    def asPDDL(self):
        if self.op is None:
            assert len(self.subformulas) == 1
            return self.subformulas[0].asPDDL()
        elif self.op == "not":
            assert len(self.subformulas) == 1
            return "(not " + self.subformulas[0].asPDDL() + ")"
        # add when which -R.pddl has
        elif self.op in ['and', 'or', '>', '<', '=', '>=', '<=', 'increase', 'decrease', 'assign', 'scale-up',
                         'scale-down','when']:
            return "(" + self.op + " " + " ".join(map(lambda x: x.asPDDL(), self.subformulas)) + ")"
        else:
            raise Exception("Don't know how to handle op " + self.op)


def parseFHead(fhead):
    terms = []
    for t in fhead.term():
        if t.VARIABLE() is not None:
            terms.append(TypedArg(t.VARIABLE().getText()))
        elif t.name() is not None:
            terms.append(TypedArg(t.name().getText()))
        else:
            raise Exception("Can't handle term " + fhead.getText())
    return FHead(fhead.functionSymbol().name().getText(), TypedArgList(terms))



def parseFExp(fexp):
    if fexp.NUMBER() is not None:
        return parseConstantNumber(fexp.NUMBER())
    elif fexp.fHead() is not None:
        return parseFHead(fexp.fHead())
    else:
        op = None
        fexp1 = parseFExp(fexp.fExp())
        if fexp.binaryOp() is not None:
            op = fexp.binaryOp().getText()
            fexp2 = parseFExp(fexp.fExp2().fExp())
            return FExpression(op, [fexp1, fexp2])
        else:
            op = "-"
            return FExpression(op, [fexp1])
        return


def parseGoalDescription(gd, is_effect=False):
    if gd.atomicTermFormula() is not None:
        name = gd.atomicTermFormula().predicate().name().getText()
        terms = []
        for t in gd.atomicTermFormula().term():
            if t.VARIABLE() is not None:
                terms.append(TypedArg(t.VARIABLE().getText()))
            elif t.name() is not None:
                terms.append(TypedArg(t.name().getText()))
            else:
                raise Exception("Can't handle term " + gd.getText())
        op = None
        if gd.getChildCount() > 1:
            op = gd.getChild(1).getText()
        return Formula([Predicate(name, TypedArgList(terms))], op, is_effect=is_effect)
    elif gd.fComp() is not None:
        op = gd.fComp().binaryComp().getText()
        fexp1 = parseFExp(gd.fComp().fExp()[0])
        fexp2 = parseFExp(gd.fComp().fExp()[1])
        return Formula([fexp1, fexp2], op, is_effect=is_effect)
    else:
        op = gd.getChild(1).getText()
        preds = []
        for p in gd.goalDesc():
            preds.append(parseGoalDescription(p))
        return Formula(preds, op, is_effect=is_effect)