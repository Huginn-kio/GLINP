from parseGlinp.pythonpddl.parsepddl import parseConstantNumber, FHead, FExpression, TypedArgList, TypedArg


class TotalTime:
    """ represents (total-time)"""
    def __init__(self):
        pass
    def asPDDL(self):
        return "total-time"
    def __eq__(self, other):
        return isinstance(other, TotalTime)


def parseMetricFExp(fexp):
    if fexp.NUMBER() is not None:
        return parseConstantNumber(fexp.NUMBER())
    elif fexp.functionSymbol() is not None:
        return FHead(fexp.functionSymbol().name().getText(), TypedArgList(list(map(lambda x: TypedArg(x.NAME().getText()), fexp.name()))))
    elif fexp.getText() == 'total-time':
        return TotalTime()
    else:
        op = None
        subexps = list(map(parseMetricFExp, fexp.metricFExp()))
        if fexp.binaryOp() is not None:
            op = fexp.binaryOp().getText()
        else:
            assert fexp.getChildCount() > 1
            op = fexp.getChild(1).getText()
        return FExpression(op, subexps)


class Metric:
    """ represents a metric/optimization objective"""
    def __init__(self, objective, fexp):
        self.objective = objective
        self.fexp = fexp
    def asPDDL(self):
        return "(:metric " + self.objective + " " + self.fexp.asPDDL() + ")"


class Problem:
    """ represents a PDDL problem"""
    def __init__(self, name, domainname, objects, init, goal, metric=None):
        self.name = name
        self.domainname = domainname
        self.objects = objects
        self.init = init
        self.goal = goal
        self.metric = metric
    def asPDDL(self):
        ret = ""
        ret = ret + "(define (problem " + self.name + ")\n"
        ret = ret + "\t(:domain " + self.domainname + ")\n"
        ret = ret + "\t(:objects " + self.objects.asPDDL() + ")\n"
        ret = ret + "\t(:init " +  self.init.asPDDL() + ")\n"
        ret = ret + "\t(:goal " +  self.goal.asPDDL() + ")\n"
        if self.metric is not None:
            ret = ret + "\t" + self.metric.asPDDL() + "\n"
        ret = ret + ")"
        return ret