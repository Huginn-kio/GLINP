from parseGlinp.pythonpddl.parsepddl import TypedArg, TypedArgList, parseFHead, parseFExp, Formula, \
    parseGoalDescription, parseConstantNumber


# parse like this: (on?x - object ?y - object)
def parseTypeVariableList(tvl):
    args = []
    arg_name = ""
    arg_type = "<NONE>"
    for arg in tvl.singleTypeVarList():
        arg_type = arg.r_type().getText()
        for arg_context in arg.VARIABLE():
            arg_name = arg_context.getText()
            args.append(TypedArg(arg_name, arg_type))
    for arg_context in tvl.VARIABLE():
        arg_name = arg_context.getText()
        args.append(TypedArg(arg_name))
    return TypedArgList(args)


class Function:
    def __init__(self, name, args):
        self.name = name
        self.args = args
    def asPDDL(self):
        return "(" + self.name + " " + self.args.asPDDL() + ")"
    def asPDDLwithouBracket(self):
        return self.name




def parsePEffect(peff):
    if peff.assignOp() is not None:
        op = peff.assignOp().getText()
        head = parseFHead(peff.fHead())
        exp = parseFExp(peff.fExp())
        return Formula([head, exp], op, is_effect=True, is_numeric=True)
    else:
        return parseGoalDescription(peff, is_effect=True)


class Action:
    def __init__(self, name, parameters, pre, eff):
        self.name = name
        self.parameters = parameters
        self.pre = pre  # precondition formula
        self.eff = eff  # list of effects
    def get_pre(self, positive):
        return self.pre.get_predicates(positive)
    def get_eff(self, positive):
        l = []
        for x in self.eff:
            if type(x) is not Action:
                l = l + x.get_predicates(positive)
        return l
    def asPDDL(self):
        # empty action which is a condition effect in -R.pddl
        if(self.name == ''):
            return "(when " + self.pre.asPDDL() + "(and " + " ".join(map(lambda x: x.asPDDL(), self.eff)) + ")"+ ")\n"
        else:
            ret = ""
            ret = ret + "(:action " + self.name + "\n"
            ret = ret + "\t:parameters (" + self.parameters.asPDDL() + ")\n"
            ret = ret + "\t:precondition " + self.pre.asPDDL() + "\n"
            ret = ret + "\t:effect (and " + " ".join(map(lambda x: x.asPDDL(), self.eff)) + ")\n"
            ret = ret + ")"
        return ret


def parseCEffect(ceff):
    if ceff.condEffect() is not None:
        effs=list(map(lambda x: parsePEffect(x), ceff.condEffect().pEffect()))
        # condition effect is a empty action
        return Action('', '', parseGoalDescription(ceff.goalDesc()), effs)
    else:
        return parsePEffect(ceff.pEffect())


def parseAction(act):
    name = act.actionSymbol().getText()
    parameters = parseTypeVariableList(act.typedVariableList())
    body = act.actionDefBody()
    action_cond = []
    pre = parseGoalDescription(body.precondition().goalDesc())
    effs = list(map(lambda x: parseCEffect(x), body.effect().cEffect()))
    return Action(name, parameters, pre, effs)


def parseSimpleDurationConstraint(sdc):
    op = sdc.durOp().getText()
    if sdc.durValue().NUMBER() is not None:
        val = parseConstantNumber(sdc.durValue().NUMBER())
    elif sdc.durValue().fExp() is not None:
        val = parseFExp(sdc.durValue().fExp())
    return (op, val)


class TimedFormula:
    """ represents a timed goal description"""
    def __init__(self, timespecifier, gd):
        self.timespecifier = timespecifier
        self.formula = gd
    def asPDDL(self):
        if self.timespecifier == "start":
            return "(at start " + self.formula.asPDDL() + ")"
        elif self.timespecifier == "end":
            return "(at end " + self.formula.asPDDL() + ")"
        elif self.timespecifier == "all":
            return "(over all " + self.formula.asPDDL() + ")"
        else:
            return "(at " + str(self.timespecifier) + " " + self.formula.asPDDL() + ")"


def parseTimedGoalDescription(timedGD):
    gd = parseGoalDescription(timedGD.goalDesc())
    timespecifier = None
    if timedGD.interval() is not None:
        timespecifier = timedGD.interval().getText()
    elif timedGD.timeSpecifier() is not None:
        timespecifier = timedGD.timeSpecifier().getText()
    return TimedFormula(timespecifier, gd)


def parsePrefTimedGoalDescription(prefTimedGD):
    timedGD = parseTimedGoalDescription(prefTimedGD.timedGD())
    name = prefTimedGD.name()
    if name is not None:
        raise Exception("Can't handle preferences " + prefTimedGD.getText())
        return PrefTimedGoalDescription(name, timedGD)
    else:
        return timedGD


def parseTimedEffect(timedEffect):
    timespecifier = timedEffect.timeSpecifier().getText()
    if timedEffect.cEffect() is not None:
        ceff = parseCEffect(timedEffect.cEffect())
        return TimedFormula(timespecifier, ceff)
    else:
        raise Exception("Don't know how to handle effect " + timedEffect.getText())


def parseDaEffect(daEffect):
    if daEffect.timedEffect() is not None:
        te = parseTimedEffect(daEffect.timedEffect())
        return [te]
    else:
        op = daEffect.getChild(1).getText()
        assert op == 'and'
        effs = []
        for p in daEffect.daEffect():
            effs = effs + parseDaEffect(p)
        return effs


class DurativeAction:
    def __init__(self, name, parameters, duration_lb, duration_ub, cond, eff):
        self.name = name
        self.parameters = parameters
        self.duration_lb = duration_lb
        self.duration_ub = duration_ub
        self.cond = cond  # list of conditions
        self.eff = eff  # list of effects
    def get_cond(self, timespecifier, positive):
        l = []
        for x in self.cond:
            if x.timespecifier == timespecifier:
                l = l + x.formula.get_predicates(positive)
        return l
    def get_eff(self, timespecifier, positive):
        l = []
        for x in self.eff:
            if x.timespecifier == timespecifier:
                l = l + x.formula.get_predicates(positive)
        return l
    def asPDDL(self):
        ret = ""
        ret = ret + "(:durative-action " + self.name + "\n"
        ret = ret + "\t:parameters (" + self.parameters.asPDDL() + ")\n"
        ret = ret + "\t:duration "
        if self.duration_lb == self.duration_ub:
            ret = ret + "(= ?duration " + self.duration_lb.asPDDL() + ")\n"
        else:
            ret = ret + "(and (<= ?duration " + self.duration_ub.asPDDL() + ") (>= ?duration " + self.duration_lb.asPDDL() + "))\n"
        ret = ret + "\t:condition (and " + " ".join(map(lambda x: x.asPDDL(), self.cond)) + ")\n"
        ret = ret + "\t:effect (and " + " ".join(map(lambda x: x.asPDDL(), self.eff)) + ")\n"
        ret = ret + ")"
        return ret


def parseDurativeAction(da):
    name = da.actionSymbol().getText()
    parameters = parseTypeVariableList(da.typedVariableList())
    body = da.daDefBody()
    duration = body.durationConstraint().simpleDurationConstraint()
    duration_lb = None
    duration_ub = None
    if duration is not None:
        if len(duration) == 1:
            d = parseSimpleDurationConstraint(duration[0])
            assert d[0] == '='
            duration_lb = d[1]
            duration_ub = d[1]
        else:
            assert len(duration) == 2
            d1 = parseSimpleDurationConstraint(duration[0])
            d2 = parseSimpleDurationConstraint(duration[1])
            if d1[0] == '<=':
                assert d2[0] == '>='
                duration_lb = d2[1]
                duration_ub = d1[1]
            elif d1[0] == '>=':
                assert d2[0] == '<='
                duration_lb = d1[1]
                duration_ub = d2[1]
            else:
                raise Exception("Can't parse duration " + duration.getText())
    action_cond = []
    cond = body.daGD()
    if cond.typedVariableList() is not None:
        raise Exception("Can't handle forall " + cond.getText())
    elif cond.prefTimedGD() is not None:
        action_cond.append(parsePrefTimedGoalDescription(cond.prefTimedGD()))
    elif cond.daGD() is not None:
        for x in cond.daGD():
            action_cond.append(parsePrefTimedGoalDescription(x.prefTimedGD()))
    effs = parseDaEffect(body.daEffect())
    return DurativeAction(name, parameters, duration_lb, duration_ub, action_cond, effs)


class Domain:
    """ represents a PDDL domain"""
    def __init__(self, name, reqs, types, constants, predicates, functions, actions, durative_actions):
        self.name = name
        self.reqs = reqs
        self.types = types
        self.constants = constants
        self.predicates = predicates
        self.functions = functions
        self.actions = actions
        self.durative_actions = durative_actions
    def asPDDL(self):
        ret = ""
        ret = ret + "(define (domain " + self.name + ")\n"
        ret = ret + "\t(:requirements " + " ".join(self.reqs) + ")\n"
        ret = ret + "\t(:types " + self.types.asPDDL() + ")\n"
        ret = ret + "\t(:constants " + self.constants.asPDDL() + ")\n"
        if len(self.functions) > 0:
            ret = ret + "\t(:functions\n"
            for func in self.functions:
                ret = ret + "\t\t" + func.asPDDL() + "\n"
            ret = ret + "\t)\n"
        if len(self.predicates) > 0:
            ret = ret + "\t(:predicates\n"
            for pred in self.predicates:
                ret = ret + "\t\t" + pred.asPDDL() + "\n"
            ret = ret + "\t)\n"
        for a in self.actions:
            ret = ret + a.asPDDL() + "\n"
        for da in self.durative_actions:
            ret = ret + da.asPDDL() + "\n"
        ret = ret + ")"
        return ret