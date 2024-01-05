# get a parser tree corresponding to a pddl file
import re
import random
from antlr4 import FileStream, CommonTokenStream
from z3 import *

from parseGlinp.pddlLexer import pddlLexer
from parseGlinp.pddlParser import pddlParser
from parseGlinp.pythonpddl.parsedomain import Function, parseTypeVariableList, parseAction, parseDurativeAction, Domain
from parseGlinp.pythonpddl.parsepddl import parseTypeNameList, TypedArgList, Predicate


# get a parser tree corresponding to a pddl file
def readAndParseFile(file):
    inp = FileStream(file)
    lexer = pddlLexer(inp)
    stream = CommonTokenStream(lexer)
    parser = pddlParser(stream)
    return parser


def parseDomainObject(domain):
    domainname = domain.domainName().name().getText()
    reqs = []
    for r in domain.requireDef().REQUIRE_KEY():
        reqs.append(r.getText())
    if domain.typesDef() is not None:
        types = parseTypeNameList(domain.typesDef().typedNameList())
    else:
        types = TypedArgList([])
    if domain.constantsDef() is not None:
        constants = parseTypeNameList(domain.constantsDef().typedNameList())
    else:
        constants = TypedArgList([])
    functions = []
    if domain.functionsDef() is not None:
        for func in domain.functionsDef().functionList().atomicFunctionSkeleton():
            functions.append(
                Function(func.functionSymbol().name().getText(), parseTypeVariableList(func.typedVariableList())))
    predicates = []
    if domain.predicatesDef() is not None:
        for pred in domain.predicatesDef().atomicFormulaSkeleton():
            predicates.append(
                Predicate(pred.predicate().name().getText(), parseTypeVariableList(pred.typedVariableList())))
    durative_actions = []
    actions = []
    for action in domain.structureDef():
        if action.actionDef() is not None:
            actions.append(parseAction(action.actionDef()))
        elif action.durativeActionDef() is not None:
            durative_actions.append(parseDurativeAction(action.durativeActionDef()))
    d = Domain(domainname, reqs, types, constants, predicates, functions, actions, durative_actions)
    return d

def parseDomain(domainfile):
    dtree = readAndParseFile(domainfile)
    domain = dtree.domain()
    # print("domain:",domain)
    if domain is not None:
        dom = parseDomainObject(domain)
    else:
        raise Exception("No domain defined in " + domainfile)
    return dom



predicate_list = []  # list of predicates
variables_list = []  # list of variables

def prefix_to_infix(prefix_expression):
    """

    :function  Convert prefix expression to infix expression
    :param     prefix_expression: prefix expression such as '(not(ccontainig))' or '(=(numeh)2)'
    :return    infix expression such as 'Not(ccontainig)' or '(numeh==2)'

    """
    operand_v_regex = re.compile(r'^[a-zA-Z][a-zA-Z0-9_]*$') # variable
    operand_n_regex = re.compile(r'^[0-9]+$') # number
    operator_regex = re.compile(r'[+\-*/]|[><]=?|=') # operator
    tokens = prefix_expression.replace('(', ' ').replace(')', ' ').split() # remove all ( and ) and split
    # print("tokens:",tokens)
    if(len(tokens) == 1):
        return str(convert_operand_b_to_z3_type(tokens[0]))
    if(tokens[0] == 'not'):
        return 'Not('+ str(convert_operand_b_to_z3_type(tokens[1])) +')'
    stack = []
    for token in reversed(tokens):
        # print(token)
        if operand_v_regex.match(token): # variable
            stack.append(convert_operand_v_to_z3_type(token))
        elif operand_n_regex.match(token): # number
            stack.append(int(token))
        elif operator_regex.match(token): # operator
            op1 = stack.pop()
            op2 = stack.pop()
            if(token == '='):
                stack.append('%s%s%s' % (op1, '==', op2))
            else:
                stack.append('%s%s%s' % (op1, token, op2))
    return stack.pop()


def convert_operand_v_to_z3_type(oprand_v):  # convert variable to z3 type int
    """

    :function  Convert variable to z3 type int
    :param     oprand_v: variable such as 'numeh' or 'numig'
    :return    z3 type int such as 'numeh' or 'numig'

    """
    global variables_list
    variables_list.append(oprand_v)
    return Int(oprand_v)


def convert_operand_b_to_z3_type(oprand_b): # convert variable to z3 type boolean
    """

    :function  Convert variable to z3 type boolean
    :param     oprand_b: variable such as 'contable' or 'sontable'
    :return    z3 type boolean such as 'contable' or 'sontable'

    """
    global predicate_list
    predicate_list.append(oprand_b)
    return Bool(oprand_b)


def convert_prefix_expression_list_to_constraint_list(prefix_expression_list):
    """

    :function  Convert prefix expression list to constraint list
    :param prefix_expression_list: prefix expression list such as ['(contable)', '(sontable)', '(cempty)', '(cclean)', '(not(ccontainig))','(not(ccontainct))', '(not(scontainct))', '(=(numeh)2)', '(>(numig)0)']
    :return constrant_list: constrant list such as ['contable', 'sontable', 'cempty', 'cclean', 'Not(ccontainig)', 'Not(ccontainct)', 'Not(scontainct)', '(numeh==2)', '(numig>0)']
    :return variables_list: variables list such as ['numeh', 'numig']
    :return predicate_list: predicate list such as ['contable', 'sontable', 'cempty', 'cclean', 'ccontainig', 'ccontainct', 'scontainct']

    """
    global variables_list
    global predicate_list
    variables_list = []
    predicate_list = []
    constrant_list = []
    # get And constrant string
    for prefix_expression in prefix_expression_list:
        constrant_list.append(prefix_to_infix(prefix_expression))
    return constrant_list, variables_list,predicate_list


def convert_constraint_list_to_z3_type(constrant_list, variables_list, predicate_list):
    """

    :function Convert constraint list to z3 type
    :param constrant_list: list of constraints such as ['contable', 'sontable', 'cempty', 'cclean', 'Not(ccontainig)', 'Not(ccontainct)', 'Not(scontainct)', '(numeh==2)', '(numig>0)']
    :param variables_list: list of variables such as ['numeh', 'numig']
    :param predicate_list: list of predicates such as ['contable', 'sontable', 'cempty', 'cclean', 'ccontainig', 'ccontainct', 'scontainct']
    :return: z3 type constraints such as And(contable, sontable, cempty, cclean, Not(ccontainig), Not(ccontainct), Not(scontainct), numeh==2, numig>0)

    """
    # must declare global variables and predicates otherwise z3 can not recognize them after
    for var in variables_list:
        exec("global " + var + "; "  + var+"=Int('%s')"%var)
    for pred in predicate_list:
        exec("global " + pred + "; "  + pred+"=Bool('%s')"%pred)
    # Only Not(predicate)
    expr_list = [eval(constrant) for constrant in constrant_list]
    z3_constrant = And(expr_list)
    return z3_constrant

def modifyGenerateInitialState(domain,bound,stateSize,modelSort):
    new_init_upred_list, new_init_dpred_list, new_init_uvar_list, new_init_dvar_list, init_cons, goal_cons = generateInitialcons(domain)

    # to get init states text
    inits_text = generate_init_states(modelSort, stateSize, bound, new_init_upred_list, new_init_dpred_list,
                                      new_init_uvar_list,
                                      new_init_dvar_list, init_cons, goal_cons)
    domainRoot = './domain/' + domain
    glinpfile = domainRoot + '/glinp.pddl'
    # parse problem file to get init constraints
    problem = readAndParseFile(glinpfile).problem()
    # to get problem text
    probs_text = generate_problem_text(problem, inits_text, stateSize)
    # to write problem text to file
    write_to_file(modelSort, probs_text, domain)


def generateInitialcons(domain):
    domainRoot = './domain/' + domain
    # print("domainRoot: ", domainRoot)
    domainfile = domainRoot + '/domain.pddl'
    # print("domainfile: ", domainfile)
    glinpfile = domainRoot + '/glinp.pddl'
    # print("glinpfile: ", glinpfile)
    # parse problem file to get init constraints
    problem = readAndParseFile(glinpfile).problem()
    init_states = [str(expr.getText()) for expr in problem.init().goalDesc().getChildren()]
    init_state = init_states[2:-1]

    goal_states = [str(expr.getText()) for expr in problem.goal().goalDesc().getChildren()]
    goal_state = goal_states[2:-1]

    init_cons_list, init_var_list, init_pred_list = convert_prefix_expression_list_to_constraint_list(init_state)
    goal_cons_list, goal_var_list, goal_pred_list = convert_prefix_expression_list_to_constraint_list(goal_state)

    # original z3 constraints for init
    init_cons = convert_constraint_list_to_z3_type(init_cons_list, init_var_list, init_pred_list)
    goal_cons = convert_constraint_list_to_z3_type(goal_cons_list, goal_var_list, goal_pred_list)

    print("init_cons: ", init_cons)

    # parse domain file to get predicates and functions
    dom = parseDomain(domainfile)
    predicate = [p.asPDDLwithouBracket() for p in dom.predicates]
    function = [f.asPDDLwithouBracket() for f in dom.functions]

    # predicate and function list for z3 type in domain
    domain_predicate_list = []
    domain_function_list = []

    # generate init constraints for each predicate and function to determine if it is true or false or if it has a value
    domain_predicate_init_cons = {}
    domain_function_init_cons = {}

    # generate z3 variables for each function to determine its upper bound
    upper_init_map = {}
    all_map = {}

    init_map = {}

    # must eval(i) otherwise i is a string
    for i in predicate:
        exec("global " + i + "; " + i + "=Bool('%s')" % i)
        # exec(i + "=Bool('%s')" % i)
        exec(f"constraint_{i}=Implies({init_cons},Or({i},Not({i})))")
        domain_predicate_init_cons[eval(i)] = eval(f"constraint_{i}")
        domain_predicate_list.append(eval(i))

    # print("domain_predicate_list: ", domain_predicate_list)

    for i in function:
        exec("global " + i + "; " + i + "=Int('%s')" % i)
        # exec(i + "=Int('%s')" % i)
        exec(f"upper_init_{i}=Int('upper_init_{i}')")
        exec(f"all_{i}=Int('all_{i}')")
        upper_init_map[eval(i)] = eval(f"upper_init_{i}")
        all_map[eval(i)] = eval(f"all_{i}")
        domain_function_list.append(eval(i))

    # print("domain_function_list: ", domain_function_list)

    for i in domain_function_list:
        exec(
            f"upper_constraints_{i}=[ForAll({domain_function_list},Implies({init_cons},{i}<=upper_init_{i})),ForAll(all_{i},Implies(ForAll({domain_function_list},Implies({init_cons},{i}<=all_{i})),all_{i}>=upper_init_{i}))]")
        domain_function_init_cons[i] = eval(f"upper_constraints_{i}")

    # new init undefined predicates
    new_init_upred_list = []
    # new init defined predicates
    new_init_dpred_list = []
    # new init undefined functions
    new_init_uvar_list = []
    # new init defined functions
    new_init_dvar_list = []
    # new init constraints which just contain defined predicates and functions
    new_init_cons = []

    # determine if a predicate is defined in init and goal
    for i in domain_predicate_list:
        init_predicate = isDefinedPredicate(i, init_cons, domain_predicate_init_cons[i])
        if init_predicate is not None:
            init_map[i] = init_predicate
            if init_predicate:
                new_init_cons.append(i)
            else:
                new_init_cons.append(Not(i))
            new_init_dpred_list.append(i)
        else:
            new_init_upred_list.append(i)

    for i in domain_function_list:
        init_function = isDefinedFunction(i, upper_init_map[i], init_cons, domain_function_init_cons[i])
        if init_function is not None:
            init_map[i] = init_function
            new_init_cons.append(eval(f"{i}=={init_function}"))
            new_init_dvar_list.append(i)
        else:
            new_init_uvar_list.append(i)

    # print("new_init_upred_list: ", new_init_upred_list)
    # print("new_init_dpred_list: ", new_init_dpred_list)
    # print("new_init_uvar_list: ", new_init_uvar_list)
    # print("new_init_dvar_list: ", new_init_dvar_list)

    # maybe modify the api
    return new_init_upred_list, new_init_dpred_list, new_init_uvar_list, new_init_dvar_list, init_cons, goal_cons

    # to get init states text
    # inits_text = generate_init_states(modelSort,stateSize, bound, new_init_upred_list, new_init_dpred_list, new_init_uvar_list,
    #                                   new_init_dvar_list, init_cons,goal_cons)
    # # to get problem text
    # probs_text = generate_problem_text(problem, inits_text, stateSize)
    # # to write problem text to file
    # write_to_file(modelSort,probs_text, domain)


def generate_init_states(modelSort,stateSize,bound,init_upred_list,init_dpred_list,init_uvar_list,init_dvar_list,original_init_cons,goal_cons):
    """

    :function generate init states text
    :param stateSize: the number of init states
    :param bound: the lower bound of undefined variables
    :param init_upred_list: undefined predicates in init
    :param init_dpred_list: defined predicates in init
    :param init_uvar_list: undefined functions in init
    :param init_dvar_list: defined functions in init
    :param original_init_cons: original init constraints
    :return init states text

    """
    # generate Solver and add original init constraints for all init states
    s = Solver()
    s.add(original_init_cons)
    # add undefined variables constraints for all init states
    # restrict the lower bound of undefined variables
    if modelSort == 1:
        for var in init_uvar_list:
            s.add(eval(f"{var}>={bound}"))
    # random init states
    # for Arith init has no n
    elif modelSort == 2:
        for var in init_uvar_list:
            s.add(eval(f"{var}>=0"))
    inits_text = []
    # to avoid the same state and generate different init states
    notEqualList = []
    while len(inits_text) < stateSize:
        init_text = '(:init' + '\n'
        # to generate the next state
        s.push()
        # to avoid the same state
        constrain = ''
        for item in notEqualList:
            constrain += item + ','
        if constrain != '':
            # constrain[:-1] to remove the last ','
            constrain = 'Not(Or(' + constrain[:-1] + "))"
            s.add(eval(constrain))
        # if it just has one state , it will just generate the same state
        if s.check() == sat:
            initial = s.model()
            new_init_states_cons = []
            # print(initial)
            notEqualItem = 'True'
            for pred in init_upred_list:
                option = random.randint(0, 99)
                if (option % 2 == 0):
                    init_text += '(' + str(pred) + ')' + '\n'
                    new_init_states_cons.append(pred)
                else:
                    init_text += '(not (' + str(pred) + '))' + '\n'
                    new_init_states_cons.append(Not(pred))
            for dpred in init_dpred_list:
                if initial[dpred]:
                    init_text += '(' + str(dpred) + ')' + '\n'
                    new_init_states_cons.append(dpred)
                else:
                    init_text += '(not (' + str(dpred) + '))' + '\n'
                    new_init_states_cons.append(Not(dpred))
            for var in init_uvar_list:
                init_text += '( = ('+ str(var) +') ' + str(initial[var]) + ')' + '\n'
                notEqualItem += "," + str(var) + "==" + str(initial[var])
                new_init_states_cons.append(eval(f"{var}=={initial[var]}"))
            for var in init_dvar_list:
                init_text += '( = ('+ str(var) +') ' + str(initial[var]) + ')' + '\n'
                new_init_states_cons.append(eval(f"{var}=={initial[var]}"))
            notEqualList.append('And(' + notEqualItem + ")")
            init_text += ')'
            # print("init_text:",init_text)
            print("new_init_states_cons:",new_init_states_cons)
            solver = Solver()
            solver.add(goal_cons)
            if solver.check(new_init_states_cons) == sat:
                print("the init state has satisfied the goal state,and we will generate another init state")
            else:
                inits_text.append(init_text)
            s.pop()
        else:
            print("Incorrect formalization of GLINP problem.")
            sys.exit()
    return inits_text


def generate_problem_text(problem,inits_text,stateSize):
    """

    :function generate problem text
    :param problem: the problem
    :param inits_text: init states text
    :param stateSize: the number of init states
    :return problems_text

    """
    problems_text = []
    for i in range(stateSize):
        problem_text = '(define'
        problemDecl = problem.problemDecl().name().getText()
        problemDomain = problem.problemDomain().name().getText()
        goal = problem.goal().getText()
        problem_text += '(problem ' + problemDecl + ')\n'
        problem_text += '(:domain ' + problemDomain + ')\n'
        problem_text += inits_text[i] + '\n'
        problem_text += goal + '\n'
        problem_text += ')'
        # print("problem_text:",problem_text)
        problems_text.append(problem_text)
    return problems_text


def write_to_file(modelSort,problems_text,domain):
    """

    :function write to file
    :param problems_text: problems text
    :return None

    """
    # to get the path of problem folder
    if modelSort == 1:
        prob_path = './domain/' + domain
    elif modelSort == 2:
        prob_path = './domain/' + domain + '/Random'
    # print(prob_path)
    for i in range(len(problems_text)):
        with open(prob_path + '/prob' + str(i+1) + '.pddl', 'w') as f:
            f.write(problems_text[i])


def setRandomBool():
    """

    :function set random bool
    :return True or False

    """
    option = random.randint(0, 99)
    if (option % 2 == 0):
        return True
    else:
        return False

def isDefinedPredicate(i,cons,predicate_cons):
    """

    :function to check whether the predicate is defined
    :param i: the predicate
    :param cons: the original z3 constraints for init
    :param predicate_cons: the predicate constraints to determine whether the predicate is defined
    :return True or False

    """
    s = Solver()
    s.add(cons)
    s.add(predicate_cons)
    res = None
    if s.check() == sat:
        model = s.model()
        res = model[i]
        # print("{} = {}".format(i,res))
    # else:
        # print("i is not defined")
    return res


def isDefinedFunction(i,upper,cons,function_cons):
    """

    :function to check whether the function is defined
    :param i: the function
    :param upper: the upper bound variable of undefined functions
    :param cons: the original z3 constraints for init
    :param function_cons: the function constraints to determine whether the function is defined

    """
    s = Solver()
    s.add(cons)
    s.add(function_cons)
    res = None
    if s.check() == sat:
        model = s.model()
        res = model[upper]
        # print("{} = {}".format(upper,res))
    # else:
        # print("upper is not defined")
    return res



def addInitialState(domain, modelSort,stateNum,states):
    domainRoot = './domain/' + domain
    glinpfile = domainRoot + '/glinp.pddl'
    # parse problem file to get init constraints
    problem = readAndParseFile(glinpfile).problem()
    domainfile = domainRoot + '/domain.pddl'
    if modelSort == 2:
        domainRoot = domainRoot + "/Random"
    if not os.path.exists(domainRoot):
        os.mkdir(domainRoot)
    dom = parseDomain(domainfile)
    predicate = [p.asPDDLwithouBracket() for p in dom.predicates]
    function = [f.asPDDLwithouBracket() for f in dom.functions]

    for i in predicate:
        exec(i + "=Bool('%s')" % i)
    for i in function:
        exec(i + "=Int('%s')" % i)

    # get domain cons
    init_upred_list,init_dpred_list,init_uvar_list,init_dvar_list,original_init_cons,goal_cons = generateInitialcons(
        domain)

    index = stateNum
    notEqualList = []
    constrain = ''
    for times in range(len(states)):
        s = Solver()
        # print(states[times])
        for i in predicate:
            a = eval("states[times]['(" + i + ")']")
            s.add(eval(str(i) + " == " + str(a)))
        for i in function:
            a = eval("states[times]['(" + i + ")']")
            s.add(eval(str(i) + " == " + str(a)))

        init_texts = []
        #add constrains
        init_text = '(:init' + '\n'
        for item in notEqualList:
            constrain += item + ','
        if constrain != '':
            # constrain[:-1] to remove the last ','
            constrain = 'Not(Or(' + constrain[:-1] + "))"
            s.add(eval(constrain))
        # if it just has one state , it will just generate the same state
        if s.check() == sat:
            initial = s.model()
            # print(initial)
            notEqualItem = 'True'
            for pred in init_upred_list:
                option = random.randint(0, 99)
                if (option % 2 == 0):
                    init_text += '(' + str(pred) + ')' + '\n'
                else:
                    init_text += '(not (' + str(pred) + '))' + '\n'
            for dpred in init_dpred_list:
                if initial[dpred]:
                    init_text += '(' + str(dpred) + ')' + '\n'
                else:
                    init_text += '(not (' + str(dpred) + '))' + '\n'
            for var in init_uvar_list:
                init_text += '( = (' + str(var) + ') ' + str(initial[var]) + ')' + '\n'
                notEqualItem += "," + str(var) + "==" + str(initial[var])
            for var in init_dvar_list:
                init_text += '( = (' + str(var) + ') ' + str(initial[var]) + ')' + '\n'
            notEqualList.append('And(' + notEqualItem + ")")
            init_text += ')'
            init_texts.append(init_text)
            problems_text = generate_problem_text(problem, init_texts, 1)
            f = open(domainRoot + "/prob" + str(index) + ".pddl", "w")
            f.writelines(problems_text[0])
            f.close()
            index = index + 1
            times = times + 1
        else:
            print("Incorrect formalization of GLINP problem.")
            sys.exit()




if __name__ == "__main__":
    modifyGenerateInitialState('MNestVar2',3,2,2)