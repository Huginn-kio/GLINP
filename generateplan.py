import os
import sys

from datastructure import Item
from generateinit import parseDomain

def generateSequencePlans(domain,probfileSet):
    """

    :function: call ff planner to generate plans
    :param domain: domain name
    :param probfileSet: problem file set
    :return: plans such as [['PICKUP', 'WALK', 'PICKUP', 'WALK', 'PICKUP', 'WALK', 'TIGHTEN', 'TIGHTEN', 'TIGHTEN']]

    """
    domainfile = './domain/' + domain + '/domain.pddl'
    plans = []
    for problemfile in probfileSet:
        output = os.popen("./ff -o " + domainfile + " -f " + problemfile)
        mid = output.read().strip()
        res = mid.split("\n")
        k = len(res)
        if 'unsolvable' in mid:
            print("The domain or problem is unsolvable.")
            sys.exit()
        if 'MAX_PLAN_LENGTH!' in mid:
            print("increase MAX_PLAN_LENGTH! currently 5000")
            sys.exit()
        pstr = res[k - 1].strip()
        # print("pstr:", pstr)
        # only when O E needs to be removed
        # if pstr[0] == '0':
        #     pstr = pstr[1:]
        plan = list(filter(None, pstr.split(" ")))
        plans.append(plan)
    # print(plans)
    return plans


def mapAction(domain):
    """
    :function: map action to letter and letter to action in domain file to simplify the description of the plan
    :param domain: domain name
    :return: actionToLetterList, letterToActionList
    """
    domainfile = './domain/' + domain + '/domain.pddl'
    dom = parseDomain(domainfile)
    # map action to letter
    actionToLetterList = {}
    # map letter to action
    letterToActionList = {}
    # empty action
    emptyAction = '#'
    # a - ascii 97
    count = 97
    # map action to letter and letter to action in domain file to simplify the description of the plan
    for atom in dom.actions:
        actionToLetterList[atom.name.upper()] = chr(count)
        letterToActionList[chr(count)] = atom.name.upper()
        count = count + 1
    actionToLetterList['EMPTYACTION'] = emptyAction
    letterToActionList[emptyAction] = 'EMPTYACTION'
    # for key,value in actionToLetterList.items():
    #     print(key,value)
    # for key,value in letterToActionList.items():
    #     print(key,value)
    return actionToLetterList, letterToActionList


def generateItemPlan(domain,probfileSet):
    # generate plans for each problem
    plans = generateSequencePlans(domain, probfileSet)

    print("\n1.Compute corresponding solution by planner as follows:")
    for plan in plans:
        print(plan)

    # map action to letter and letter to action in domain file to simplify the description of the plan
    actionToLetterList, letterToActionList = mapAction(domain)

    print("\n2.The action representing by letter as follows:")
    print(actionToLetterList)
    print(letterToActionList)

    # handle each plan to prepare for the generation of the regex
    ItemPlan = []
    for plan in plans:
        Items = []
        for act in plan:
            s = actionToLetterList[act]
            Items.append(Item(s, s, 'S'))
        ItemPlan.append(Items)
    return ItemPlan,plans, actionToLetterList, letterToActionList


if __name__ == "__main__":
    # generateSequencePlans('Spanner',['./domain/Spanner/prob1.pddl'])
    # mapAction('Spanner')
    generateItemPlan('Spanner',['./domain/Spanner/prob1.pddl','./domain/Spanner/prob2.pddl'])
