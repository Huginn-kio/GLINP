FINISH_FLAG='finish'
emptyAction='#'
emptyActionName='EmptyAction'
emptyRegex=''
MIN_CHAR='a'
MAX_CHAR='z'
MIN_LARGE_CHAR='A'
MAX_LARGE_CHAR='Z'

print(isinstance('ab',list))

array1 = [1, 2, 3]
array2 = ['a', 'b', 'c']
 
pair_array = list(zip(array1, array2))
for a in pair_array:
    print(a[0])
    print(a[1])

import re

def is_valid_regex(regex):
    try:
        re.compile(regex)
        return True
    except re.error:
        return False

def validate_regex(regex):
    if not regex:
        return False
    if regex[0] == '|':
        return False
    if regex[-1] == '|':
        return False
    if '||' in regex:
        return False
    if regex[0] == '*':
        return False
    if regex[-1] == '*':
        return False
    if '**' in regex:
        return False
    if regex[0] == '+':
        return False
    if regex[-1] == '+':
        return False
    if '++' in regex:
        return False
    if regex[0] == '?':
        return False
    if regex[-1] == '?':
        return False
    if '??' in regex:
        return False
    
    if regex[0] == '(' and regex[-1] == ')':
        depth = 0
        for i in range(len(regex)):
            if regex[i] == '(':
                depth += 1
            elif regex[i] == ')':
                depth -= 1
                if depth == 0 and i < len(regex) - 1:
                    return False
    elif '(' in regex or ')' in regex:
        return False
    
    if '|' in regex:
        parts = regex.split('|')
        for part in parts:
            if not validate_regex(part):
                return False
    
    if '*' in regex:
        parts = regex.split('*')
        for part in parts:
            if not validate_regex(part):
                return False
    
    if '+' in regex:
        parts = regex.split('+')
        for part in parts:
            if not validate_regex(part):
                return False
    
    if '?' in regex:
        parts = regex.split('?')
        for part in parts:
            if not validate_regex(part):
                return False
    
    return True

def main():
    regex = input("请输入要验证的正则表达式：")
    if is_valid_regex(regex):
        if validate_regex(regex):
            print("正则表达式有效并符合要求。")
        else:
            print("正则表达式有效但不符合要求。")
    else:
        print("正则表达式无效。")

if __name__ == "__main__":
    main()
    re.match()
