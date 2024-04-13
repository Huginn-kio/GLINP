import re

def custom_match(pattern, string, flags=0):
    match_obj = re.match(pattern, string, flags)
    if not match_obj:
        return None
    
    # 获取正则表达式模式
    regex = match_obj.re.pattern
    
    # 修改正则表达式模式，确保循环至少匹配两次
    modified_regex = regex.replace('*', '{2,}')
    
    # 重新编译修改后的正则表达式
    modified_pattern = re.compile(modified_regex, flags)
    
    # 使用修改后的正则表达式进行匹配
    return modified_pattern.match(string)

# 用法示例
#pattern = r'((ab)*c)*(d|(c|f))'

#pattern=r'(a)(((ab)*|(a|e))aa((aac)*a*)*)'
#string = 'aababaaaacaacaaaacaacaa'
pattern=r'((c)*)((((a)*))((((|(((b)*)(e((a)*)))))(((c)((((|(d(((((c)*)a)*)(((c(((a)*)(((c)*)(e(((a)*)(b(d(a(((c)*)a)))))))))*)(c(((a)*)((c)*))))))))(((e)(((((c((((a)*)(b(d(a(((c)*)(a(c(((a)*)(((c)*)e)))))))))*))|(|c)))(((((a)*))(((d)((|(b(a(((c)*)(a(c(((a)*)(((b)*)(((e(((a)*)(b(d(a(((c)*)(a(c(((a)*)((c)*))))))))))*)(e(((a)*)d)))))))))))))))))))))))))))'
string = 'ccaaacecaaadbaccacaaabbeaaabdaccacaaacceaaabdaccacaaacceaaabdaccacaaacceaaad'
match=custom_match(pattern, string)
if match:
    # 使用match.group(1)来获取第一个子模式的匹配内容
    print("1 part:", match.group(1))
    # 使用match.group(2)来获取第二个子模式的匹配内容
    print("2 part:", match.group(3))
else:
    print("No match found.")


import re
 
def replace_first(pattern, repl, string):
    # 使用maxsplit=1确保只替换第一个匹配
    return re.sub(pattern, repl, string, count=1)
 
# 示例使用
original_string = "hello python, I am learning python today"
pattern = r'python'
replacement = 'Py'
 
# 替换第一个出现的'python'
result = replace_first(pattern, replacement, original_string)
print(result)  # 输出: hello Py, I am learning python today



def replace_last(text, old, new):
    """
    在文本中替换最后一个匹配的字符串。
    参数:
    text -- 原始字符串
    old -- 需要被替换的子字符串
    new -- 新的字符串，用于替换旧的字符串
    返回:
    修改后的字符串
    """
    # 找到最后一个old的位置
    start_idx = text.rfind(old)
    # 如果没有找到匹配，直接返回原始字符串
    if start_idx == -1:
        return text
    # 构造新的字符串
    return text[:start_idx] + new + text[start_idx + len(old):]
 
# 示例使用
original_text = "((abc)*a)(((abc)*a)*)"
new_text = replace_last(original_text, "*", "{1,}")
print(new_text)  # 输出: hello oldold new oldworld






import re
 
text = "ccaaacecaaadbaccacaaabbeaaabdaccacaaacceaaabdaccacaaacceaaabdaccacaaacceaaad"
pattern = r"((c)*)((((a)*))((((|(((b)*)(e((a)*)))))(((c)((((|(d(((((c)*)a)*)(((c(((a)*)(((c)*)(e(((a)*)(b(d(a(((c)*)a)))))))))*)(c(((a)*)((c)*))))))))(((e)(((((c((((a)*)(b(d(a(((c)*)(a(c(((a)*)(((c)*)e)))))))))*))|(|c)))(((((a)*))(((d)((|(b(a(((c)*)(a(c(((a)*)(((b)*)(((e(((a)*)(b(d(a(((c)*)(a(c(((a)*)((c)*))))))))))*)(e(((a)*)d)))))))))))))))))))))))))))" 
 
matches = re.findall(pattern, text)
print(1)
print(matches) 
print(2)

[('cc', 'c', 'aaacecaaad', 'aaa', 'aaa', 'a', 'cecaaad', 'cecaaad', '', '', '', '', '', '', '', '', 'cecaaad', 'cecaaad', 'c', 'ecaaad', 'ecaaad', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', 'ecaaad', 'ecaaad', 'e', 'caaad', 'caaad', 'c', 'c', 'c', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', 'aaad', 'aaad', 'aaa', 'aaa', 'a', 'd', 'd', 'd', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', ''), 
 ('c', 'c', 'ceaaad', '', '', '', 'ceaaad', 'ceaaad', '', '', '', '', '', '', '', '', 'ceaaad', 'ceaaad', 'c', 'eaaad', 'eaaad', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', 'eaaad', 'eaaad', 'e', 'aaad', 'aaad', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', 'aaad', 'aaad', 'aaa', 'aaa', 'a', 'd', 'd', 'd', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '', '')]




import re
 
pattern = re.compile(r'python')
match = pattern.search('I love python')
 
if match:
    print('Matched')
else:
    print('Not Matched')