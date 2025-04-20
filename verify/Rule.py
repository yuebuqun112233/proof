import json
import os
import re

from utils import write_thy

path = '../output/without_newlemma/rule_message'
if not os.path.isdir(path):
    os.mkdir(path)

def template(name):
    return "ML\\<open>\nwriteln \"<name>" + name + "</name>\"\n\\<close>\n" + "code_thms " + name + "\n\n"

def user_template(name, suffix):
    return "ML\\<open>\nwriteln \"<user defined name>" + name + suffix + "</user defined name>\"\n\\<close>\n" + "thm " + name + suffix + "\n\n"

def user_template2(name, suffix):
    return "ML\\<open>\nwriteln \"<user defined name type>" + name + suffix + "</user defined name type>\"\n\\<close>\n" + "thm " + name + suffix + "\n\n"

def match_name(message):
    result = re.match(r'<name>(.*?)</name>', message)
    if result is None:
        return False,""
    #print("<name>")
    #print(result.group(1))
    #print("/name")
    return True, result.group(1)

def match_user_name(message):
    result = re.match(r'<user defined name>(.*?)</user defined name>', message)
    if result is None:
        return False, ""
    #print("<user defined name>")
    #print(result.group(1))
    #print("/user defined name")
    return True, result.group(1)

def match_user_name2(message):
    result = re.match(r'<user defined name type>(.*?)</user defined name type>', message)
    if result is None:
        return False, ""
    #print("<user defined name>")
    #print(result.group(1))
    #print("/user defined name")
    return True, result.group(1)

def data_to_thy_decomposition(data, path):
    thy = "theory " + data["theorem name"] + "\n     imports " + data["packages"] + "\nbegin\n"
    if "context" in data and data["context"] != "":
        thy = thy + "context " + data["context"] + "\nbegin\n"

    thy = thy + data['other formal'] + "\n\n"
    fun_names = data["function names"]
    for fun_name in fun_names:
        thy = thy + data["formal function definitions"][fun_name] +"\n"
        if 'definition ' in data["formal function definitions"][fun_name]:
            thy = thy + template(fun_name)
        elif 'fun ' in data["formal function definitions"][fun_name] or 'function ' in data["formal function definitions"][fun_name] or 'primrec ' in data["formal function definitions"][fun_name]:
            thy = thy + template(fun_name)
    if "context" in data and data["context"] != "":
        thy = thy + "end\n"
    thy = thy + 'end'
    print(thy)
    write_thy(path, data["theorem name"], thy)


def data_to_thy_decomposition_user(data, path):
    thy = "theory " + data["theorem name"] + "\n     imports " + data["packages"] + "\nbegin\n"
    if "context" in data and data["context"] != "":
        thy = thy + "context " + data["context"] + "\nbegin\n"

    thy = thy + data['other formal'] + "\n\n"
    fun_names = data["function names"]
    for fun_name in fun_names:
        thy = thy + data["formal function definitions"][fun_name] +"\n"
        if 'definition ' in data["formal function definitions"][fun_name]:
            thy = thy + user_template(fun_name, "_def")
        elif 'fun ' in data["formal function definitions"][fun_name] or 'function ' in data["formal function definitions"][fun_name] or 'primrec ' in data["formal function definitions"][fun_name]:
            thy = thy + user_template(fun_name, ".simps")
    for rule_name in data["type constraint rules"]:
        thy = thy + user_template2(rule_name, "")
    if "context" in data and data["context"] != "":
        thy = thy + "end\n"
    thy = thy + 'end'
    print(thy)
    write_thy(path, data["theorem name"], thy)

def data_to_thy_decomposition_all(data, path):
    thy = "theory " + data["theorem name"] + "\n     imports " + data["packages"] + "\nbegin\n"
    if "context" in data and data["context"] != "":
        thy = thy + "context " + data["context"] + "\nbegin\n"

    thy = thy + data['other formal'] + "\n\n"
    fun_names = data["function names"]
    for fun_name in fun_names:
        thy = thy + data["formal function definitions"][fun_name] +"\n"
        if 'definition ' in data["formal function definitions"][fun_name]:
            thy = thy + template(fun_name)
            thy = thy + user_template(fun_name, "_def")
        elif 'fun ' in data["formal function definitions"][fun_name] or 'function ' in data["formal function definitions"][fun_name] or 'primrec ' in data["formal function definitions"][fun_name]:
            thy = thy + template(fun_name)
            thy = thy + user_template(fun_name, ".simps")
    if "type constraint rules" in data:
        for rule_name in data["type constraint rules"]:
            thy = thy + user_template2(rule_name, "")

    if "other rules" in data:
        for rule_name in data["other rules"]:
            thy = thy + user_template2(rule_name, "")

    if "context" in data and data["context"] != "":
        thy = thy + "end\n"
    thy = thy + 'end'
    print(thy)
    write_thy(path, data["theorem name"], thy)

def rules_form_message(message):
    rules = {}
    results = message.split("\n")
    length = len(results)
    i = 0
    while i < length:

        if not results[i].startswith("  "):
            name = results[i]
            i = i + 1
            rule = ""
            while i < length and results[i].startswith("  "):
                rule = rule + results[i]
                i = i + 1
            rules[name] = rule
    return rules

def get_decompsition_rules(responses):
    """

    decompsition_rules: == {
                               func_name1: {rule_name1 : rule1, rule_name2 : rule2, ...},
                               func_name2: {}
                                ....

                            }
    例子：
    {
        'push': {'push': '  push ?v ?s \\<equiv> ?v # ?s'},
        'pop': {'pop': '  pop (?x # ?xs) \\<equiv> (?x, ?xs)'},
        'top': {'hd': '  hd (?x21.0 # ?x22.0) \\<equiv> ?x21.0', 'pop_push.top': '  pop_push.top ?s \\<equiv> hd ?s'},
        'emp': {'List.null': '  List.null [] \\<equiv> True  List.null (?x # ?xs) \\<equiv> False', 'emp': '  emp ?s \\<equiv> List.null ?s'},
        'test': {'If': '  if False then ?x else ?y \\<equiv> ?y  if True then ?x else ?y \\<equiv> ?x', 'Let': '  Let ?s ?f \\<equiv> ?f ?s', 'less [nat]': '  ?m < Suc ?n \\<equiv> ?m \\<le> ?n  ?n < 0 \\<equiv> False', 'less_eq [nat]': '  Suc ?m \\<le> ?n \\<equiv> ?m < ?n  0 \\<le> ?n \\<equiv> True', 'nat_of_num': '  nat_of_num (num.Bit1 ?n) \\<equiv> let m = nat_of_num ?n in Suc (m + m)  nat_of_num (num.Bit0 ?n) \\<equiv> let m = nat_of_num ?n in m + m  nat_of_num num.One \\<equiv> 1', 'one_class.one [nat]': '  1 \\<equiv> Suc 0', 'plus [nat]': '  Suc ?m + ?n \\<equiv> ?m + Suc ?n  0 + ?n \\<equiv> ?n', 'test': '  test 0 \\<equiv> 0  test (Suc ?v) \\<equiv>  if nat_of_num      (num.Bit0        (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 (num.Bit1 num.One))))))     < Suc ?v  then if Suc ?v          < nat_of_num             (num.Bit0               (num.Bit1                 (num.Bit1                   (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))       then if nat_of_num                (num.Bit0                  (num.Bit1                    (num.Bit1                      (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))               < Suc ?v            then nat_of_num (num.Bit0 num.One)            else nat_of_num (num.Bit0 (num.Bit0 num.One))       else if Suc ?v               < nat_of_num                  (num.Bit0                    (num.Bit1                      (num.Bit1                        (num.Bit0                          (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))            then if Suc ?v                    < nat_of_num                       (num.Bit0                         (num.Bit1                           (num.Bit1                             (num.Bit0                               (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))                 then nat_of_num (num.Bit0 num.One)                 else if Suc ?v                         < nat_of_num                            (num.Bit0                              (num.Bit1                                (num.Bit1                                  (num.Bit0                                    (num.Bit1', '(num.Bit0 (num.Bit0 num.One)))))))': '                      then nat_of_num (num.Bit0 num.One)                      else nat_of_num (num.Bit0 (num.Bit0 num.One))                 else nat_of_num (num.Bit0 (num.Bit0 num.One))            else if Suc ?v                    < nat_of_num                       (num.Bit0                         (num.Bit1                           (num.Bit1                             (num.Bit0                               (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))                 then nat_of_num (num.Bit0 num.One)                 else nat_of_num (num.Bit0 (num.Bit0 num.One))'}}

    :param responses:
    :return:
    """
    pass
    decompsition_rules = {}
    response_type = responses[-1].response_type
    if response_type != 'FINISHED':
        return None
    messages = json.loads(responses[-1].response_body)["nodes"][-1]["messages"]
    length = len(messages)
    i = 0
    while i < length:
        ismatch, name = match_name(messages[i]["message"])
        if ismatch:
            i = i + 2
            message_ = messages[i]["message"]
            decompsition_rules[name] = rules_form_message(message_)
        i = i + 1
    return decompsition_rules


def get_decompsition_user_rules(responses):
    """

    decompsition_rules: == {
                               func_name1: {rule_name1 : rule1, rule_name2 : rule2, ...},
                               func_name2: {}
                                ....

                            }
    例子：
    {
        'push': {'push': '  push ?v ?s \\<equiv> ?v # ?s'},
        'pop': {'pop': '  pop (?x # ?xs) \\<equiv> (?x, ?xs)'},
        'top': {'hd': '  hd (?x21.0 # ?x22.0) \\<equiv> ?x21.0', 'pop_push.top': '  pop_push.top ?s \\<equiv> hd ?s'},
        'emp': {'List.null': '  List.null [] \\<equiv> True  List.null (?x # ?xs) \\<equiv> False', 'emp': '  emp ?s \\<equiv> List.null ?s'},
        'test': {'If': '  if False then ?x else ?y \\<equiv> ?y  if True then ?x else ?y \\<equiv> ?x', 'Let': '  Let ?s ?f \\<equiv> ?f ?s', 'less [nat]': '  ?m < Suc ?n \\<equiv> ?m \\<le> ?n  ?n < 0 \\<equiv> False', 'less_eq [nat]': '  Suc ?m \\<le> ?n \\<equiv> ?m < ?n  0 \\<le> ?n \\<equiv> True', 'nat_of_num': '  nat_of_num (num.Bit1 ?n) \\<equiv> let m = nat_of_num ?n in Suc (m + m)  nat_of_num (num.Bit0 ?n) \\<equiv> let m = nat_of_num ?n in m + m  nat_of_num num.One \\<equiv> 1', 'one_class.one [nat]': '  1 \\<equiv> Suc 0', 'plus [nat]': '  Suc ?m + ?n \\<equiv> ?m + Suc ?n  0 + ?n \\<equiv> ?n', 'test': '  test 0 \\<equiv> 0  test (Suc ?v) \\<equiv>  if nat_of_num      (num.Bit0        (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 (num.Bit1 num.One))))))     < Suc ?v  then if Suc ?v          < nat_of_num             (num.Bit0               (num.Bit1                 (num.Bit1                   (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))       then if nat_of_num                (num.Bit0                  (num.Bit1                    (num.Bit1                      (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))               < Suc ?v            then nat_of_num (num.Bit0 num.One)            else nat_of_num (num.Bit0 (num.Bit0 num.One))       else if Suc ?v               < nat_of_num                  (num.Bit0                    (num.Bit1                      (num.Bit1                        (num.Bit0                          (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))            then if Suc ?v                    < nat_of_num                       (num.Bit0                         (num.Bit1                           (num.Bit1                             (num.Bit0                               (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))                 then nat_of_num (num.Bit0 num.One)                 else if Suc ?v                         < nat_of_num                            (num.Bit0                              (num.Bit1                                (num.Bit1                                  (num.Bit0                                    (num.Bit1', '(num.Bit0 (num.Bit0 num.One)))))))': '                      then nat_of_num (num.Bit0 num.One)                      else nat_of_num (num.Bit0 (num.Bit0 num.One))                 else nat_of_num (num.Bit0 (num.Bit0 num.One))            else if Suc ?v                    < nat_of_num                       (num.Bit0                         (num.Bit1                           (num.Bit1                             (num.Bit0                               (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))                 then nat_of_num (num.Bit0 num.One)                 else nat_of_num (num.Bit0 (num.Bit0 num.One))'}}

    :param responses:
    :return:
    """
    decompsition_user_rules = {}
    response_type = responses[-1].response_type
    if response_type != 'FINISHED':
        return None
    messages = json.loads(responses[-1].response_body)["nodes"][-1]["messages"]
    length = len(messages)
    i = 0
    while i < length:
        ismatch, name = match_user_name(messages[i]["message"])
        if ismatch:
            i = i + 2
            message_ = messages[i]["message"]
            decompsition_user_rules[name] = message_
        i = i + 1
    return decompsition_user_rules

def get_decompsition_all_rules(responses):
    """

    decompsition_rules: == {
                               func_name1: {rule_name1 : rule1, rule_name2 : rule2, ...},
                               func_name2: {}
                                ....

                            }
    例子：
    {
        'push': {'push': '  push ?v ?s \\<equiv> ?v # ?s'},
        'pop': {'pop': '  pop (?x # ?xs) \\<equiv> (?x, ?xs)'},
        'top': {'hd': '  hd (?x21.0 # ?x22.0) \\<equiv> ?x21.0', 'pop_push.top': '  pop_push.top ?s \\<equiv> hd ?s'},
        'emp': {'List.null': '  List.null [] \\<equiv> True  List.null (?x # ?xs) \\<equiv> False', 'emp': '  emp ?s \\<equiv> List.null ?s'},
        'test': {'If': '  if False then ?x else ?y \\<equiv> ?y  if True then ?x else ?y \\<equiv> ?x', 'Let': '  Let ?s ?f \\<equiv> ?f ?s', 'less [nat]': '  ?m < Suc ?n \\<equiv> ?m \\<le> ?n  ?n < 0 \\<equiv> False', 'less_eq [nat]': '  Suc ?m \\<le> ?n \\<equiv> ?m < ?n  0 \\<le> ?n \\<equiv> True', 'nat_of_num': '  nat_of_num (num.Bit1 ?n) \\<equiv> let m = nat_of_num ?n in Suc (m + m)  nat_of_num (num.Bit0 ?n) \\<equiv> let m = nat_of_num ?n in m + m  nat_of_num num.One \\<equiv> 1', 'one_class.one [nat]': '  1 \\<equiv> Suc 0', 'plus [nat]': '  Suc ?m + ?n \\<equiv> ?m + Suc ?n  0 + ?n \\<equiv> ?n', 'test': '  test 0 \\<equiv> 0  test (Suc ?v) \\<equiv>  if nat_of_num      (num.Bit0        (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 (num.Bit1 num.One))))))     < Suc ?v  then if Suc ?v          < nat_of_num             (num.Bit0               (num.Bit1                 (num.Bit1                   (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))       then if nat_of_num                (num.Bit0                  (num.Bit1                    (num.Bit1                      (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))               < Suc ?v            then nat_of_num (num.Bit0 num.One)            else nat_of_num (num.Bit0 (num.Bit0 num.One))       else if Suc ?v               < nat_of_num                  (num.Bit0                    (num.Bit1                      (num.Bit1                        (num.Bit0                          (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))            then if Suc ?v                    < nat_of_num                       (num.Bit0                         (num.Bit1                           (num.Bit1                             (num.Bit0                               (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))                 then nat_of_num (num.Bit0 num.One)                 else if Suc ?v                         < nat_of_num                            (num.Bit0                              (num.Bit1                                (num.Bit1                                  (num.Bit0                                    (num.Bit1', '(num.Bit0 (num.Bit0 num.One)))))))': '                      then nat_of_num (num.Bit0 num.One)                      else nat_of_num (num.Bit0 (num.Bit0 num.One))                 else nat_of_num (num.Bit0 (num.Bit0 num.One))            else if Suc ?v                    < nat_of_num                       (num.Bit0                         (num.Bit1                           (num.Bit1                             (num.Bit0                               (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))                 then nat_of_num (num.Bit0 num.One)                 else nat_of_num (num.Bit0 (num.Bit0 num.One))'}}

    :param responses:
    :return:
    """
    decompsition_rules = {}
    decompsition_user_rules = {}
    decompsition_user_rules_type = {}
    response_type = responses[-1].response_type
    if response_type != 'FINISHED':
        return {} , {}, {}
    messages = json.loads(responses[-1].response_body)["nodes"][-1]["messages"]
    length = len(messages)
    i = 0
    while i < length:
        ismatch_user, name_user = match_user_name(messages[i]["message"])
        ismatch, name = match_name(messages[i]["message"])
        ismatch_user_tpye, name_type = match_user_name2(messages[i]["message"])
        if ismatch_user:
            i = i + 2
            message_ = messages[i]["message"]
            decompsition_user_rules[name_user] = message_

        if ismatch:
            i = i + 2
            message_ = messages[i]["message"]
            decompsition_rules[name] = rules_form_message(message_)

        if ismatch_user_tpye:
            i = i + 2
            message_ = messages[i]["message"]
            decompsition_user_rules_type[name_type] = message_

        i = i + 1
    return decompsition_rules, decompsition_user_rules, decompsition_user_rules_type

class Rule:
    def __init__(self, isabelle):
        self.isabelle = isabelle

    def decomposition_rule(self, data):
        """

        :param data:
        :return:

        {
           func_name1: {rule_name1 : rule1, rule_name2 : rule2, ...},
           func_name2: {}
            ....

        }
    例子：
        {
            'push': {'push': '  push ?v ?s \\<equiv> ?v # ?s'},
            'pop': {'pop': '  pop (?x # ?xs) \\<equiv> (?x, ?xs)'},
            'top': {'hd': '  hd (?x21.0 # ?x22.0) \\<equiv> ?x21.0', 'pop_push.top': '  pop_push.top ?s \\<equiv> hd ?s'},
            'emp': {'List.null': '  List.null [] \\<equiv> True  List.null (?x # ?xs) \\<equiv> False', 'emp': '  emp ?s \\<equiv> List.null ?s'},
            'test': {'If': '  if False then ?x else ?y \\<equiv> ?y  if True then ?x else ?y \\<equiv> ?x', 'Let': '  Let ?s ?f \\<equiv> ?f ?s', 'less [nat]': '  ?m < Suc ?n \\<equiv> ?m \\<le> ?n  ?n < 0 \\<equiv> False', 'less_eq [nat]': '  Suc ?m \\<le> ?n \\<equiv> ?m < ?n  0 \\<le> ?n \\<equiv> True', 'nat_of_num': '  nat_of_num (num.Bit1 ?n) \\<equiv> let m = nat_of_num ?n in Suc (m + m)  nat_of_num (num.Bit0 ?n) \\<equiv> let m = nat_of_num ?n in m + m  nat_of_num num.One \\<equiv> 1', 'one_class.one [nat]': '  1 \\<equiv> Suc 0', 'plus [nat]': '  Suc ?m + ?n \\<equiv> ?m + Suc ?n  0 + ?n \\<equiv> ?n', 'test': '  test 0 \\<equiv> 0  test (Suc ?v) \\<equiv>  if nat_of_num      (num.Bit0        (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 (num.Bit1 num.One))))))     < Suc ?v  then if Suc ?v          < nat_of_num             (num.Bit0               (num.Bit1                 (num.Bit1                   (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))       then if nat_of_num                (num.Bit0                  (num.Bit1                    (num.Bit1                      (num.Bit0 (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))               < Suc ?v            then nat_of_num (num.Bit0 num.One)            else nat_of_num (num.Bit0 (num.Bit0 num.One))       else if Suc ?v               < nat_of_num                  (num.Bit0                    (num.Bit1                      (num.Bit1                        (num.Bit0                          (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))            then if Suc ?v                    < nat_of_num                       (num.Bit0                         (num.Bit1                           (num.Bit1                             (num.Bit0                               (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))                 then nat_of_num (num.Bit0 num.One)                 else if Suc ?v                         < nat_of_num                            (num.Bit0                              (num.Bit1                                (num.Bit1                                  (num.Bit0                                    (num.Bit1', '(num.Bit0 (num.Bit0 num.One)))))))': '                      then nat_of_num (num.Bit0 num.One)                      else nat_of_num (num.Bit0 (num.Bit0 num.One))                 else nat_of_num (num.Bit0 (num.Bit0 num.One))            else if Suc ?v                    < nat_of_num                       (num.Bit0                         (num.Bit1                           (num.Bit1                             (num.Bit0                               (num.Bit1 (num.Bit0 (num.Bit0 num.One)))))))                 then nat_of_num (num.Bit0 num.One)                 else nat_of_num (num.Bit0 (num.Bit0 num.One))'}
        }
        """
        data_to_thy_decomposition(data, path)
        responses = self.isabelle.get_responses(path, data["theorem name"])
        print(responses)
        if responses is None:
            return None
        decomposition_rules = get_decompsition_rules(responses)
        return decomposition_rules

    def decomposition_rules_deduplication(self, data):
        """
        rules deduplication
        {
            rule_name1 : rule1,
            rule_name2 : rule2,
            ...
        }
    例子：
        {
            'push': '  push ?v ?s \\<equiv> ?v # ?s',
            ''pop': '  pop (?x # ?xs) \\<equiv> (?x, ?xs)',
            ''hd': '  hd (?x21.0 # ?x22.0) \\<equiv> ?x21.0',
            'pop_push.top': '  pop_push.top ?s \\<equiv> hd ?s',
             ....
       }
        :param data:
        :return:
        """
        decomposition_rules = self.decomposition_rule(data)
        decomposition_rules_deduplication = {}
        for func_name, rules in decomposition_rules.items():
            for rule_name, rule in rules.items():
                if rule not in decomposition_rules_deduplication:
                    decomposition_rules_deduplication[rule_name] = rule
        return decomposition_rules_deduplication

    def uer_defined_rules(self, data):
        """
        capacity_def : capacity ?s ≡ snd (alist_of ?s)

        size_def : bounded_stack_push_top.size ?s ≡ length (fst (alist_of ?s))

        isfull_def : isfull ?s ≡ bounded_stack_push_top.size ?s = capacity ?s

        isempty_def : isempty ?s ≡ fst (alist_of ?s) = []

        top_def : bounded_stack_push_top.top ?s ≡ if ¬ isempty ?s then Some (hd (fst (alist_of ?s))) else None

        push_def : push ?v ?s ≡ if ¬ isfull ?s then Abs_bstack (?v # fst (alist_of ?s), snd (alist_of ?s)) else ?s

        :param data:
        :return:
        """
        data_to_thy_decomposition_user(data, path)
        responses = self.isabelle.get_responses(path, data["theorem name"])
        print(responses)
        if responses is None:
            return None
        decomposition_user_rules = get_decompsition_user_rules(responses)
        return decomposition_user_rules

    def all_rules(self, data):
        data_to_thy_decomposition_all(data, path)
        responses = self.isabelle.get_responses(path, data["theorem name"])
        print(responses)
        if responses is None or responses == "isabelle_Timeout":
            return {}, {}, {}
        decomposition_rules, decomposition_user_rules, decompsition_user_rules_type = get_decompsition_all_rules(responses)
        decomposition_rules_deduplication = {}
        for func_name, rules in decomposition_rules.items():
            for rule_name, rule in rules.items():
                if rule not in decomposition_rules_deduplication:
                    decomposition_rules_deduplication[rule_name] = rule

        return decomposition_rules_deduplication, decomposition_user_rules, decompsition_user_rules_type
