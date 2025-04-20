import glob
import json
import logging
import os
import random
import re
import sys
import time
from typing import List

import colorlog

from generator.Role import Role
from message.Lemma import Lemma
from message.Message import Message


def get_lemma_statement(lemma):
    while True:
        if "proof" in lemma:
           lemma = lemma[:lemma.find("proof")]
        elif "apply" in lemma:
            lemma = lemma[:lemma.find("apply")]
        elif "by" in lemma:
            lemma = lemma[:lemma.find("by")]
        else:
            return lemma


def split_lemmas(lemmas):
    lemmas_ = []
    for lemma in lemmas:
        lemma_count = lemma.count("lemma ")
        if lemma_count > 1:
            lemmas__ = lemma.strip().split("lemma ")
            for lemma__ in lemmas__:
                if lemma__.strip() != "":
                    lemmas_.append(get_lemma_statement("lemma " + lemma__))
        elif lemma_count == 1:
            lemmas_.append(get_lemma_statement(lemma))
        else:
            print("没有lemma关键字")
    return lemmas_

def match_function_defintion(message):
    definition_ = ""
    pattern = re.compile('```isabelle(.*?)```', flags=re.S)
    definitions = pattern.findall(message)
    for definition in definitions:
        definition_ = definition_ + definition + "\n"
    return definition_

def match_midlemmas(message, data_message:Message):
    if "" == message:
        return []
    name_lemmas = {}
    try:
        #pattern = re.compile('Code([0-9]*)\n```isabelle\n(.*?)\n```', flags=re.S)
        pattern = re.compile('```isabelle(.*?)```', flags=re.S)
        lemmas_ = pattern.findall(message)
        #lemmas = [lemma_[1] for lemma_ in lemmas_]
        print("----------new lemma--------------")
        print(lemmas_)

        print("----------处理后的lemma--------------")
        lemmas_ = split_lemmas(lemmas_)
        print(lemmas_)

        #theorem_specification = get_theorem_specification(data_message)
        #print("----------theorem_specification-------------")
        #print(theorem_specification)


        for lemma in lemmas_:
            lemma = lemma.strip()
            print("********************************************")
            if not lemma.startswith("lemma "):
                continue

            res = re.match('lemma (.*?)\"(.*?)\"', lemma, flags=re.S)
            if res is None:
                continue
            index = lemma.find(":")
            lemma_name = lemma[:index].replace("lemma ", "").strip()
            lemma_specification = lemma[index+1:].strip()

            #lemma_name = res.group(1).split(":")[0].strip()
            #lemma_specification = res.group(2).strip()
            print("----------lemma_specification-------------")
            print(lemma_specification)
            print("-----------lemma_name----------")
            print(lemma_name)
            print("___________theorem name___________")
            print(data_message.getData()["theorem name"])
            if lemma_name.strip() == data_message.getData()["theorem name"]:
                print("___________theorem name == lemma_name___________")
                continue
            theorem_specification = get_theorem_specification(data_message)
            print("----------theorem_specification-------------")
            print(theorem_specification)
            #print(data_message.getData()['theorem name'])

            if theorem_specification.replace(" ", "") == lemma_specification.replace(" ", ""):
                print("___________theorem specificatione == lemma_specification___________")
                continue
            name_lemmas[lemma_name.strip()] = lemma
    except Exception as e:
        print(e)
    return name_lemmas

def get_theorem_specification(data_message):
    specification = ""
    try:
        res = re.match('theorem (.*?)\"(.*?)\"', data_message.getData()["formal theorem statement"].strip(), flags=re.S)
        if res is None:
            res = re.match('lemma (.*?)\"(.*?)\"', data_message.getData()["formal theorem statement"].strip(), flags=re.S)
            if res is None:
                return ""
        specification = res.group(2).strip()
    except Exception as e:
        print(e)
    return specification

def jsonmerge(js1, js2):
    for midlemma_key, midlemma_value in js1.items():
        if midlemma_key not in js2:
            js2[midlemma_key] = midlemma_value
    return js2

def lemmas_obj(lemmas, stage):
    lemmas_obj = {}
    for lemma_key, lemma_value in lemmas.items():
        lemmas_obj[lemma_key] = Lemma(name=lemma_key, lemma_statement=lemma_value, stage=stage)
    return lemmas_obj

def list_lemmas_name(lemmas):
    list_lemmas = []
    for name, lemma in lemmas.items():
        list_lemmas.append(name)
    return list_lemmas

def delete_tactic(formal_sketch, key, sorry):
    mes = re.findall(key + r'(.*?)\n', formal_sketch, flags=re.S)
    # print(mes)
    mes_ = []
    for me in mes:
        if me.endswith("*)"):
            continue
        mes_.append(me)
    #print(mes_)
    for me_ in mes_:
        formal_sketch = formal_sketch.replace(key + me_, sorry, 1)
    #print(formal_sketch)
    return formal_sketch

def formal_sketch_format_match(formal_sketch):
    formal_sketch_ = delete_tactic(formal_sketch, "by", "sorry")
    formal_sketch__ = delete_tactic(formal_sketch_, "apply", "sorry")
    formal_sketch__ = formal_sketch__.replace("?case .", "?case sorry")
    formal_sketch__ = formal_sketch__.replace("?thesis .", "?thesis sorry")
    result = re.split(r'\n', formal_sketch__, flags=re.S)
    #print(result)
    formal = ""
    for res in result:
        if res.strip() == "proof":
            formal = formal + "proof -" + "\n"
        else:
            formal = formal + res + "\n"
    #print(formal)
    formal = formal.replace("sledgehammer", "sorry")

    """mes = re.findall("using" + r'(.*?)sorry', formal, flags=re.S)
    for me_ in mes:
        print(me_)
        formal = formal.replace("using" + me_, "", 1)"""

    return formal

if __name__ == "__main__":
    formal = """
    theorem min_priority_leq_all:
  assumes a1: "\<not> is_empty q"
    and a2: "v \<in> set |q|"
  shows "the (priority q (min q)) \<le> the (priority q v)"
proof -
  (* Step 3: Definition of by the min Function *)
  have h1: "min q = fst (hd (alist_of q))"
    by sfdsfsd
  (* Step 4: Priority of the Minimum Element *)
  have h2: "the (priority q (min q)) = the (map_of (alist_of q) (fst (hd (alist_of q))))"
    by sfdsfsd
  (* Step 5: Priority of Element v *)
  have h3: "the (priority q v) = the (map_of (alist_of q) v)"
    by sfdsfsd
  (* Step 7: Behavior of map_of *)
  have h4: "map_of (alist_of q) (fst (hd (alist_of q))) = Some (snd (hd (alist_of q)))"
    using distinct_alist_of hd_in_set list.set_map map_of_eq_None_iff option.distinct(1) in_set_values_imp_in_alist_of  by sfdsfsd
  (* Step 8: Sorted Property of the Queue *)
  have h5: "sorted (map snd (alist_of q))"
    using alist_of
    by auto 
  (* Step 9: Final Conclusion *)
  show ?thesis
    using h1 h2 h3 h4 h5 a1 a2 by sfdsfsd
qed
    """

    print(formal_sketch_format_match(formal))

def get_theory(data_message, formal, theory_name):
    if data_message.get_lemmas_theory_library() == "":
        theory = __get_theory(data_message, formal, theory_name)
    else:
        theory = __get_theory_library(data_message, formal, theory_name)
    return theory

def __get_theory(data_message, formal, theory_name):
    data = data_message.getData()
    theory = "theory " + theory_name + '\n     imports ' + data['packages'] + '\nbegin\n\n'


    theory = theory + data['other formal'] + "\n\n"
    for fun_name in data['function names']:
        theory = theory + data['formal function definitions'][fun_name] + "\n\n"

    # theory = theory + data['formal theorem statement'] + '\n' + formal + '\n\n'
    theory = theory + '\n' + formal + '\n\n'

    theory = theory + '\n\n\nend'
    return theory

def __get_theory_library(data_message, formal, theory_name):
    data = data_message.getData()
    theory = "theory " + theory_name + '\n     imports ' + data[
        'packages'] + " " + data_message.get_lemmas_package() + '\nbegin\n\n'

    theory = theory + '\n' + formal + '\n\n'

    if "context" in data and data["context"] != "":
        theory = theory + "end\n"
    theory = theory + '\n\n\nend'
    return theory


def get_theory_with_lemmas(data_message:Message, pre, key, post, verified_midlemmas=None, unverified_midlemmas=None):
    if data_message.get_lemmas_theory_library() == "":
        thy = __get_theory_with_lemmas(data_message, pre, key, post, verified_midlemmas, unverified_midlemmas)
    else:
        thy = __get_theory_with_lemmas_library(data_message, pre, key, post, unverified_midlemmas)
    return thy

def __get_theory_with_lemmas_library(data_message, pre, key, post,  unverified_midlemmas=None):
    data = data_message.getData()
    theory = "theory " + data['theorem name'] + '\n     imports ' + data['packages'] + " " + data_message.get_lemmas_package() + '\nbegin\n\n'

    for name, midlemma in unverified_midlemmas.items():
        theory = theory + midlemma.get_lemma_statement() + f" sorry\n\n"

    theory = theory + pre + key + post + '\n\n\n'


    theory = theory + '\n\n\nend'
    return theory

def __get_theory_with_lemmas(data_message, pre, key, post, verified_midlemmas=None, unverified_midlemmas=None):
    data = data_message.getData()
    theory = "theory " + data['theorem name'] + '\n     imports ' + data['packages'] + '\nbegin\n\n'



    theory = theory + data['other formal'] + "\n\n"

    for fun_name in data['function names']:
        theory = theory + data['formal function definitions'][fun_name] + "\n\n"

    #latest_midlemmas = data_message.latest_midlemmas()

    for name, midlemma in verified_midlemmas.items():
        if midlemma is not None:
            theory = theory + midlemma.get_lemma_statement()

    for name, midlemma in unverified_midlemmas.items():
        theory = theory + midlemma.get_lemma_statement() + f" sorry\n\n"

    theory = theory + pre + key + post + '\n\n\n'

    theory = theory + '\n\n\nend'
    return theory

def write_thy(theory_path: str, name: str, thy: str, mode='w'):
    """
    将thy写入文件
    :param theory_path:
    :param name:
    :param thy: 将thy写入文件
    :return:
    """
    print("----------------------")
    print(f'{theory_path}/{name}.thy')
    print("----------------------")
    file = None
    try:
        file = open(f'{theory_path}/{name}.thy', mode, encoding= 'utf-8')
        file.write(thy)
    except Exception as e:
        print(f'{theory_path}/{name}.thy---- {e}')
    finally:
        if file:
            file.flush()
            file.close()

def create_lemmas_theory_library(args, lemmas, checker):
    args.logger.info(f"create_lemmas_theory_library")
    if args.lemmas_theory_library != "":
        theory = "theory " + args.dataset + '\n     imports ' + "Main" + '\nbegin\n\n'
        definitons = args.formal_definfition[args.dataset]
        theory = theory + definitons + " "


        for id, lemma in lemmas.items():
            if lemma is not None:
                theory = theory + lemma.get_lemma_statement() +"\n\n"

        theory = theory + "\nend"
        print(theory)
        write_thy(args.lemmas_theory_library, args.dataset, theory)
        if not checker.check_theory(args.lemmas_theory_library, args.dataset):
            args.logger.warning(f"lemmas_theory_library 创建错误， 请检查错误")
            sys.exit()

def read_dir_(dir_path, suffix):
    contents = {}
    # dir_path = "../prompt/formalize/"
    for dir_name in glob.glob(os.path.join(dir_path, f'*{suffix}')):
        #self.logger.info(dir_name)
        filename = os.path.basename(dir_name)
        #self.logger.info("________")
        #self.logger.info(filename)
        filename_ = filename.split(".")[0]
        contents[filename_] = (open(dir_name, encoding='utf-8').read())
    #self.logger.info(contents)
    # self.logger.info(list(contents))

    print("Loaded %d contents" % len(contents))
    return contents


def config_formal_definition(args):
    if args.lemmas_theory_library != "":
        args.formal_definfition = {}
        formal_defintions = read_dir_(args.global_function_defintion_path, 'txt')
        print(formal_defintions)
        for key, formal_defintion in formal_defintions.items():
            print(key)
            print(match_function_defintion(formal_defintion))
            args.formal_definfition[key] = match_function_defintion(formal_defintion)

def is_sorry(formal):
    """
    判断formal中是否包含关键字sorry

    :param formal:
    :return:
    """

    offset = formal.find('sorry')
    if offset == -1:
        return False
    return True

def first_sorry_to_sledgehammer(formal):
    """
    将formal中第一个sorry替换为sledgehammer

    :param formal:
    :return:
    """
    offset = formal.find('sorry')
    pre = ''
    post = ''
    if offset != -1:
        end_offset = offset + len('sorry')
        pre = formal[:offset]
        post = formal[end_offset:]
    return pre, post


def format_lemmas_mess(lemmas):
    mess = ""
    for name, midlemma in lemmas.items():
        mess = mess + f"```isabelle\n{midlemma.get_lemma_statement()}\n```\n"

    return mess


def write_valid(data_message, true_proof_data_path, proof_state , formal, all_count=0):
    print(f"write_{proof_state}_lemma")
    print(true_proof_data_path)
    data = data_message.getData()
    theory = "theory " + data['theorem name'] + '\n     imports ' + data['packages'] + " "

    theory = theory + '\nbegin\n\n'

    if "context" in data and data["context"] != "":
        theory = theory + "context " + data["context"] + " begin\n"

    theory = theory + data['other formal'] + "\n\n"

    for fun_name in data['function names']:
        theory = theory + data['formal function definitions'][fun_name] + "\n\n"

    theory = theory + f"\n*********************** all_count={all_count} ***********************\n"

    theory = theory + formal

    if "context" in data and data["context"] != "":
        theory = theory + "end\n"

    theory = theory + '\n\n\nend'

    random_0_100 = random.randint(0, 100)
    path = f'{true_proof_data_path}/{proof_state + str(random_0_100) + "-" + data["theorem name"]}.thy'
    count = 0
    while os.path.exists(path):
        if count > 10:
            print("变量重复太多")
            break
        random_0_100 = random.randint(0, 100)
        path = f'{true_proof_data_path}/{proof_state + str(random_0_100) + "-" + data["theorem name"]}.thy'
        count = count + 1

    write_thy(true_proof_data_path, proof_state + str(random_0_100) + "-" + data["theorem name"], theory)

def final_key(formal, key):
    offset = formal.rfind(key)
    pre = ''
    post = ''
    if offset != -1:
        end_offset = offset + len(key)
        pre = formal[:offset]
        post = formal[end_offset:]
        # thy_ = pre + key2+ post
    return pre, post

"""def save_name(path: str, name: str, count1: int, count2: int):
    print("save_name")
    print(path)
    file = None
    try:
        file = open(f"{path}\\name.txt", 'a')
        file.write(f'{name} {count1} {count2}\n')
        print(f'+++++++++++++++++++++++++理论名"{name}"验证成功++++++++++++++++++++++++++++++')
    except Exception as e:
        print(f'{path}---- {e}')
    finally:
        if file:
            file.close()"""
def save_name(path: str, name: str, count1: int, count2: int, logger):
    print_logger("save_name",logger,"info")
    print_logger(path, logger, "info")
    file = None
    try:
        file = open(f"{path}\\name.txt", 'a')
        file.write(f'{name} {count1} {count2}\n')
        print_logger(f'+++++++++++++++++++++++++理论名"{name}"验证成功++++++++++++++++++++++++++++++',logger,"info")
    except Exception as e:
        print_logger(f'{path}---- {e}',logger,"info")
    finally:
        if file:
            file.close()

def print_logger(mess, logger, level):
    if logger is None:
        print(mess)
    else:
        if level == "info":
            logger.info(mess)
        elif level == "warning":
            logger.warning(mess)

def get_logger():
    # logging.basicConfig(stream=sys.stdout, level=logging.INFO, encoding='utf-8')
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)  # Log等级总开关
    log_colors_config = {
        "DEBUG": 'white',
        "INFO": 'black',
        "WARNING": 'yellow',
        "ERROR": 'bold_red',
        "CRITICAL": 'red'
    }
    # 第二步，创建一个handler，用于写入日志文件
    time1 = time.strftime('%Y-%m-%d-%H-%M-%S', time.localtime())
    logfile = '../log/log-' + time1 + '.txt'
    fh = logging.FileHandler(filename=logfile, mode='a', encoding='utf-8')  # open的打开模式这里可以进行参考
    fh.setLevel(logging.DEBUG)  # 输出到file的log等级的开关

    # 第三步，再创建一个handler，用于输出到控制台
    ch = logging.StreamHandler()
    ch.setLevel(logging.DEBUG)  # 输出到console的log等级的开关

    # 第四步，定义handler的输出格式
    # formatter = logging.Formatter("%(asctime)s - %(filename)s[line:%(lineno)d] - %(levelname)s: %(message)s")
    formatter = logging.Formatter("%(filename)s[line:%(lineno)d] - %(levelname)s: %(message)s")
    fh.setFormatter(formatter)
    ch.setFormatter(formatter)

    console_formatter = colorlog.ColoredFormatter(
        fmt='%(log_color)s[%(asctime)s.%(msecs)03d] %(filename)s -> %(funcName)s line:%(lineno)d [%(levelname)s : %(message)s',
        datefmt='%Y-%m-%d %H:%m:%S',
        log_colors=log_colors_config
    )
    ch.setFormatter(console_formatter)
    # 第五步，将logger添加到handler里面
    logger.addHandler(fh)
    logger.addHandler(ch)
    return logger

def read_name(path: str):
    file = None
    names = []
    try:
        file = open(f"{path}\\name.txt", 'r')
        names_ = file.read().split('\n')
        while names_[len(names_) - 1] == "":
            names_ = names_[:len(names_) - 1]
        for name in names_:
            names.append(name.split(" ")[0])
    except Exception as e:
        print(f'{path}---- {e}')
    finally:
        if file:
            file.close()
        return names

def read_dir(dir_path: str, suffix: str) -> List:
    """
    :param args:
    :param dir_path:  ./data/informal/test1/
    :return:
    """
    if not os.path.isdir(dir_path):
        return []
    contents = []
    print(dir_path)
    if suffix == 'json':
        for dir_name in glob.glob(os.path.join(dir_path, f'*.{suffix}')):
            contents.append(json.loads(open(dir_name,encoding='utf-8').read()))
    else:
        for dir_name in glob.glob(os.path.join(dir_path, f'*.{suffix}')):
            contents.append(open(dir_name).read())
    print("Loaded %d contents" % len(contents))
    return contents

def format_rules(rules, user_rules_type):
    text = ""
    for rule_name, rule in rules.items():
        text = text + rule_name + " : " + rule + "\n"

    for rule_name, rule in user_rules_type.items():
        text = text + rule_name + " : " + rule + "\n"

    return text

def metadata_template_problem(metadata_class, metadata_theorem, id):
    return {"class": metadata_class, "theorem": metadata_theorem, "id":id}

def metadata_template(metadata_class, metadata_theorem, stage:Role):
    return {"class": metadata_class, "theorem": metadata_theorem, "stage":stage.name.lower()}

def metadata_template_proof(metadata_class, metadata_theorem, proof, stage:Role, index):
    return {"class": metadata_class, "theorem": metadata_theorem, "proof":proof, "stage":stage.name.lower(), "index":index}

def return_stage_role(stage:str):

    if stage == Role.INDIRECT_LEMMA:
        return Role.INDIRECT_LEMMA
    elif stage == Role.DIRECT_LEMMA:
        return Role.DIRECT_LEMMA
    elif stage == Role.REFLECTION_LEMMA:
        return Role.REFLECTION_LEMMA
    elif stage == Role.SUBGOAL_LEMMA:
        return Role.SUBGOAL_LEMMA
    else:
        return Role.NONE

def theorem_to_lemma(theorem:str):
    theorem = theorem.strip()
    if theorem.startswith("theorem "):
        lemma = theorem.replace("theorem ", "lemma ", 1)
    else:
        print("定理关键词错误")
        lemma = theorem
    return lemma

def lemma_to_theorem(lemma:str):
    lemma = lemma.strip()
    if lemma.startswith("lemma "):
        theorem = lemma.replace("lemma ", "theorem ", 1)
    else:
        print("引理关键词错误")
        theorem = lemma
    return theorem


if __name__ == '__main__':
    formal = """theorem bounded_stack_pop_push_inverse:
  assumes a1: "\<not> isempty s" and a2: "(v, s0) = pop s"
  shows "push (the v) s0 = s"
proof (cases "isfull s")
  case True
  then have "push (the v) s0 = push (the v) s"
    by (auto simp add: push_def isfull_def)
  also have "... = s"
    using True a2 by (auto simp add: push_def pop_def)
  finally show ?thesis .
next
  case False
  then have "push (the v) s0 = push (the v) (pop s)"
    by (auto simp add: push_def False)
  also have "... = s"
    using False a2 by (auto simp add: push_def pop_def)
  finally show ?thesis .
qed
"""

    print(formal_sketch_format_match(formal))






def read_thy(theory_path: str, name: str) -> str:
    """
    读取theory，返回string
    :param theory_path:
    :param name:
    :return:
    """
    thy = ""
    file = None
    try:
        file = open(f'{theory_path}/{name}.thy', 'r', encoding= 'utf-8')
        thy = file.read()
    except Exception as e:
        print(f'{theory_path}/{name}.thy---- {e}')
    finally:
        if file:
            file.close()
        return thy



def save_true_theory(true_proof_data_path, theory_path, name):
    thy = read_thy(theory_path, name)
    write_thy(true_proof_data_path, name, thy)

def save_false_theory(path, thy, name, time):
    print("----------------------")
    print(f'{path}/{name}-{time}.txt')
    print("----------------------")
    file = None
    try:
        file = open(f'{path}/{name}-{time}.txt', 'a', encoding='utf-8')
        file.write(f'{thy}\n##############################################\n')
    except Exception as e:
        print(f'{path}/{name}-{time}.txt---- {e}')
    finally:
        if file:
            file.flush()
            file.close()
    print()









def json_to_string(js):
    st = f"--len = {len(js)}--\n"
    for key, value in js.items():
        st = st + key + f":\n{value}\n"
    return st

def list_to_string(lst):
    st = f"--len = {len(lst)}--\n"
    for value in lst:
        st = st + f"{value}\n"
    return st


def diffmidemmas(old_valid_midlemmas, new_valid_midlemmas):
    diffmidlemmas = {}
    for key, value in new_valid_midlemmas.items():
        if key not in old_valid_midlemmas:
            diffmidlemmas[key] = value
    return diffmidlemmas





def used_midlemmas(midlemmas, formal):
    used_midlemmas = {}
    for midlemma_key, midlemma_value in midlemmas.items():
        if midlemma_key in formal:
            used_midlemmas[midlemma_key] = midlemma_value
    return used_midlemmas





def match_formal(formal):
    res = re.match(r'(.*?)```isabelle(.*?)```', formal, flags=re.S)
    if res:
        return res.group(2)
    return ""


def first_placeholder_split(formal, placeholder):
    """
    将formal中第一个sorry替换为sledgehammer

    :param formal:
    :return:
    """
    offset = formal.find(placeholder)
    pre = ''
    post = ''
    if offset != -1:
        end_offset = offset + len(placeholder)
        pre = formal[:offset]
        post = formal[end_offset:]
    return pre, post






"""def valid_midlemmas_check_syntax_nitpick(data, midlemmas, verifier, args, logger):
    useful_midlemmas = {}
    for name, midlemma in midlemmas.items():
        theory = "theory " + name + '\n     imports ' + data['packages'] + '\nbegin\n\n' \
                    '' + data['other formal'] + "\n\n"
        for fun_name in data['function names']:
            theory = theory + data['formal function definitions'][fun_name] + "\n\n"

        theory = theory + midlemma  + " nitpick sorry " + '\n\n\nend'
        print(theory)
        write_thy(args.theory_path, name, theory)
        isture, mess = verifier.run_nitpick_check_syntax_all_subgoal(args.theory_path, name)
        if isture:
            logger.info("\n no nitpick_check_syntax")
            useful_midlemmas[name] = midlemma
        else:
            logger.info(mess)
    return useful_midlemmas
"""

def final_key1_to_key2(thy, key1, key2):
    """
    将thy中最后一个key1替换为key2

    :return:
    """
    offset = thy.rfind(key1)
    pre = ''
    post = ''
    if offset != -1:
        end_offset = offset + len(key1)
        pre = thy[:offset]
        post = thy[end_offset:]
        thy_ = pre + key2+ post
        return thy_

    return ""






def get_line(thy, str):
    """
    获取str所在行
    :param thy:
    :param str:
    :return:
    """
    lines = thy.split('\n')
    for count, line in enumerate(lines):
        count = count + 1
        if str in line:
            return count
    return -1

def merge_dict(dict1, dict2):
    for key, value in dict2.items():
        if key in dict1:
            continue
        else:
            dict1[key] = value
    return dict1



def jsonmerge2(js1, js2):
    js3 = {}
    for key, value in js2.items():
        js3[key] = value
    for midlemma_key, midlemma_value in js1.items():
        if midlemma_key not in js3 and midlemma_value not in js3.values():
            js3[midlemma_key] = midlemma_value
    return js3

def key_split_string(string, key):
    """
    :param string:
    :param key:
    :return: 用string中最后一个key，分隔string
    """
    offset = string.rfind(key)
    if offset != -1:
        end_offset = offset
        pre = string[:offset]
        post = string[end_offset:]
        return pre, post
    return "", ""






