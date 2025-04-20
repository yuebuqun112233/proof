import copy
import json
import re
import sys
from typing import List

import nest_asyncio
from func_timeout import FunctionTimedOut
from isabelle_client import start_isabelle_server, get_isabelle_client, IsabelleResponse, IsabelleClient
from isabelle_client.isabelle_Timeout import isabelle_Timeout

import utils
from message.Isabelle_response_message import Isabelle_response_message
from message.Message import Message
from utils import write_thy, read_thy, save_false_theory,  print_logger, get_theory_with_lemmas


def finally_sorry_to_sledgehammer(theory_path: str, name: str):
    """
    将thy中最后一个sorry替换为sledgehammer
    :param theory_path:
    :param name:
    :return:
    """
    thy = read_thy(theory_path, name)
    offset = thy.rfind('sorry')
    pre = ''
    post = ''
    if offset != -1:
        end_offset = offset + len('sorry')
        pre = thy[:offset]
        post = thy[end_offset:]
        thy = pre + 'sledgehammer' + post
        write_thy(theory_path, name, thy)
    return pre, post





class Isabelle:

    def __init__(self, logger=None):
        self.isabelle_prover= Isabelle._prover()
        self.session_id = self.isabelle_prover.session_start()
        self.__logger = logger
        self.__isabelle_response_message = Isabelle_response_message()

    def get_isabelle_response_message(self):
        return self.__isabelle_response_message

    def init_isabelle_response_message(self):
        isabelle_responses_message = self.get_isabelle_response_message()
        isabelle_responses_message.init()

    def get_logger(self):
        return self.__logger

    def set_logger(self, logger):
        self.__logger = logger

    def session_stop(self, session_id):
        self.isabelle_prover.session_stop(session_id)

    @staticmethod
    def _prover():
        """
            start Isabelle server
            :rtype: object
            :return: 返回isabelle对象，类型为IsabelleClient
            """
        isabelle = None
        nest_asyncio.apply()
        try:
            server_info, _ = start_isabelle_server()
            print(f'server_info = {server_info}')
            isabelle = get_isabelle_client(server_info)
        except Exception as e:
            print(e)

        return isabelle

    # @func_set_timeout(300) #5分钟
    def get_responses(self, theory_path, name):
        """
        func_set_timeout(300) get_responses最长运行5分钟
        :param theory_path: thy文件所在路径
        :param name: thy名字
        :return: 返回isabelle的相应信息
        """
        responses = None

        # args.logger.info(os.path.abspath('.'))
        # init_name = name[:len(name) - 3]
        # rename1(theory_path, name, init_name)
        print_logger( f"session id = {self.session_id}", self.get_logger(), "info")
        try:
            responses = self.isabelle_prover.use_theories(
                theories=[name], master_dir=theory_path, watchdog_timeout=0,session_id=self.session_id
            )
            print_logger(responses, self.get_logger(), "info")
        except isabelle_Timeout as timeout:
            print_logger(timeout, self.get_logger(), "warning")
            responses = "isabelle_Timeout"
            return responses
        if responses != None and responses[-1].response_type == "FAILED":
            return None
        return responses


    def nitpick_check_syntax_all_subgoal(self, theory_path, name):
        self.init_isabelle_response_message()
        isabelle_response_message = self.get_isabelle_response_message()
        self.get_logger().info("----------------------------------开始 nitpick_check_syntax_all_subgoal-------------------------------------------")
        responses = None

        try:
            responses = self.get_responses(theory_path, name)
        except FunctionTimedOut as e:
            self.get_logger().warning(e)
        finally:
            self.get_logger().info(responses)
            if responses is None:
                isabelle_response_message.set_ok(False)
                isabelle_response_message.set_info("isabelle responses 响应空")
                return isabelle_response_message
            elif responses == "isabelle_Timeout":
                isabelle_response_message.set_ok(False)
                isabelle_response_message.set_info("isabelle_Timeout")
                self.get_logger().warning(responses)
                return isabelle_response_message
            elif responses[-1].response_type != 'FINISHED':
                isabelle_response_message.set_ok(False)
                isabelle_response_message.set_info("response_type不为FINISHED")
                return isabelle_response_message
            elif not json.loads(responses[-1].response_body)["ok"]:
                isabelle_response_message.set_ok(False)
                isabelle_response_message.set_info("check_syntax 错误")
                #return json.loads(responses[-1].response_body)["ok"], "check_syntax 错误"
                #添加错误信息
                errors = json.loads(responses[-1].response_body)["errors"]
                for error in errors:
                    isabelle_response_message.add_syntax_error_message(error["message"])
                #添加反例信息
                messages = json.loads(responses[-1].response_body)["nodes"][-1]["messages"]
                for message in messages:
                    if 'Nitpick found a counterexample' in message["message"]:
                        isabelle_response_message.add_counterexample_message(message)
                return isabelle_response_message
            isabelle_response_message.set_ok(True)
            return isabelle_response_message

    def run_sledgehammer(self, theory_path, data_message:Message, pre, post, args, subgoal_lemmas=None, count=1):
        """
        调用sledgehammer，返回theory是否被证明
        :param theory_path:
        :param name:
        :param pre:
        :param post:
        :return:
        """
        if subgoal_lemmas is None:
            subgoal_lemmas = {}
        self.get_logger().info("----------------------------------开始 run_sledgehammer-------------------------------------------")
        responses = None
        method = ""
        formal = ""

        try:
            responses = self.get_responses(theory_path, data_message.getData()["theorem name"])
        except FunctionTimedOut as e:
            self.get_logger().warning(e)
        finally:
            if responses is None:
                return False, method, formal
            if responses == "isabelle_Timeout":
                return False, method, formal
        self.get_logger().info(responses)
        """if pre == '' and post == '':
            return json.loads(responses[-1].response_body)["ok"]"""
        tactics = get_tactics(responses, self.get_logger())
        self.get_logger().info(f"------------得到 证明策略 {tactics}----------------")

        for tactic in tactics:
            if "by" in tactic:
                tactic_ = tactic

            elif "apply" in tactic:
                tactic_ = tactic + "\nsorry\n"

            else:
                self.get_logger().info(f"策略{tactic}不是by 和 apply")
                sys.exit()
            thy = get_theory_with_lemmas(data_message, pre, tactic_, post, verified_midlemmas=data_message.get_all_verified_lemmas(),
                                     unverified_midlemmas=utils.jsonmerge(data_message.get_unverified_lemmas(), copy.copy(subgoal_lemmas)))
            write_thy(theory_path, data_message.getData()["theorem name"], thy)
            self.get_logger().info(thy)
            if not self.theory_proof(theory_path, data_message.getData()["theorem name"]):
                self.get_logger().info(f"------------证明策略 {tactic} 证明失败----------------")
                method = tactic
                continue
            else:
                self.get_logger().info(f"------------证明策略 {tactic} 证明成功----------------")
                if "by" in tactic:
                    method = tactic
                if "apply" in tactic:
                    method = tactic + "\nsorry\n"
                formal = pre + method + post
                return True, method, formal

        if args.dataset in ["boundedstack", "priority_queue"] and count > 0 and data_message.get_property() == "lemma":
            self.get_logger().info(f"------------using alist_of Abs_pq_inverse----------------")
            thy = get_theory_with_lemmas(data_message, pre + " using alist_of ",
                                         f"\nsledgehammer [prover=cvc4 vampire verit e spass z3 zipperposition] sorry\n",
                                         post, verified_midlemmas=data_message.get_all_verified_lemmas(),
                                         unverified_midlemmas=utils.jsonmerge(data_message.get_unverified_lemmas(), copy.copy(subgoal_lemmas)))
            write_thy(theory_path, data_message.getData()["theorem name"], thy)
            self.get_logger().info(thy)
            return self.run_sledgehammer(theory_path, data_message, pre + " using alist_of ", post, args, count=count-1, subgoal_lemmas=subgoal_lemmas)
        self.get_logger().info(f"------------所有证明策略证明失败----------------")

        #save_false_theory(args.false_proof_trace_path, thy, data_message.getData()["theorem name"], args.time)

        return False, method, formal

    def theory_proof(self, theory_path, name) -> bool:
        """
        返回理论是否验证成功
        :param theory_path:
        :param name:
        :return:
        """
        responses = None
        """init_name = name[:len(name)-3]
        rename(theory_path, name, init_name)"""
        try:
            responses = self.get_responses(theory_path, name)
        # except FunctionTimedOut as e:
        except Exception as e:
            self.get_logger().warning(e)
        finally:
            if responses is None:
                return False
            if responses == "isabelle_Timeout":
                return False
            if responses[-1].response_type == 'FAILED':
                self.get_logger().warning(responses[-1].response_body)
                return False
        # args.logger.info(responses[-1])
        #self.get_logger().info(responses[-1].response_body)
        """self.get_logger().info("=====")
        self.get_logger().info(responses[-1])
        self.get_logger().info("=====")
        self.get_logger().info(responses)"""
        return json.loads(responses[-1].response_body)["ok"]

    def get_proof_state(self, pre, post, data_message:Message, theory_path):
        """
        :param pre: 属于formal的前半部分，是以当前目标为断点，将formal分为两部分， 前部分是pre， 后部分是post
        :param post:
        :param data:
        :param theory_path:
        :param midlemmas:
        :return:
        """
        thy = get_theory_with_lemmas(data_message, pre, "print_state\n" + "ML\\<open>\nwriteln \"<print_state>\"\n\\<close>\n",
                          post, verified_midlemmas=data_message.get_all_verified_lemmas(),
                                         unverified_midlemmas=data_message.get_unverified_lemmas())
        print(thy)
        write_thy(theory_path, data_message.getData()["theorem name"], thy)
        responses = self.get_responses(theory_path, data_message.getData()["theorem name"])
        print(responses)
        if responses is None:
            print("isabelle response 异常 FAILED")
            sys.exit(0)
        if responses == "isabelle_Timeout":
            return ""
        response_type = responses[-1].response_type
        print(response_type)
        if response_type != 'FINISHED':
            return ""
        messages = json.loads(responses[-1].response_body)["nodes"][-1]["messages"]
        print("----------------------messages----------------------")
        print(messages)
        for i, message in enumerate(messages):
            if message["message"] == '<print_state>':
                proof_state_message = messages[i - 2]["message"]
                return proof_state_message
        return ""




if __name__ == '__main__':
    pre = """
    
theorem bounded_stack_push_pop_inverse :
  assumes a1:"\<not> isfull s"
  shows "pop (push x s) = (Some x, s)"
proof -
  have "push x s \<noteq> s" using a1 push_def isfull_def 
    """

    post = """
          then obtain xs where xs_def: "alist_of (push x s) = xs" sorry
  have h1: "pop (push x s) = (Some (hd (fst xs)), Abs_bstack (tl (fst xs), snd xs))"
    using pop_def xs_def sorry
  have "hd (fst xs) = x" using xs_def sorry
  then have "hd (fst xs) = x" sorry
  hence "pop (push x s) = (Some x, s)" using h1 xs_def sorry
  thus ?thesis by simp
qed

    """
    data = {
	"packages":	"Main",
	"theorem name":	"bounded_stack_push_pop_inverse",
	"function names":	["capacity","size","isfull","isempty","pop","push"],
	"other formal":	"\ntypedef (overloaded) 'a bstack =\n \"{xs :: ('a list \\<times> nat). length (fst xs) \\<le> snd xs}\"\n morphisms alist_of Abs_bstack\nproof -\n have \"([],0) \\<in> {xs. length (fst xs) \\<le> snd xs}\" by simp\n thus ?thesis by blast\nqed",
	"other rules": ["alist_of_inverse", "alist_of", "Abs_bstack_inverse", "Abs_bstack_inject"],
	"formal function definitions":	{
		"capacity":	"definition capacity :: \"'a bstack \\<Rightarrow> nat\"\nwhere \"capacity s \\<equiv> snd (alist_of s)\"",
		"size":	"definition size :: \"'a bstack \\<Rightarrow> nat\"\nwhere \"size s \\<equiv> length (fst (alist_of s))\"",
		"isfull":	"definition isfull :: \"'a bstack \\<Rightarrow> bool\"\nwhere \"isfull s \\<equiv> size s = capacity s\"",
		"isempty": "definition isempty :: \"'a bstack \\<Rightarrow> bool\"\nwhere \"isempty s \\<equiv> fst (alist_of s) = []\"",
		"pop":	"definition pop :: \"'a bstack \\<Rightarrow> ('a option \\<times> 'a bstack)\"\nwhere \"pop s \\<equiv> \n(if \\<not> isempty s then \n (Some (hd (fst (alist_of s))), Abs_bstack (tl (fst (alist_of s)), snd (alist_of s))) \n else (None, s))\"",
		"push":	"definition push :: \"'a \\<Rightarrow> 'a bstack \\<Rightarrow> 'a bstack\"\nwhere \"push v s \\<equiv> \n(if \\<not>isfull s then \n Abs_bstack (v # fst (alist_of s), snd (alist_of s)) \n else s)\""
	},
	"formal theorem statement": "theorem bounded_stack_push_pop_inverse :\n  assumes a1:\"\\<not> isfull s\"\n  shows \"pop (push x s) = (Some x, s)\""
}
    data_message = Message(data=data,class_name="")
    theory_path = "../output"
    isabelle = Isabelle()

    print(isabelle.get_proof_state(pre, post, data_message, theory_path))




    def check_syntax(self, theory_path: str, name: str) -> bool:
        """
        :param theory_path: 输入待检测theory的文件路径
        :param name: theory文件名
        :return: 此thy的证明过程语法是否有误，所有的中间猜想都没证明，使用sorry填充
        """
        return self.theory_proof(theory_path, name)

    def check_proof_path(self, theory_path: str, name: str, args) -> bool:
        """
        :param theory_path: 输入待检测theory的文件路径
        :param name: theory文件名
        :return: 此thy的证明路径是否有误，所有的中间猜想都没证明，使用sorry填充，只有最后一步（证明此引理）使用sledgehammer
        填充
        """
        pre, post = finally_sorry_to_sledgehammer(theory_path, name)
        if pre == '' and post == '':
            return self.theory_proof(theory_path, name)
        isproof,method = self.run_sledgehammer(theory_path, name, pre, post, args)
        return isproof

    def check_proof_path1(self, theory_path: str, name: str, args) -> bool:
        """
        :param theory_path: 输入待检测theory的文件路径
        :param name: theory文件名
        :return: 此thy的证明路径是否有误，所有的中间猜想都没证明，使用sorry填充，只有最后一步（证明此引理）使用sledgehammer
        填充
        """
        pre, post = finally_sorry_to_sledgehammer(theory_path, name)
        if pre == '' and post == '':
            return self.theory_proof(theory_path, name)
        isproof,method = self.run_sledgehammer(theory_path, name, pre, post, args)
        return isproof

    def nitpick_check_all_subgoal(self, theory_path, name):
        self.get_logger().info("----------------------------------开始 run_nitpick_check_all_subgoal-------------------------------------------")
        responses = None

        try:
            responses = self.get_responses(theory_path, name)
        except FunctionTimedOut as e:
            self.get_logger().warning(e)
        finally:
            if responses is None:
                return False, ""
            if responses == "isabelle_Timeout":
                self.get_logger().warning(responses)
                return False, "isabelle_Timeout"
        #self.get_logger().info(responses)
        response_type = responses[-1].response_type
        if response_type != 'FINISHED':
            return False, ""
        messages = json.loads(responses[-1].response_body)["nodes"][-1]["messages"]
        for message in messages:
            if 'Nitpick found a counterexample' in message["message"]:
                return False, message["message"]
        return True, ""



    def run_heuristic_sledgehammer(self, theory_path, name, pre, post):
        """
        #访问isabelle client，返回responses，在访问之前使用heuristic
        # ['by auto', 'by simp', 'by blast', 'by fastforce', 'by force', 'by eval', 'by presburger', 'by sos',
         'by arith', 'by linarith', 'by (auto simp: field_simps)']
        #返这一步的sledgehammer是否成功
        :param theory_path:
        :param name:
        :param pre:
        :param post:
        :return:
        """
        self.get_logger().info(
            "-------------------------------开始 run_heuristic_sledgehammer-----------------------------------")
        for heuristic in ['by auto', 'by simp', 'by blast', 'by fastforce', 'by force', 'by eval', 'by presburger',
                          'by sos', 'by arith', 'by linarith', 'by (auto simp: field_simps)']:
            thy = pre + heuristic + post
            write_thy(theory_path, name, thy)
            responses = None
            try:
                responses = self.get_responses(theory_path, name)
            except FunctionTimedOut as e:
                self.get_logger().warning(e)
            finally:
                if responses is None:
                    return False
                if responses == "isabelle_Timeout":
                    return False
            if not json.loads(responses[-1].response_body)["ok"]:
                self.get_logger().info(f'----------- heuristic--{heuristic} 证明失败------------')
                continue
            else:
                self.get_logger().info(f'----------- heuristic--{heuristic} 证明成功------------')
                return True
        self.get_logger().info(f'----------- 所有-- heuristic--证明失败------------')
        return False


def get_tactic(message, logger):
    """
    从字符串'"vampire": Try this: by simp (0.0 ms)' ，'"cvc4": Try this: by simp (0.0 ms)’中获取‘by simp’
    :param message:
    :return:
    """
    #result = re.match(r'(.*?)Try this: (.*?) \(([0-9]*.?[0-9]*) ms\)', message)

    if message.endswith(" ms)"):
        result = re.match(r'(.*?)Try this: (.*?) \(([0-9]*.?[0-9]*) ms\)', message)
    elif message.endswith(" s)"):
        result = re.match(r'(.*?)Try this: (.*?) \(([0-9]*.?[0-9]*) s\)', message)
    else:
        result = None
    if result is None:
        result = re.match(r'(.*?)Try this: (.*?)$', message)
    if result is None and 'by' in message:
        logger.info("有证明策略，但没有获得")
        return ''
    return result.group(2)


def add_tactic_to_tactics(tactics, tactic):
    """
    tactic在tactices中不存在，则将tactic添加到tactices
    :param tactics:
    :param tactic:
    :return:
    """
    for tactic_ in tactics:
        if tactic_ == tactic:
            return tactics
    tactics.append(tactic)
    return tactics


def get_tactics(responses, logger):
    """
    返回sledgehammer提供的证明策略 ,例如by simp,by auto
    :param responses:
    :return:
    """
    tactics = []
    response_type = responses[-1].response_type
    if response_type != 'FINISHED':
        return tactics
    messages = json.loads(responses[-1].response_body)["nodes"][-1]["messages"]
    for message in messages:
        if message["kind"] != 'writeln':
            continue
        if 'by' not in message["message"] and 'apply' not in message["message"]:
            continue
        logger.info(f'--------------------------------messages----------------------------\n{message["message"]}')
        tactic = get_tactic(message["message"], logger)
        logger.info(f'tactic : {tactic}')
        if tactic != '':
            tactics = add_tactic_to_tactics(tactics, tactic)
    return tactics
