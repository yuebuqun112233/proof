import json

import utils
from message.Isabelle_response_message import Isabelle_response_message
from message.Message import Message
from verify.Isabelle import Isabelle


class Checker():
    def __init__(self, isabelle:Isabelle, logger=None):
        self.__isabelle = isabelle
        self.logger = logger

    def set_isabelle(self, isabelle):
        self.__isabelle = isabelle

    def get_isabelle(self):
        return self.__isabelle

    def check_nitpick_syntax_all_subgoal(self, formal, theory_path, data_message):
        formal = utils.formal_sketch_format_match(formal)
        formal_ = str.replace(formal, 'sorry', 'nitpick sorry')
        theory = utils.get_theory(data_message, formal_.strip(), data_message.getData()["theorem name"])
        utils.write_thy(theory_path, data_message.getData()["theorem name"], theory)
        self.logger.info(theory)

        isabelle_response_message: Isabelle_response_message = self.get_isabelle().nitpick_check_syntax_all_subgoal(theory_path, data_message.getData()["theorem name"])

        if isabelle_response_message.get_ok():
            self.logger.info("检查通过")
            return formal.strip()
        else:
            self.logger.info(isabelle_response_message.get_info())
            return ""

    def check_nitpick_syntax_for_lemma(self, lemma_name, lemma, theory_path, data_message):

        formal = lemma + " nitpick sorry"
        theory = utils.get_theory(data_message, formal, lemma_name)
        utils.write_thy(theory_path, lemma_name, theory)
        self.logger.info(theory)

        isabelle_response_message: Isabelle_response_message = self.get_isabelle().nitpick_check_syntax_all_subgoal(
            theory_path, lemma_name)

        if isabelle_response_message.get_ok():
            self.logger.info("检查通过")
            return True
        else:
            self.logger.info(isabelle_response_message.get_info())
            return False


    def check_nitpick_syntax_for_lemmas(self, lemmas, theory_path, data_message):
        lemmas_ = {}
        for lemma_name, lemma in lemmas.items():
            """formal = lemma + " nitpick sorry"
            theory = utils.get_theory(data_message, formal, lemma_name)
            utils.write_thy(theory_path, lemma_name, theory)
            self.logger.info(theory)

            isabelle_response_message: Isabelle_response_message = self.get_isabelle().nitpick_check_syntax_all_subgoal(
                theory_path, lemma_name)"""
            is_ok = self.check_nitpick_syntax_for_lemma(lemma_name, lemma, theory_path, data_message)

            if is_ok:
                lemmas_[lemma_name] = lemma
            else:
                continue
        return lemmas_

    def check_path_for_formal(self, theory_path, data_message:Message, args, formal):

        pre, post = utils.final_key(formal, 'sorry')
        if pre == '' and post == '':  # pre和post同时为空的条件是，文件中没有一个sorry
            return False, "", ""
        thy = utils.get_theory_with_lemmas(data_message, pre,
                                     f"\nsledgehammer [prover=cvc4 vampire verit e spass z3 zipperposition] sorry\n",
                                           post, verified_midlemmas=data_message.get_all_verified_lemmas(),
                                           unverified_midlemmas=data_message.get_unverified_lemmas())
        utils.write_thy(theory_path, data_message.getData()["theorem name"], thy)
        self.logger.info(thy)
        isproof, method, formal = self.get_isabelle().run_sledgehammer(theory_path, data_message, pre, post, args)
        if isproof:
            self.logger.info(
                '----------------------------------sledgehammer 证明成功----------------------------------------------')
            return isproof, method, formal
        return False, "", ""

    def check_theory(self, path, name, thy=""):
        if thy != "":
            utils.write_thy(path, name, thy)
        return self.get_isabelle().theory_proof(path, name)



if __name__ == '__main__':
    logger = utils.get_logger()
    isabelle = Isabelle(logger = logger)
    checker = Checker(isabelle=isabelle)
    formal = """
    theorem bounded_stack_pop_push_inverse:
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
    theory_path = "../output/without_newlemma/theory"
    data = {
	"packages": "Main",
	"theorem name": "bounded_stack_pop_push_inverse",
	"function names": ["capacity","size","isfull","isempty","pop","push"],
	"other formal": "\ntypedef (overloaded) 'a bstack =\n \"{xs :: ('a list \\<times> nat). length (fst xs) \\<le> snd xs}\"\n morphisms alist_of Abs_bstack\nproof -\n have \"([],0) \\<in> {xs. length (fst xs) \\<le> snd xs}\" by simp\n thus ?thesis by blast\nqed",
  "other rules": ["alist_of_inverse", "alist_of", "Abs_bstack_inverse", "Abs_bstack_inject"],
	"formal function definitions": {
		"capacity": "definition capacity :: \"'a bstack \\<Rightarrow> nat\"\nwhere \"capacity s \\<equiv> snd (alist_of s)\"",
        "size": "definition size :: \"'a bstack \\<Rightarrow> nat\"\nwhere \"size s \\<equiv> length (fst (alist_of s))\"",
        "isfull": "definition isfull :: \"'a bstack \\<Rightarrow> bool\"\nwhere \"isfull s \\<equiv> size s = capacity s\"",
        "isempty": "definition isempty :: \"'a bstack \\<Rightarrow> bool\"\nwhere \"isempty s \\<equiv> fst (alist_of s) = []\"",
        "push": "definition push :: \"'a \\<Rightarrow> 'a bstack \\<Rightarrow> 'a bstack\"\nwhere \"push v s \\<equiv> \n(if \\<not>isfull s then \n Abs_bstack (v # fst (alist_of s), snd (alist_of s)) \n else s)\"",
        "pop": "definition pop :: \"'a bstack \\<Rightarrow> ('a option \\<times> 'a bstack)\"\nwhere \"pop s \\<equiv> \n(if \\<not> isempty s then \n (Some (hd (fst (alist_of s))), Abs_bstack (tl (fst (alist_of s)), snd (alist_of s))) \n else (None, s))\""
   },
	"formal theorem statement": "theorem bounded_stack_pop_push_inverse:\n  assumes a1:\"\\<not> isempty s\" and a2:\"(v, s0) = pop s\"\n  shows \"push (the v) s0 = s\""
}
    data_message = Message(data=data,class_name="", theorem_name="")
    formal_ = checker.check_nitpick_syntax_all_subgoal(formal, theory_path, data_message)
    print(formal_)

    print("++++++++++++++++++++++++++++++++++++++++++++++")

    lemmas = {'push_pop_inverse': 'lemma push_pop_inverse:\n  assumes a1: "\\<not> isfull s" and a2: "\\<not> isempty s"\n  shows "push (the (fst (pop s))) (snd (pop s)) = s"', 'pop_push_inverse': 'lemma pop_push_inverse:\n  assumes a1: "\\<not> isempty s"\n  shows "snd (pop (push (the v) s)) = s"'}

    lemmas_ = checker.check_nitpick_syntax_for_lemmas(lemmas, theory_path, data_message)
    print(lemmas_)