import argparse
import logging
import re

import time
from abc import ABCMeta

import colorlog

import utils
from Chromadb.Collection import Collection
from Chromadb.ROLE_COLLECTION import Role_collection

from generator.Key import Key
from generator.LLM import LLM
from generator.Prompter import Prompter
from generator.Role import Role
from message.Message import Message
from utils import match_midlemmas


def remove_similar_lemma(lemmas, data_message:Message, collection:Collection, logger, role:Role):
    if collection.embedding_model_name == "":
        threshold_problem = 0.175
        threshold_verified = 0.05
    elif collection.embedding_model_name == "text-embedding-3-small":
        threshold_problem = 0.15
        threshold_verified = 0.09
    else:
        exit()
        logger.warning(f"--{collection.embedding_model_name}--此模型未设置--")
    if role == Role.REFLECTION_LEMMA:
        threshold_problem = 0.05
        threshold_verified = 0.05

    logger.info("-----------remove_similar_lemma--------------")
    logger.info("-----------all lemma--------------")
    logger.info(len(lemmas))
    logger.info(lemmas)
    lemmas_ = {}
    for name, lemma in lemmas.items():
        #problem
        logger.info(
            f"\n-------------problem-------------------------\n")
        dintance,document = collection.similarity_distance(Role_collection.PROBLEM, lemma, data_message.get_class(), data_message.get_theorem_name())
        dintance1, document1 = collection.similarity_distance(Role_collection.VERIFIED_LEMMA1, lemma, data_message.get_class())
        logger.info(f"dintance = {dintance}, dintance1 = {dintance1}")
        logger.info(
            f"\n{lemma}\n与document\n{document}\n -dintance--\n{dintance}-------------------------")
        logger.info(
            f"\n{lemma}\n与document1\n{document1}\n -dintance1--{dintance1}-------------------------")


        if dintance > threshold_problem and dintance1 > threshold_verified:
            lemmas_[name] = lemma
        else:
            logger.info(f"dintance = {dintance}, dintance1 = {dintance1}")
            logger.info(
                f"\nlemma\n与定理\n{data_message.getData()['formal theorem statement']}\n 非常相似，被移除。-------------------------")


        """# verified lemma
        logger.info(
            f"\n----------------verified lemma-------------------------\n")
        dintance, document = collection.similarity_distance(Role_collection.VERIFIED_LEMMA1, lemma)
        logger.info(
            f"\n{lemma}\n与document\n{document}\n -dintance--{dintance}-------------------------")
        if collection.embedding_model_name == "":
            if dintance > 0.05:
                lemmas_[name] = lemma
            else:
                logger.info(
                    f"\n{lemma}\n与已验证的引理\n{document}\n 非常相似，被移除。-------------------------")
                continue
        elif collection.embedding_model_name == "text-embedding-3-small":
            if dintance > 0.09:
                lemmas_[name] = lemma
            else:
                logger.info(
                    f"{lemma}\n与定理\n{data_message.getData()['formal theorem statement']}\n 非常相似，被移除。-------------------------")
                continue
        else:
            logger.info(f"--{collection.embedding_model_name}--此模型未设置--")"""
    logger.info("-----------after remove_similar_lemma--------------")
    logger.info(len(lemmas_))
    logger.info(lemmas_)
    return lemmas_


class Generator(metaclass=ABCMeta):
    def __init__(self, llm, prompter, logger=None, collection=None):
        self.LLM = llm
        self.prompter = prompter
        self.logger = logger
        self.__collection = collection

    def get_collection(self):
        return self.__collection

    def get_prompter(self):
        return self.prompter

    def config(self, system_message="", max_tokens=0, n=0, model="",
               temperature=0, frequency_penalty=0, presence_penalty=0):
        if not "" == system_message:
            self.LLM.system_message = system_message
        if not 0 == max_tokens:
            self.LLM.max_tokens = max_tokens
        if not "" == model:
            self.LLM.model = model
        if not 0 == n:
            self.LLM.n = n
        if not 0 == temperature:
            self.LLM.temperature = temperature
        if not 0 == frequency_penalty:
            self.LLM.frequency_penalty = frequency_penalty
        if not 0 == presence_penalty:
            self.LLM.presence_penalty = presence_penalty

    def request_model_responses(self, data_name , problem, role:Role, max_tokens = 1024, n=5,failure_limit=3):
        while True:
            prompt = self.prompter.get_prompt(role)
            examples = self.prompter.get_examples(data_name, role)
            self.logger.info(prompt)
            self.logger.info(examples)
            self.logger.info(problem)

            self.LLM.init_model_messages()
            self.LLM.add_system_message(prompt)
            self.LLM.add_examples(examples)
            self.LLM.add_problem(problem)
            self.LLM.max_tokens = max_tokens
            self.LLM.n = n
            res, error =  self.LLM.responses()
            if "This model's maximum context length" in error and failure_limit > 0:
                failure_limit = failure_limit - 1
                number_examples = self.prompter.number_examples
                if number_examples != 1:
                    self.prompter.set_number_examples(self.prompter.number_examples-1)
                continue
            else:
                return res

    def request_direct_lemma(self, data_message:Message, problem, role:Role, max_tokens = 1024, n=5, number_examples=-1):
        if number_examples != -1:
            self.prompter.set_number_examples(number_examples)
        responses = self.request_model_responses(data_message.getData()["theorem name"], problem, role, max_tokens=max_tokens, n=n)
        lemmas = get_midlemmas_from_response(responses, data_message, logger=self.logger)
        lemmas = remove_similar_lemma(lemmas, data_message, self.get_collection(), self.logger, role)
        return lemmas, role

    def request_indirct_lemma(self, data_message:Message, problem, role:Role, max_tokens = 1024, n=5, number_examples=-1):
        if number_examples != -1:
            self.prompter.set_number_examples(number_examples)
        responses = self.request_model_responses(data_message.getData()["theorem name"], problem, role, max_tokens=max_tokens, n=n)
        lemmas = get_midlemmas_from_response(responses, data_message, logger=self.logger)
        lemmas = remove_similar_lemma(lemmas, data_message, self.get_collection(), self.logger, role)
        return lemmas, role

    def request_subgoal_lemma(self, data_message:Message, problem, role:Role, max_tokens = 1024, n=5, number_examples=-1):
        if number_examples != -1:
            self.prompter.set_number_examples(number_examples)
        responses = self.request_model_responses(data_message.getData()["theorem name"], problem, role, max_tokens=max_tokens, n=n)
        lemmas = get_midlemmas_from_response(responses, data_message, logger=self.logger)
        lemmas = remove_similar_lemma(lemmas, data_message, self.get_collection(), self.logger, role)
        return lemmas, role

    def request_reflection_lemma(self, data_message:Message, problem, role:Role, max_tokens = 1024, n=5, number_examples=-1):
        if number_examples != -1:
            self.prompter.set_number_examples(number_examples)
        responses = self.request_model_responses(data_message.getData()["theorem name"], problem, role, max_tokens=max_tokens, n=n)
        lemmas = get_midlemmas_from_response(responses, data_message, logger=self.logger)
        lemmas = remove_similar_lemma(lemmas, data_message, self.get_collection(), self.logger, role)
        return lemmas, role

    def request_formal(self, data_message:Message, problem, role:Role, max_tokens = 1024, n=5, number_examples=-1):
        if number_examples != -1:
            self.prompter.set_number_examples(number_examples)
        responses = self.request_model_responses(data_message.getData()["theorem name"], problem, role, max_tokens=max_tokens, n=n)
        formals = get_formal_from_responses(responses, logger=self.logger)
        return formals

    def request_informal(self, data_message:Message, problem, role:Role, max_tokens=1024, n=5, number_examples=-1):
        if number_examples != -1:
            self.prompter.set_number_examples(number_examples)
        responses = self.request_model_responses(data_message.getData()["theorem name"], problem, role, max_tokens=max_tokens, n=n)
        return responses

    def request_formalizer(self, data_message:Message, problem, role, max_tokens=1024, n=5, number_examples=-1):
        if number_examples != -1:
            self.prompter.set_number_examples(number_examples)
        responses = self.request_model_responses(data_message.getData()["theorem name"], problem, role, max_tokens=max_tokens, n=n)
        formals = get_formal_from_responses(responses, logger=self.logger)
        return formals

    def request_informalizer(self, data_message:Message, problem, role, max_tokens=1024, n=5, number_examples=-1):
        if number_examples != -1:
            self.prompter.set_number_examples(number_examples)
        responses = self.request_model_responses(data_message.getData()["theorem name"], problem, role, max_tokens=max_tokens, n=n)
        return responses

    """def get_responses(self, data_name, problem, role:Role):
            if role == Role.DIRECT_LEMMA:
                return self.request_direct_lemma(data_name, problem)
            elif role == Role.INDIRECT_LEMMA:
                return self.request_indirct_lemma(data_name, problem)
            elif role == Role.SUBGOAL_LEMMA:
                return self.request_subgoal_lemma(data_name, problem)
            elif role == Role.INFORMAL:
                return self.request_informal(data_name, problem)
            elif role == Role.FORMAL:
                return self.request_formal(data_name, problem)
            elif role == Role.INFORMALIZER:
                return self.resquest_informalizer(data_name, problem)
            elif role == Role.FORMALIZER:
                return self.resquest_formalizer(data_name, problem)"""
        
def get_midlemmas_from_response(response_messages, data_message:Message, logger=None):
    midlemmas = {}
    lemma_message = []
    data_message.clean_lemma_messages()
    logger.info("********************response_messages**********************")
    logger.info(len(response_messages))
    for response_message in response_messages:
        logger.info("*********************midlemma_message**********************")
        #logger.info(response_message)
        midlemmas_ = match_midlemmas(response_message, data_message)
        if midlemmas_ != {}:
            data_message.add_lemma_messages(response_message)
        logger.info(f"\n\n--------当前大的midlemmas-----\n\n")
        logger.info(midlemmas_)
        logger.info(len(midlemmas_))
        if midlemmas_ == {}:
            continue
        for midlemma_key, midlemma_value in midlemmas_.items():
            if midlemma_key not in midlemmas and midlemma_value not in midlemmas.values():
                midlemmas[midlemma_key] = midlemma_value
        logger.info(f"\n\n--------最后的midlemmas-----\n\n")
        logger.info(midlemmas)
        logger.info(len(midlemmas))
    return midlemmas

def get_formal_from_responses(responses, logger=None):
    logger.info(responses)
    formals = []
    for response in responses:
        logger.info("________________________")
        logger.info(response)
        res = re.match(r'(.*?)```isabelle(.*?)```', response, flags=re.S)
        if res:
            logger.info("++++++++++++++++++++++++++++__________________________")
            formals.append(res.group(2))
            logger.info(res.group(2))
    return formals

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--direct_lemma_examples_path', type=str, default='../prompt/prompt1/direct_lemma/')
    parser.add_argument('--indirect_lemma_examples_path', type=str, default='../prompt/prompt1/indirect_lemma/')
    parser.add_argument('--subgoal_lemma_examples_path', type=str, default='../prompt/prompt1/subgoal_lemma/')
    parser.add_argument('--informal_examples_path', type=str, default='../prompt/prompt1/formal/')
    parser.add_argument('--formal_examples_path', type=str, default='../prompt/prompt1/formal/')
    parser.add_argument('--informalizer_examples_path', type=str, default='../prompt/prompt2/informalizer/')
    parser.add_argument('--formalizer_examples_path', type=str, default='../prompt/prompt2/formalizer/')
    parser.add_argument('--system_messages_path', type=str, default='./system_messages.json')
    parser.add_argument('--keys_path', type=str, default='../data/keys')

    args = parser.parse_args()

    logger = utils.get_logger()
    args.logger = logger

    api_base = "https://api.xiaoai.plus/v1"

    key: Key = Key(args.keys_path)
    llm = LLM(key=key , model='gpt-3.5-turbo', logger = logger, api_base=api_base)
    prompter = Prompter(1)
    prompter.read_all_prompts(args)
    prompter.read_all_examples(args)

    generator = Generator(llm=llm, prompter=prompter)

    data_name = "bounded_stack_pop_push_inverse"

    problem = """## Function definition
```isabelle
typedef (overloaded) 'a bstack =
  "{xs :: ('a list \<times> nat). length (fst xs) \<le> snd xs}"
  morphisms alist_of Abs_bstack
proof -
  have "([],0) \<in> {xs. length (fst xs) \<le> snd xs}" by simp
  thus ?thesis by blast
qed
```

```isabelle
definition capacity :: "'a bstack \<Rightarrow> nat"
where "capacity s \<equiv> snd (alist_of s)"
```

```isabelle
definition size :: "'a bstack \<Rightarrow> nat"
where "size s \<equiv> length (fst (alist_of s))"
```

```isabelle
definition isfull :: "'a bstack \<Rightarrow> bool"
where "isfull s \<equiv> size s = capacity s"
```

```isabelle
definition isempty :: "'a bstack \<Rightarrow> bool"
where "isempty s \<equiv> fst (alist_of s) = []"
```

```isabelle
definition push :: "'a \<Rightarrow> 'a bstack \<Rightarrow> 'a bstack"
where "push v s \<equiv> (if \<not>isfull s then
                      Abs_bstack (v # fst (alist_of s), snd (alist_of s))
                   else s)"
```

```isabelle
definition pop :: "'a bstack \<Rightarrow> ('a option \<times> 'a bstack)"
where "pop s \<equiv> (if \<not> isempty s then
                  (Some (hd (fst (alist_of s))), Abs_bstack (tl (fst (alist_of s)), snd (alist_of s)))
                else (None, s))"
```

## Implicit rules
### Dependent function
snd :   snd (?x1.0, ?x2.0) \<equiv> ?x2.0
fst :   fst (?x1.0, ?x2.0) \<equiv> ?x1.0
hd :   hd (?x21.0 # ?x22.0) \<equiv> ?x21.0
tl :   tl [] \<equiv> []  tl (?x21.0 # ?x22.0) \<equiv> ?x22.0

### Dependent rules
alist_of_inverse : Abs_bstack (alist_of ?x) = ?x
alist_of : alist_of ?x \<in> {xs. length (fst xs) \<le> snd xs}
Abs_bstack_inverse : ?y \<in> {xs. length (fst xs) \<le> snd xs} \<Longrightarrow> alist_of (Abs_bstack ?y) = ?y
Abs_bstack_inject : ?x \<in> {xs. length (fst xs) \<le> snd xs} \<Longrightarrow>
                    ?y \<in> {xs. length (fst xs) \<le> snd xs} \<Longrightarrow> (Abs_bstack ?x = Abs_bstack ?y) = (?x = ?y)

### Verified intermediate lemma

## Theorem statement
```isabelle
theorem bounded_stack_pop_push_inverse:
  assumes a1:"\<not> isempty s" and a2:"(v, s0) = pop s"
  shows "push (the v) s0 = s"
```
## Informal proof
To prove the theorem bounded_stack_pop_push_inverse, we aim to show that if we pop an element from a non-empty stack s, and then push the popped element back onto the resulting stack s0, we get the original stack s.

The proof will proceed by the following steps:

Step 1: Assumptions: We assume that the stack s is non-empty (\<not> isempty s), and we have (v, s0) = pop s, where v is the value popped from s and s0 is the resulting stack.

Step 2: Case analysis on the isfull s condition:

- Case 1: If isfull s = True, then the stack s is already full and cannot accommodate any more elements. In this case, the pop operation does not modify the stack, so s0 = s. Since the stack is full, the push operation will not change the stack either. Therefore, push (the v) s0 = push (the v) s = s.

- Case 2: If isfull s = False, then the stack s is not full and can accommodate more elements. In this case, the pop operation removes the top element from the stack, and s0 is the resulting stack. The push operation then adds the popped element back to the top of the resulting stack s0. Since the push operation adds the element to the top of the stack, the resulting stack will be the same as the original stack s. Therefore, push (the v) s0 = push (the v) (pop s) = s.

Step 3: Conclusion: In both cases, we have shown that push (the v) s0 = s. Therefore, the theorem bounded_stack_pop_push_inverse holds.

"""


    """## Informal proof
To prove the theorem bounded_stack_pop_push_inverse, we aim to show that if we pop an element from a non-empty stack s, and then push the popped element back onto the resulting stack s0, we get the original stack s.

The proof will proceed by the following steps:

Step 1: Assumptions: We assume that the stack s is non-empty (\<not> isempty s), and we have (v, s0) = pop s, where v is the value popped from s and s0 is the resulting stack.

Step 2: Case analysis on the isfull s condition:

- Case 1: If isfull s = True, then the stack s is already full and cannot accommodate any more elements. In this case, the pop operation does not modify the stack, so s0 = s. Since the stack is full, the push operation will not change the stack either. Therefore, push (the v) s0 = push (the v) s = s.

- Case 2: If isfull s = False, then the stack s is not full and can accommodate more elements. In this case, the pop operation removes the top element from the stack, and s0 is the resulting stack. The push operation then adds the popped element back to the top of the resulting stack s0. Since the push operation adds the element to the top of the stack, the resulting stack will be the same as the original stack s. Therefore, push (the v) s0 = push (the v) (pop s) = s.

Step 3: Conclusion: In both cases, we have shown that push (the v) s0 = s. Therefore, the theorem bounded_stack_pop_push_inverse holds.
"""
    pro = [{"role": "user", "content": problem}]
    #responses = generator.request_model_responses(data_name, pro, Role.INFORMAL)
    #self.logger.info(responses)
    logger.info("-----------------------------")
    lemmas = generator.request_direct_lemma(data_name,pro,Role.DIRECT_LEMMA,max_tokens=800)
    #lemmas = generator.request_indirct_lemma(data_name,pro,Role.INDIRECT_LEMMA,max_tokens=400)
    #formals = generator.request_formal(data_name, pro , Role.FORMAL,max_tokens=400)
    #informals = generator.request_informal(data_name, pro , Role.INFORMAL,max_tokens=400)
    logger.info("++++++++++++++++")
    logger.info(lemmas)

    """for formal in formals:
        self.logger.info(formal)"""