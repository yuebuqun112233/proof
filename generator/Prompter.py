import argparse
import copy
import glob
import json
import os
import random

from generator.Role import Role
from message.Message import Message
from utils import read_dir, key_split_string, format_lemmas_mess, get_logger, read_dir_




def end_str(str, separator):
    index = str.find(separator)
    if index == -1:
        print("实例错误")
    return str[index:]


class Prompter:
    def __init__(self, number_examples, global_function_definition=None, logger=None):
        if global_function_definition is None:
            global_function_definition = [False, ""]
        self.number_examples = number_examples
        self.examples = {}
        self.prompts = {}
        self.function_definitions = {}
        self.global_function_definition = global_function_definition
        self.logger = logger

    def set_number_examples(self, number_examples):
        self.number_examples = number_examples

    def set_function_attribute(self, attribute):
        self.global_function_definition[1] = attribute

    def get_examples(self, dataname, role: Role):
        if self.global_function_definition[0]:
            examples = self.__get_examples_global(dataname, role)
        else:
            examples = self.__get_examples(dataname, role)
        return examples

    def __get_examples(self, dataname, role:Role):
        examples = self.examples[role.name.lower()]
        if self.number_examples < 1:
            return []
        examples_list = list(examples)
        examples_list_ = examples_list
        for examples_name in examples_list_:
            if dataname in examples_name:
                examples_list.remove(examples_name)
        if len(examples_list) < self.number_examples:
            examples_n_names = random.sample(examples_list, len(examples_list))
        else:
            examples_n_names = random.sample(examples_list, self.number_examples)
        examples_n = []
        for count,examples_n_name in enumerate(examples_n_names):
            content = f"#Examples{count + 1}\n\n" + examples[examples_n_name] + "\n\n"
            user_message = {"role": "user", "content": content}
            examples_n.append(user_message)
        return examples_n

    def __get_examples_global(self, dataname, role:Role):
        examples = self.examples[role.name.lower()]
        if self.number_examples < 1:
            return []
        examples_ = {}
        example:str
        for name, example in examples.items():
            if example.startswith(self.global_function_definition[1]):
                examples_[name] = example
        self.logger.info(f"attribute= {self.global_function_definition[1]} \n{examples_}")
        examples_list = list(examples_)
        examples_list_ = copy.copy(examples_list)
        for examples_name in examples_list_:
            if dataname in examples_name:
                examples_list.remove(examples_name)
        if len(examples_list) == 0:
            self.logger.info("examples_list长度为0")
            examples_n_names = random.sample(examples_list_, self.number_examples)
        elif len(examples_list) < self.number_examples:
            examples_n_names = random.sample(examples_list, len(examples_list))
        else:
            examples_n_names = random.sample(examples_list, self.number_examples)
        examples_n = []
        examples_n.append({"role": "user", "content": self.function_definitions[self.global_function_definition[1]]})
        for count, examples_n_name in enumerate(examples_n_names):
            content = f"#Examples{count + 1}\n\n" + end_str(examples_[examples_n_name], "## Theorem statement") + "\n\n"
            user_message = {"role": "user", "content": content}
            examples_n.append(user_message)
        self.logger.info("examples_n")
        self.logger.info(examples_n)
        return examples_n

    def get_prompt(self, role:Role):
        return self.prompts[role.name.lower()]

    def read_all_prompts(self, args):
        self.prompts = json.loads(open(args.system_messages_path, encoding='utf-8').read())

    def read_all_examples(self, args):
        direct_lemma_examples = read_dir_(args.direct_lemma_examples_path, 'txt')
        self.examples["direct_lemma"] = direct_lemma_examples

        indirect_lemma_examples = read_dir_(args.indirect_lemma_examples_path, 'txt')
        self.examples["indirect_lemma"] = indirect_lemma_examples

        subgoal_lemma_examples = read_dir_(args.subgoal_lemma_examples_path, 'txt')
        self.examples["subgoal_lemma"] = subgoal_lemma_examples

        reflection_lemma_examples = read_dir_(args.reflection_lemma_examples_path, 'txt')
        self.examples["reflection_lemma"] = reflection_lemma_examples

        informal_examples = read_dir_(args.informal_examples_path, 'txt')
        self.examples["informal"] = informal_examples

        formal_examples = read_dir_(args.formal_examples_path, 'txt')
        self.examples["formal"] = formal_examples

        informalizer_examples = read_dir_(args.informalizer_examples_path, 'txt')
        self.examples["informalizer"] = informalizer_examples

        formalizer_examples = read_dir_(args.formalizer_examples_path, 'txt')
        self.examples["formalizer"] = formalizer_examples

        if self.global_function_definition[0]:
            self.__read_function_definitions(args)

    def __read_function_definitions(self, args):
        self.function_definitions = read_dir_(args.global_function_defintion_path, 'txt')

    #proof without newlemma for informalizer
    def format_problem_for_informalizer(self, data_message: Message):
        if self.global_function_definition[0]:
            problem = self.__format_problem_for_informalizer_global(data_message)
        else:
            problem = self.__format_problem_for_informalizer(data_message)
        return problem

    def __format_problem_for_informalizer_global(self, data_message: Message):
        data = data_message.getData()
        problem = "#My problem\n" + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"
        problem = problem + "\n## Informal proof\n"
        return [{"role": "user", "content": problem}]

    def __format_problem_for_informalizer(self, data_message: Message):
        data = data_message.getData()
        problem = "#My Problem\n## Function definition\n```isabelle\n" + data["other formal"] + "```\n\n"
        for count, fun_name in enumerate(data["function names"]):
            problem = problem + "\n```isabelle\n" + \
                      data["formal function definitions"][fun_name] + "\n```\n\n"

        problem = problem + "## Implicit rules\n### Dependent function\n" + data_message.get_dependent_function()
        problem = problem + f"\n### Dependent rules\n" + data_message.get_dependent_rules()

        problem = problem + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"
        problem = problem + "\n## Informal proof\n"
        return [{"role": "user", "content": problem}]

    # proof without newlemma for formalizer
    def format_problem_for_formalizer(self, data_message: Message):
        if self.global_function_definition[0]:
            problem = self.__format_problem_for_formalizer_global(data_message)
        else:
            problem = self.__format_problem_for_formalizer(data_message)
        return problem

    def __format_problem_for_formalizer_global(self, data_message: Message):
        data = data_message.getData()
        problem = "#My problem\n" + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"
        problem = problem + "\n## Informal proof\n" + data_message.get_informal()
        problem = problem + "\n## Formal proof\n"
        return [{"role": "user", "content": problem}]

    def __format_problem_for_formalizer(self, data_message: Message):
        data = data_message.getData()
        problem = "#My Problem\n## Function definition\n```isabelle\n" + data["other formal"] + "```\n\n"
        for count, fun_name in enumerate(data["function names"]):
            problem = problem + "\n```isabelle\n" + \
                      data["formal function definitions"][fun_name] + "\n```\n\n"

        problem = problem + "## Implicit rules\n### Dependent function\n" + data_message.get_dependent_function()
        problem = problem + f"\n### Dependent rules\n" + data_message.get_dependent_rules()
        problem = problem + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"

        problem = problem + "\n## Informal proof\n" + data_message.get_informal()

        problem = problem + "\n## Formal proof\n"
        return [{"role": "user", "content": problem}]

    # proof with newlemma for informal
    def format_problem_for_informal(self, data_message: Message):
        if self.global_function_definition[0]:
            problem = self.__format_problem_for_informal_global(data_message)
        else:
            problem = self.__format_problem_for_informal(data_message)
        return problem

    def __format_problem_for_informal_global(self, data_message: Message):
        data = data_message.getData()

        problem = "#My problem\n" + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"
        problem = problem + "## Informal proof\n"
        return [{"role": "user", "content": problem}]

    def __format_problem_for_informal(self, data_message: Message):
        data = data_message.getData()
        problem = "#My Problem\n## Function definition\n```isabelle\n" + data["other formal"] + "```\n\n"
        for count, fun_name in enumerate(data["function names"]):
            problem = problem + "\n```isabelle\n" + \
                      data["formal function definitions"][fun_name] + "\n```\n\n"

        problem = problem + "## Implicit rules\n### Dependent function\n" + data_message.get_dependent_function()
        problem = problem + f"\n### Dependent rules\n" + data_message.get_dependent_rules()

        problem = problem + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"
        problem = problem + "\n## Informal proof\n"
        return [{"role": "user", "content": problem}]

    # proof with newlemma for indirect_lemma
    def format_indirect_lemma_problem_for_informal(self, data_message: Message):
        if self.global_function_definition[0]:
            problem = self.__format_indirect_lemma_problem_for_informal_global(data_message)
        else:
            problem = self.__format_indirect_lemma_problem_for_informal(data_message)
        return problem

    def __format_indirect_lemma_problem_for_informal_global(self, data_message: Message):
        data = data_message.getData()

        problem = "#My problem\n" + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"

        problem = problem + "\n## Informal proof\n" + data_message.get_informal()
        problem = problem + "\n\n## Required new intermediate lemma\n"

        return [{"role": "user", "content": problem}]

    def __format_indirect_lemma_problem_for_informal(self, data_message: Message):
        data = data_message.getData()
        problem = "#My Problem\n## Function definition\n```isabelle\n" + data["other formal"] + "```\n\n"
        for count, fun_name in enumerate(data["function names"]):
            problem = problem + "\n```isabelle\n" + \
                      data["formal function definitions"][fun_name] + "\n```\n\n"

        problem = problem + "## Implicit rules\n### Dependent function\n" + data_message.get_dependent_function()
        problem = problem + f"\n### Dependent rules\n" + data_message.get_dependent_rules()

        problem = problem + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"

        problem = problem + "\n## Informal proof\n" + data_message.get_informal()

        problem = problem + "\n\n## Required new intermediate lemma\n"
        return [{"role": "user", "content": problem}]

    # proof with newlemma for formal
    def format_problem_for_formal(self, data_message: Message):
        if self.global_function_definition[0]:
            problem = self.__format_problem_for_formal_global(data_message)
        else:
            problem = self.__format_problem_for_formal(data_message)
        return problem

    def __format_problem_for_formal_global(self, data_message: Message):
        data = data_message.getData()

        problem = f"\n### Verified intermediate lemma\n" + format_lemmas_mess(data_message.get_verified_lemmas())

        problem = problem + "#My problem\n" + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"

        problem = problem + "\n## Informal proof\n" + data_message.get_informal()

        problem = problem + "\n## Formal proof\n"
        return [{"role": "user", "content": problem}]

    def __format_problem_for_formal(self, data_message: Message):
        data = data_message.getData()
        problem = "#My Problem\n## Function definition\n```isabelle\n" + data["other formal"] + "```\n\n"
        for count, fun_name in enumerate(data["function names"]):
            problem = problem + "\n```isabelle\n" + \
                      data["formal function definitions"][fun_name] + "\n```\n\n"

        problem = problem + "## Implicit rules\n### Dependent function\n" + data_message.get_dependent_function()
        problem = problem + f"\n### Dependent rules\n" + data_message.get_dependent_rules()
        problem = problem + f"\n### Verified intermediate lemma\n" + format_lemmas_mess(
            data_message.get_verified_lemmas())

        problem = problem + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"

        problem = problem + "\n## Informal proof\n" + data_message.get_informal()

        problem = problem + "\n## Formal proof\n"
        return [{"role": "user", "content": problem}]

    # proof with newlemma for subgoal_lemma
    def format_subgoal_lemma_problem(self, data_message: Message, pre, post, subgoal):
        if self.global_function_definition[0]:
            problem = self.__format_subgoal_lemma_problem_global(data_message, pre, post, subgoal)
        else:
            problem = self.__format_subgoal_lemma_problem(data_message, pre, post, subgoal)
        return problem

    def __format_subgoal_lemma_problem_global(self, data_message: Message, pre, post, subgoal):
        data = data_message.getData()

        problem = "#My problem\n" + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"

        problem = problem + "## Formal proof\n```isabelle\n" + pre + lemma_mask() + post + "\n```\n\n"

        problem = problem + f"""Not proven:{subgoal}
    In Isabelle, this step cannot be verified by sledgehammer because the reasoning rules are either unclear or the reasoning gap is too large. This step should be abstracted into an intermediate lemma, which can then be formally proven in Isabelle.
    \n"""

        problem = problem + "\n## Required new intermediate lemma\n"
        return [{"role": "user", "content": problem}]

    def __format_subgoal_lemma_problem(self, data_message: Message, pre, post, subgoal):
        data = data_message.getData()
        problem = "#My Problem\n## Function definition\n```isabelle\n" + data["other formal"] + "```\n\n"
        for count, fun_name in enumerate(data["function names"]):
            problem = problem + "\n```isabelle\n" + \
                      data["formal function definitions"][fun_name] + "\n```\n\n"

        problem = problem + "## Implicit rules\n### Dependent function\n" + data_message.get_dependent_function()
        problem = problem + f"\n### Dependent rules\n" + data_message.get_dependent_rules()
        problem = problem + f"\n### Verified intermediate lemma\n" + format_lemmas_mess(
            data_message.get_verified_lemmas())

        problem = problem + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"

        problem = problem + "## Formal proof\n```isabelle\n" + pre + lemma_mask() + post + "\n```\n\n"

        problem = problem + f"""Not proven:{subgoal}
    In Isabelle, this step cannot be verified by sledgehammer because the reasoning rules are either unclear or the reasoning gap is too large. This step should be abstracted into an intermediate lemma, which can then be formally proven in Isabelle.
    \n"""

        problem = problem + "\n## Required new intermediate lemma\n"
        return [{"role": "user", "content": problem}]

    # reflection newlemma for subgoal
    def format_reflection_lemma_problem(self, data_message: Message, pre, post, subgoal, invalid_lemma_message, direction=""):
        if self.global_function_definition[0]:
            problem = self.__format_reflection_lemma_problem_global(data_message, pre, post, subgoal, invalid_lemma_message, direction=direction)
        else:
            problem = self.__format_reflection_lemma_problem(data_message, pre, post, subgoal, invalid_lemma_message,direction=direction)
        return problem

    def __format_reflection_lemma_problem_global(self, data_message: Message, pre, post, subgoal, invalid_lemma_message, direction=""):
        problem_ = []
        data = data_message.getData()

        problem = "#My problem\n" + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"

        problem = problem + "## Formal proof\n```isabelle\n" + pre + lemma_mask() + post + "\n```\n\n"

        problem = problem + f"""Not proven:{subgoal}
    In Isabelle, this step cannot be verified by sledgehammer because the reasoning rules are either unclear or the reasoning gap is too large. This step should be abstracted into an intermediate lemma, which can then be formally proven in Isabelle.
    \n"""

        problem_.append({"role": "user", "content": problem})
        problem_.append({"role": "assistant", "content": "\n## Previous lemmas\n"+ invalid_lemma_message +"\n"})
        problem_.append({"role": "user", "content": "\n## Reflection lemma\n"})

        if direction:
            instruction = "Your previous lemma can assist in proving the subgoal in Isabelle, but the lemma itself cannot be proven. It needs to be refined into a provable lemma. You must reflect and provide a new result."
        else:
            instruction = "Your previous lemma does not sufficiently help in proving the subgoal in Isabelle. You must reflect and provide a new result."

        instruction = instruction + self.get_prompt(Role.REFLECTION_LEMMA)
        problem_.append({"role": "user", "content": instruction})

        return problem_

    def __format_reflection_lemma_problem(self, data_message: Message, pre, post, subgoal, invalid_lemma_message, direction=""):
        data = data_message.getData()
        problem = "#My Problem\n## Function definition\n```isabelle\n" + data["other formal"] + "```\n\n"
        for count, fun_name in enumerate(data["function names"]):
            problem = problem + "\n```isabelle\n" + \
                      data["formal function definitions"][fun_name] + "\n```\n\n"

        problem = problem + "## Implicit rules\n### Dependent function\n" + data_message.get_dependent_function()
        problem = problem + f"\n### Dependent rules\n" + data_message.get_dependent_rules()
        problem = problem + f"\n### Verified intermediate lemma\n" + format_lemmas_mess(
            data_message.get_verified_lemmas())

        problem = problem + "## Theorem statement\n```isabelle\n" + data["formal theorem statement"] + "\n```\n\n"

        problem = problem + "## Formal proof\n```isabelle\n" + pre + lemma_mask() + post + "\n```\n\n"

        problem = problem + f"""Not proven:{subgoal}
    In Isabelle, this step cannot be verified by sledgehammer because the reasoning rules are either unclear or the reasoning gap is too large. This step should be abstracted into an intermediate lemma, which can then be formally proven in Isabelle.
    \n"""
        problem = problem + "\n## Previous lemmas\n"+ invalid_lemma_message +"\n"
        problem = problem + "\n## Reflection lemma\n"

        if direction:
            pass

        return [{"role": "user", "content": problem}]

def lemma_mask():
    return "/*@ >>> lemma <<< */"

if __name__ == "__main__":


    parser = argparse.ArgumentParser()
    parser.add_argument('--direct_lemma_examples_path', type=str, default='../prompt/prompt1/direct_lemma/')
    parser.add_argument('--indirect_lemma_examples_path', type=str, default='../prompt/prompt1/indirect_lemma/')
    parser.add_argument('--subgoal_lemma_examples_path', type=str, default='../prompt/prompt1/subgoal_lemma/')
    parser.add_argument('--informal_examples_path', type=str, default='../prompt/prompt1/formal/')
    parser.add_argument('--formal_examples_path', type=str, default='../prompt/prompt1/formal/')
    parser.add_argument('--informalizer_examples_path', type=str, default='../prompt/prompt2/informalizer/')
    parser.add_argument('--formalizer_examples_path', type=str, default='../prompt/prompt2/formalizer/')
    parser.add_argument('--system_messages_path', type=str, default='./system_messages.json')
    parser.add_argument('--global_function_defintion_path', type=str, default='../prompt/function_definition/')
    parser.add_argument('--global_function_definition', type=bool, default=False)

    args = parser.parse_args()
    pr = Prompter(2, global_function_definition=[args.global_function_definition,""], logger=get_logger())
    pr.set_function_attribute("boundedstack")
    pr.read_all_examples(args)
    print(pr.examples)
    print("*******************")
    print(Role.DIRECT_LEMMA.name.lower())
    print(pr.examples[Role.DIRECT_LEMMA.name.lower()])

    print("*******************")
    print(Role.INDIRECT_LEMMA.name.lower())
    print(pr.examples[Role.INDIRECT_LEMMA.name.lower()])

    print("*******************")
    print(Role.SUBGOAL_LEMMA.name.lower())
    print(pr.examples[Role.SUBGOAL_LEMMA.name.lower()])

    print("*******************")
    print(Role.INFORMAL.name.lower())
    print(pr.examples[Role.INFORMAL.name.lower()])

    print("*******************")
    print(Role.FORMAL.name.lower())
    print(pr.examples[Role.FORMAL.name.lower()])

    print("*******************")
    print(Role.INFORMALIZER.name.lower())
    print(pr.examples[Role.INFORMALIZER.name.lower()])

    print("**********_______________*********")
    print(Role.FORMALIZER.name.lower())

    print(pr.examples[Role.FORMALIZER.name.lower()])


    print("+++++++++++++++++++++++++++++")
    print(len(pr.get_examples("cc", Role.SUBGOAL_LEMMA)))
    print(pr.get_examples("cc", Role.SUBGOAL_LEMMA))

    pr.read_all_prompts(args)
    print(pr.prompts)
    print(pr.get_prompt(Role.SUBGOAL_LEMMA))

    print((1,2)[0])

    print(pr.function_definitions)

    cs = [False,""]
    cs[1] = "gdfgdf"
    print(cs[1])








