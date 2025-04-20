import argparse
import os
import time
import utils
from Chromadb.ROLE_COLLECTION import Role_collection
from utils import lemma_to_theorem, theorem_to_lemma
from Chromadb.Collection import Collection

from generator.Generator import Generator
from generator.Key import Key
from generator.LLM import LLM
from generator.Prompter import Prompter
from generator.Role import Role
from message.Message import Message
from utils import read_thy, write_thy
from verify.Checker import Checker
from verify.Isabelle import Isabelle
from verify.Rule import Rule
from verify.Verifier import Verifier


class Proof_method():
    def __init__(self, generator:Generator, checker:Checker, verifier:Verifier, collection:Collection=None, logger=None):
        self.__generator = generator
        self.__checker = checker
        self.__verifier = verifier
        self.logger = logger
        self.__collection = collection

    def get_collection(self):
        return self.__collection

    def get_verifier(self):
        return self.__verifier

    def get_checker(self):
        return self.__checker

    def get_generator(self):
        return self.__generator

    def method(self, data_message:Message, args):
        generator = self.get_generator()
        prompter = generator.get_prompter()
        count = 0
        data_message.set_all_verified_lemmas(self.get_collection().get_all_lemmas(Role_collection.VERIFIED_LEMMA1, metadata_class=args.dataset))
        data_message.set_verified_lemmas(self.get_collection().query_similar_lemmas(Role_collection.VERIFIED_LEMMA1,
                                                                         data_message.getData()[
                                                                             "formal theorem statement"], metadata_class=args.dataset))

        utils.create_lemmas_theory_library(args, data_message.get_all_verified_lemmas(), self.get_checker())

        for i in range(args.run_count):

            self.logger.info(f"\n\n--------Informalizer-------\n\n")
            informal_problem = prompter.format_problem_for_informalizer(data_message)
            informals = generator.request_informalizer(data_message, informal_problem, Role.INFORMALIZER, max_tokens=600, n=2)

            self.logger.info(f"\n\n--------{len(informals)}-------\n\n")
            if not informals:
                continue

            for informal_count, informal in enumerate(informals):
                self.logger.info("--------informalizer-------\n\n")
                data_message.init_informal_and_formal()

                data_message.set_informal(informal)
                self.logger.info(informal)
                self.logger.info("\n\n--------formalizer------\n\n")
                formal_problem = prompter.format_problem_for_formalizer(data_message)
                formals = generator.request_formalizer(data_message, formal_problem, Role.FORMALIZER, max_tokens=600, n=3)
                if not formals:
                    continue
                self.logger.info(f"\n\n--------{len(formals)}-------\n\n")

                for formal_count, formal in enumerate(formals):
                    count = count + 1

                    self.logger.info("\n\n--------formal-------\n\n")
                    self.logger.info(formal)
                    if "" == formal:
                        continue


                    formal = self.get_checker().check_nitpick_syntax_all_subgoal(formal, args.theory_path, data_message)
                    if "" == formal:
                        continue

                    self.logger.info("_________________检查路径_____________________")
                    isproof, method, formal = self.get_checker().check_path_for_formal(args.theory_path, data_message, args, formal)
                    if not isproof:
                        self.logger.info("_____________check_path____错误径_____________________")
                        continue

                    isproof, info, formal = self.get_verifier().verify(args.theory_path, data_message, args, formal)
                    formal = formal.replace(data_message.getData()["theorem name"] + ".", " ")
                    if data_message.get_property() == "lemma":
                        formal = theorem_to_lemma(formal)
                    data_message.set_final_formal_proof(formal)

                    if isproof:
                        data_message.set_is_verified(True)
                        save_true_trace(args.theory_path, args.true_proof_trace_path, data_message)
                        utils.write_valid(data_message, args.true_proof_data_path, "valid_",
                                                formal)
                        utils.save_name(args.true_proof_data_path_dataset, data_message.getData()["theorem name"], 0, count, self.logger)
                        return True, formal
                    else:
                        save_false_trace(args.false_proof_trace_path, informal, formal, data_message,
                                         args.time, info, count, self.logger)
                        continue

        utils.write_valid(data_message, args.true_proof_data_path, "all_invalid_", data_message.all_formal_proof(), all_count=count)
        data_message.set_is_verified(False)
        return False, ""


def save_true_theory(true_proof_data_path, theory_path, name):
    thy = read_thy(theory_path, name)
    write_thy(true_proof_data_path, name, thy)

def save_true_trace(theory_path, true_proof_trace_path, data_message:Message):
    data = data_message.getData()
    thy = read_thy(theory_path, data["theorem name"])
    thy = thy + "\n## Informal proof\n" + data_message.get_informal() +"\n"
    write_thy(true_proof_trace_path, data["theorem name"], thy)



def save_false_trace(path, informal, formal, data_message, time, info, count, logger):
    data = data_message.getData()
    logger.info("----------save_false_trace------------")
    logger.info(f'{path}/{data["theorem name"]}-{time}.txt')
    logger.info("----------------------")
    file = None

    try:
        file = open(f'{path}/{data["theorem name"]}-{time}.txt', 'a', encoding='utf-8')
        file.write(
            f'******************** {info} ******  count = {count}***************\n#### informal\n{informal}\n\n## formal\n{formal}\n\n\n')
    except Exception as e:
        logger.info(f'{path}/{data["theorem name"]}-{time}.txt---- {e}')
    finally:
        if file:
            file.flush()
            file.close()






if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--direct_lemma_examples_path', type=str, default='../prompt/prompt1/direct_lemma/')
    parser.add_argument('--indirect_lemma_examples_path', type=str, default='../prompt/prompt1/indirect_lemma/')
    parser.add_argument('--subgoal_lemma_examples_path', type=str, default='../prompt/prompt1/subgoal_lemma/')
    parser.add_argument('--informal_examples_path', type=str, default='../prompt/prompt1/informal/')
    parser.add_argument('--formal_examples_path', type=str, default='../prompt/prompt1/formal/')
    parser.add_argument('--informalizer_examples_path', type=str, default='../prompt/prompt2/informalizer/')
    parser.add_argument('--formalizer_examples_path', type=str, default='../prompt/prompt2/formalizer/')
    parser.add_argument('--system_messages_path', type=str, default='../generator/system_messages.json')
    parser.add_argument('--global_function_defintion_path', type=str, default='../prompt/function_definition/')
    parser.add_argument('--global_function_definition', type=bool, default=True)
    parser.add_argument('--keys_path', type=str, default='../data/keys')

    parser.add_argument('--data_path', type=str, default=f"../data/")

    parser.add_argument('--theory_path', type=str, default=f"../output/without_newlemma/theory")
    parser.add_argument('--true_proof_data_path', type=str, default=f"../output/without_newlemma/true")
    parser.add_argument('--true_proof_trace_path', type=str, default=f"../output/without_newlemma/trace")
    parser.add_argument('--false_proof_trace_path', type=str, default=f"../output/without_newlemma/false")
    parser.add_argument('--lemmas_theory_library', type=str, default=f"../output/with_newlemma")


    parser.add_argument('--run_count', type=int, default=2)

    args = parser.parse_args()

    logger = utils.get_logger()
    args.logger = logger

    api_base = "https://api.xiaoai.plus/v1"

    key: Key = Key(args.keys_path)
    llm = LLM(key=key , model='gpt-3.5-turbo', logger = logger, api_base=api_base)
    prompter = Prompter(2, global_function_definition=[args.global_function_definition, ""],logger=logger)
    prompter.read_all_prompts(args)
    prompter.read_all_examples(args)

    generator = Generator(llm=llm, prompter=prompter, logger=logger)

    isabelle = Isabelle(logger=logger)
    checker = Checker(isabelle=isabelle, logger=logger)

    verifier = Verifier(isabelle=isabelle, logger=logger)

    ruler = Rule(isabelle=isabelle)

    proof_method = Proof_method(generator=generator, checker=checker, verifier=verifier, logger=logger)

    #datasets = ["stack", "boundedstack", "FIFO_queue", "priority_queue"]
    datasets = ["priority_queue"]

    theory_path = args.theory_path
    true_proof_data_path = args.true_proof_data_path
    args.time = time.strftime('%Y-%m-%d-%H-%M-%S', time.localtime())
    if not os.path.isdir(f'{args.false_proof_trace_path}/{args.time}'):
        args.false_proof_trace_path = f'{args.false_proof_trace_path}/{args.time}'
        os.mkdir(args.false_proof_trace_path)

    utils.config_formal_definition(args)

    try:
        for dataset in datasets:
            args.dataset = dataset
            prompter.set_function_attribute(dataset)
            logger.info(f"-----------------------数据集{dataset}--------------------------------")
            true_proof_data_path_dataset = true_proof_data_path + '/' + dataset
            args.true_proof_data_path_dataset = true_proof_data_path_dataset
            if not os.path.isdir(true_proof_data_path_dataset):
                os.mkdir(true_proof_data_path_dataset)

            verified_names = []
            if os.path.exists(true_proof_data_path_dataset + '/name.txt'):
                verified_names = utils.read_name(true_proof_data_path_dataset)

            datas = utils.read_dir(args.data_path + dataset + "/", 'json')

            for count, data in enumerate(datas):

                logger.info(f"-----------------------开始证明数据 theory {data['theorem name']} --------------------------------")

                data_message = Message(data=data, iterations=0, class_name=dataset, theorem_name=data["theorem name"])
                data_message.set_lemmas_theory_library(args.lemmas_theory_library)
                data_message.set_lemmas_package(f"\"../../{dataset}\"")

                isproof = False
                logger.info(f'________________verified_names____________________\n')
                logger.info(f'________________{verified_names}____________________')

                if data["theorem name"] in verified_names:
                    logger.info(f'theory {data["theorem name"]} verified')
                    continue

                if not os.path.isdir(theory_path + f'/{data["theorem name"]}'):
                    os.mkdir(theory_path + f'/{data["theorem name"]}')
                args.theory_path = theory_path + f'/{data["theorem name"]}'

                if not os.path.isdir(true_proof_data_path_dataset + f'/{data["theorem name"]}'):
                    os.mkdir(true_proof_data_path_dataset + f'/{data["theorem name"]}')
                args.true_proof_data_path = true_proof_data_path_dataset + f'/{data["theorem name"]}'

                logger.info("\n\n--------rules-------\n\n")
                rules, user_rules, user_rules_type = ruler.all_rules(data)
                format_rule = utils.format_rules(rules, {})
                format_user_rules = utils.format_rules(user_rules, user_rules_type)
                data_message.set__dependent_function(format_rule)
                data_message.set_dependent_rules(format_user_rules)
                """data["rules"] = format_rule
                data["user_rules"] = format_user_rules"""
                logger.info(format_rule)
                logger.info(format_user_rules)

                """isproof, method, formal = nostructureproof.run(data, args)
                if isproof:
                    logger.info(f"{data['theo rem name']}--验证成功---")
                    continue"""


                #args.iterations = 2
                isproof, formal = proof_method.method(data_message, args)
                if isproof:
                    logger.info(f"{data['theorem name']}--验证成功---")

    except Exception as e:

        utils.write_valid(data_message, args.true_proof_data_path, "all_invalid_",  data_message.all_formal_proof())

        logger.info(e)
        logger.info("异常")
    finally:
        isabelle.session_stop(isabelle.session_id)






