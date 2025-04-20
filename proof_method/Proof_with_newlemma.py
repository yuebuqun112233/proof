import argparse
import copy
import os
import sys
import time
import utils
from message.Lemma import Lemma

from utils import lemma_to_theorem, theorem_to_lemma
from Chromadb.ROLE_COLLECTION import Role_collection

#from Controller.Subgoal_lemma import Subgoal_lemma
from Chromadb.Collection import Collection
from generator.Generator import Generator
from generator.Key import Key
from generator.LLM import LLM
from generator.Prompter import Prompter, read_dir_
from generator.Role import Role
from message.Message import Message
from proof_method import Proof_without_newlemma
from utils import format_lemmas_mess, read_thy, write_thy
from verify.Checker import Checker
from verify.Isabelle import Isabelle
from verify.Rule import Rule
from verify.Verifier import Verifier


def unverified_valid_lemmas_for_formal(formal, unverified_lemmas):
    unverified_valid_lemmas = {}
    unverified_lemmas_ = {}
    for lemma_name, lemma in unverified_lemmas.items():
        if lemma_name + " " in formal or lemma_name + ")" in formal or  lemma_name + "(" in formal:
            unverified_valid_lemmas[lemma_name] = lemma
        else:
            unverified_lemmas_[lemma_name] = lemma
    unverified_lemmas = unverified_lemmas_
    return unverified_valid_lemmas


def lemmas_data_synthesis(data_message:Message, lemmas, collection:Collection):

    if lemmas == {}:
        return {}
    lemma_datas_message = []

    for lemma_name, lemma in lemmas.items():
        lemma_data = copy.copy(data_message.getData())

        lemma_data["formal theorem statement"] = lemma_to_theorem(lemma.get_lemma_statement())
        lemma_data["theorem name"] = lemma_name
        lemma_data_message:Message = Message(data=lemma_data, class_name=data_message.get_class(), theorem_name=data_message.get_theorem_name())
        lemma_data_message.set_property("lemma")
        lemma_data_message.set_stage(lemma.get_stage())
        lemma_data_message.set_lemmas_theory_library(data_message.get_lemmas_theory_library())
        lemma_data_message.set_lemmas_package(data_message.get_lemmas_package())
        lemma_data_message.set__dependent_function(data_message.get_dependent_function())
        lemma_data_message.set_dependent_rules(data_message.get_dependent_rules())
        lemma_data_message.set_iterations(data_message.get_iterations() - 1)
        lemma_data_message.set_public_rep(data_message.get_public_rep())
        lemma_data_message.set_private_rep(data_message.get_private_rep())
        """self.logger.info(f"------------midlemma name -- {lemma_name}-----------------\n")
        self.logger.info(lemma_data_message.to_string())"""
        lemma_datas_message.append(lemma_data_message)
        print("添加引理到problem vector store")
        collection.add(collection_name=Role_collection.PROBLEM, document=lemma_data["formal theorem statement"],
                       metadatas=utils.metadata_template_problem(metadata_class=data_message.get_class(),
                                                                 metadata_theorem=data_message.get_theorem_name(), id=lemma_data["theorem name"]),
                       id=lemma_data["theorem name"])
    return lemma_datas_message




def formal_proof_conbine_lemma(formal:str, current_property, lemmas_data_message):
    final_formal = ""

    for lemma_data_message in lemmas_data_message:
        if lemma_data_message.get_is_verified():
            final_formal = final_formal + lemma_data_message.get_final_formal_proof() + "\n\n"
        else:
            final_formal = final_formal + theorem_to_lemma(lemma_data_message.getData()["formal theorem statement"]) + " sorry\n\n"

    if current_property == "lemma":
        return final_formal + theorem_to_lemma(formal)
    else:
        return final_formal + formal


def del_uvvalid_from_uvlemmas(unverified_valid_lemmas, unverified_lemmas):
    for key, value in unverified_valid_lemmas.items():
        if key in unverified_lemmas.keys():
            del unverified_lemmas[key]



def remove_lemma_problem_collection(lemmas, collection):
    for name, lemma in lemmas.items():
        collection.delete_id(Role_collection.PROBLEM, name)



class Proof_method():
    def __init__(self, generator:Generator, checker:Checker, verifier:Verifier, collection:Collection=None, logger=None):
        self.__generator = generator
        self.__checker = checker
        self.__verifier = verifier
        self.logger = logger
        self.__without_newlemma_proof_method:Proof_without_newlemma.Proof_method = Proof_without_newlemma.Proof_method(
            generator=generator,
            checker=checker,
            verifier=verifier,
            collection=collection,
            logger=logger
        )
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

        for i in range(args.run_count):
            data_message.set_all_verified_lemmas(self.get_collection().get_all_lemmas(Role_collection.VERIFIED_LEMMA2,  metadata_class=args.dataset))
            self.logger.info(f"\n\n--------data_message.set_all_verified_lemmas-------\n\n")
            self.logger.info(data_message.get_all_verified_lemmas())
            data_message.set_verified_lemmas(self.get_collection().query_similar_lemmas(Role_collection.VERIFIED_LEMMA2, data_message.getData()[
                                                                             "formal theorem statement"], metadata_class=args.dataset))
            self.logger.info(f"\n\n--------data_message.set_verified_lemmas-------\n\n")
            self.logger.info(data_message.get_verified_lemmas())

            utils.create_lemmas_theory_library(args, data_message.get_all_verified_lemmas(), self.get_checker())

            data_message.init()
            self.logger.info(f"\n\n--------Informal-------\n\n")
            informal_problem = prompter.format_problem_for_informal(data_message)
            informals = generator.request_informal(data_message, informal_problem, Role.INFORMAL, max_tokens=600, n=2)

            self.logger.info(f"\n\n--------{len(informals)}-------\n\n")
            if not informals:
                continue

            for informal_count, informal in enumerate(informals):
                self.logger.info("--------informal-------\n\n")
                data_message.init_informal_and_formal()
                data_message.init()
                data_message.set_informal(informal)
                self.logger.info(informal)

                self.logger.info("\n\n--------indirect lemma------\n\n")
                indirect_lemma_problem = prompter.format_indirect_lemma_problem_for_informal(data_message)
                lemmas, stage = generator.request_indirct_lemma(data_message, indirect_lemma_problem, Role.INDIRECT_LEMMA, max_tokens=450, n=4)
                lemmas = self.get_checker().check_nitpick_syntax_for_lemmas(lemmas, args.theory_path, data_message)
                """if lemmas is None:
                    continue"""
                """lemmas = {}
                stage = Role.INDIRECT_LEMMA"""
                data_message.add_unverified_lemmas(lemmas, stage)


                self.logger.info("\n\n--------formal------\n\n")
                formal_problem = prompter.format_problem_for_formal(data_message)
                formals = generator.request_formal(data_message, formal_problem, Role.FORMAL, max_tokens=600, n=3, number_examples=1)
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
                        self.logger.info("_____________check_path____错误路径_____________________")
                        continue
                    subgoal_lemma = Proof_method.Subgoal_lemma(outer_instance=self)

                    isproof, info, formal = self.get_verifier().verify(args.theory_path, data_message, args, formal, subgoal_lemma=subgoal_lemma)
                    formal = formal.replace(data_message.getData()["theorem name"] + ".", " ")

                    unverified_valid_lemmas = unverified_valid_lemmas_for_formal(formal, data_message.get_unverified_lemmas())
                    #del_uvvalid_from_uvlemmas(unverified_valid_lemmas, data_message.get_unverified_lemmas())
                    data_message.add_unverified_valid_lemmas(unverified_valid_lemmas)

                    lemmas_data_message = lemmas_data_synthesis(data_message, unverified_valid_lemmas, self.get_collection())
                    self.logger.info("_____________开始证明unverified_valid_lemmas_____________________")
                    self.logger.info(unverified_valid_lemmas)
                    isuseful = self.lemmas_method(lemmas_data_message, args, "valid")
                    #remove_lemma_problem_collection(unverified_valid_lemmas, self.get_collection())

                    lemmas_data_message1 = lemmas_data_synthesis(data_message, data_message.get_unverified_lemmas(), self.get_collection())
                    self.logger.info("_____________开始证明unverified_lemmas_____________________")
                    self.logger.info(data_message.get_unverified_lemmas())
                    self.lemmas_method(lemmas_data_message1, args, "invalid")
                    #remove_lemma_problem_collection(data_message.get_unverified_lemmas(), self.get_collection())

                    final_formal_with_lemmas = formal_proof_conbine_lemma(formal, data_message.get_property(), lemmas_data_message)
                    for lemma_data_message in lemmas_data_message:
                        if lemma_data_message.get_rename_flag():
                            formal = formal.replace(lemma_data_message.getData()["theorem name"], lemma_data_message.getData()["theorem name"] + "_rename",1)
                            final_formal_with_lemmas.replace(lemma_data_message.getData()["theorem name"], lemma_data_message.getData()["theorem name"] + "_rename",1)
                    data_message.set_final_formal_proof(final_formal_with_lemmas)

                    if isproof == True and isuseful == True:
                        data_message.set_is_verified(True)


                        utils.write_valid(data_message, args.true_proof_data_path, "valid_", data_message.get_final_formal_proof())
                        utils.save_name(args.true_proof_data_path_dataset, data_message.getData()["theorem name"], 0, count, self.logger)
                        return True, formal, final_formal_with_lemmas
                    else:
                        save_false_trace(args.false_proof_trace_path, informal, formal, data_message,
                                         args.time, info, count, self.logger)
                        continue
        all_final_formal = data_message.all_formal_proof()
        utils.write_valid(data_message, args.true_proof_data_path, "all_invalid_", all_final_formal, all_count=count)
        data_message.set_is_verified(False)
        return False, "", ""

    def lemmas_method(self, lemmas_data_message, args, key):
        flag = True
        for lemma_data_message in lemmas_data_message:
            isuseful, formal, formal_with_lemmas = self.lemma_method(lemma_data_message, args)

            collection.delete_id(collection_name=Role_collection.PROBLEM, id=lemma_data_message.getData()["theorem name"])

            if isuseful:
                #落库保存lemma

                args.logger.info("-----落库保存lemma---VERIFIED_LEMMA-")

                collection_name = Role_collection.VERIFIED_LEMMA2
                name = lemma_data_message.getData()["theorem name"]
                args.logger.info(name)
                lemma = theorem_to_lemma(lemma_data_message.getData()["formal theorem statement"])
                args.logger.info(lemma)
                formal = theorem_to_lemma(formal)
                args.logger.info(formal)
                if self.get_collection().get_id(collection_name, id=lemma_data_message.getData()["theorem name"])['ids'] != []:
                    args.logger.info(f"-----引理{name} 已经存在--")

                    lemma_data_message.set_rename_flag(True)
                    lemma = lemma.replace(name, name+"_rename",1)
                    formal = formal.replace(name, name+'_rename',1)
                    name = name + "_rename"
                index = collection.count(collection_name)
                metadatas = utils.metadata_template_proof(lemma_data_message.get_class(), lemma_data_message.get_theorem_name(), proof=formal, stage=lemma_data_message.get_stage(),index=index+1)
                self.get_collection().add(collection_name=collection_name, document=lemma, metadatas=metadatas, id=name)
            else:
                if key == "valid":
                    args.logger.info("-----落库保存lemma---UNVERIFIED_VALID_LEMMA-")
                    collection_name_ = Role_collection.UNVERIFIED_VALID_LEMMA2
                elif key == "invalid":
                    args.logger.info("-----落库保存lemma---UNVERIFED_LEMMA-")
                    collection_name_ = Role_collection.UNVERIFED_LEMMA2
                args.logger.info("-----落库保存lemma---UNVERIFED_LEMMA-   UNVERIFIED_VALID_LEMMA--")
                lemma = theorem_to_lemma(lemma_data_message.getData()["formal theorem statement"])
                metadatas = utils.metadata_template(lemma_data_message.get_class(),
                                                          lemma_data_message.get_theorem_name(), stage=lemma_data_message.get_stage())
                self.get_collection().add(collection_name=collection_name_, document=lemma, metadatas=metadatas,
                                          id=lemma_data_message.getData()["theorem name"])
                flag = False
        return flag

    def lemma_method(self, lemma_data_message: Message, args):
        self.logger.info(f"-------midlemma_data----nitpick check---------------------")
        lemma_data = lemma_data_message.getData()
        is_ok = self.get_checker().check_nitpick_syntax_for_lemma(lemma_data["theorem name"],
                                                                  lemma_data["formal theorem statement"],
                                                                  args.theory_path, lemma_data_message)
        if not is_ok:
            return False, "", ""



        if lemma_data_message.get_iterations() > 0:
            args.logger.info(f"----{lemma_data_message.get_iterations()}-先尝试无引理证明----")
            isuseful, formal = self.__without_newlemma_proof_method.method(lemma_data_message, args)
            if isuseful:
                return isuseful, formal, formal
            args.logger.info(f"---{lemma_data_message.get_iterations()}--继续迭代证明----")
            isuseful, formal, formal_with_lemmas = self.method(lemma_data_message, args)
            return isuseful, formal, formal_with_lemmas
        else:
            args.logger.info(f"---{lemma_data_message.get_iterations()}-----最后尝试无引理证明----")
            isuseful, formal = self.__without_newlemma_proof_method.method(lemma_data_message, args)
            return isuseful, formal, formal

    class Subgoal_lemma():
        def __init__(self, outer_instance):
            self.__outer_instance = outer_instance
            self.__generator = outer_instance.get_generator()
            self.__checker = outer_instance.get_checker()
            self.__isabelle = outer_instance.get_checker().get_isabelle()
            self.logger = outer_instance.logger
            self.__subgoal = ""
            self.__collection:Collection = outer_instance.get_collection()

        def get_collection(self):
            return self.__collection

        def set_subgoal(self, subgoal):
            self.__subgoal = subgoal

        def get_subgoal(self):
            return self.__subgoal

        def get_isabelle(self):
            return self.__isabelle

        def get_generator(self):
            return self.__generator

        def get_checker(self):
            return self.__checker

        def __get_prompter(self):
            return self.get_generator().get_prompter()

        def verify_subgoal_with_lemma(self, theory_path, data_message: Message, pre, post, args):
            subgoal = self.get_isabelle().get_proof_state(pre, post, data_message, theory_path)
            self.logger.info("----subgoal-----")
            self.logger.info(subgoal)
            self.set_subgoal(subgoal)

            problem = self.__get_prompter().format_subgoal_lemma_problem(data_message, pre, post, subgoal)

            self.logger.info("-----problem------")
            self.logger.info(problem)

            lemmas, stage = self.get_generator().request_subgoal_lemma(data_message, problem, Role.SUBGOAL_LEMMA,
                                                                       max_tokens=400, n=4, number_examples=2)

            lemmas = self.get_checker().check_nitpick_syntax_for_lemmas(lemmas, theory_path, data_message)
            if lemmas == {}:
                return False, "无引理生成", "", {}, {}
            self.logger.info(lemmas)
            #data_message.add_unverified_lemmas(lemmas, stage)

            lemmas = utils.lemmas_obj(lemmas, stage)


            thy = utils.get_theory_with_lemmas(data_message, pre,
                                         f"\nsledgehammer [prover=cvc4 vampire verit e spass z3 zipperposition] sorry\n",
                                               post, verified_midlemmas=data_message.get_all_verified_lemmas(),
                                               unverified_midlemmas=utils.jsonmerge(data_message.get_unverified_lemmas(), copy.copy(lemmas)))
            write_thy(theory_path, data_message.getData()["theorem name"], thy)
            self.logger.info(thy)

            isproof, method, formal = self.get_isabelle().run_sledgehammer(theory_path, data_message, pre, post, args, subgoal_lemmas=copy.copy(lemmas))

            valid_lemmas = {}
            lemmas_ = copy.copy(lemmas)
            if isproof:
                self.logger.info("Subgoal_lemma.verify_subgoal_with_lemma成功")
                self.logger.info("------------------method---------------")
                self.logger.info(method)
                for name, lemma in lemmas.items():
                    if lemma.get_name() + " " in method or lemma.get_name() + ")" in method or  lemma.get_name() + "(" in method:
                        valid_lemmas[name] = lemma
                        del lemmas_[name]
            return isproof, method, formal, valid_lemmas, lemmas_

        def reflection_subgoal_lemma(self, theory_path, data_message: Message, pre, post, args, direction="", lemmas=None):
            if not lemmas:
                return False, "没有传入lemmas", ""
            for name, lemma in lemmas.items():
                self.get_collection().add(collection_name=Role_collection.PROBLEM, document=lemma.get_lemma_statement(),
                               metadatas=utils.metadata_template_problem(metadata_class=data_message.get_class(), metadata_theorem=data_message.get_theorem_name(), id=name),
                               id=name)

            invalid_lemma_message = ""
            self.logger.info("========list_lemmas========")
            list_lemmas = utils.list_lemmas_name(lemmas)
            self.logger.info(f"========{list_lemmas}========")
            for lemma_message in data_message.get_lemma_messages():
                for name in list_lemmas:
                    if name in lemma_message:
                        invalid_lemma_message = invalid_lemma_message + lemma_message + "\n"
                        break
            self.logger.info("========invalid_lemma_message========")
            self.logger.info(invalid_lemma_message)
            problem = self.__get_prompter().format_reflection_lemma_problem(data_message, pre, post, self.get_subgoal(),
                                                                            invalid_lemma_message, direction=direction)

            self.logger.info("-----problem------")
            self.logger.info(problem)
            lemmas_, stage = self.get_generator().request_reflection_lemma(data_message, problem, Role.REFLECTION_LEMMA,
                                                                          max_tokens=400, n=4, number_examples=2)

            for name, lemma in lemmas.items():
                self.get_collection().delete_id(collection_name=Role_collection.PROBLEM, id=name)

            lemmas_ = self.get_checker().check_nitpick_syntax_for_lemmas(lemmas_, theory_path, data_message)
            if lemmas_ == {}:
                return False, "新中间引理无效", ""
            data_message.add_unverified_lemmas(lemmas_, stage)

            thy = utils.get_theory_with_lemmas(data_message, pre,
                                         f"\nsledgehammer [prover=cvc4 vampire verit e spass z3 zipperposition] sorry\n",
                                               post, verified_midlemmas=data_message.get_all_verified_lemmas(),
                                               unverified_midlemmas=data_message.get_unverified_lemmas())
            write_thy(theory_path, data_message.getData()["theorem name"], thy)
            self.logger.info(thy)

            isproof, method, formal = self.get_isabelle().run_sledgehammer(theory_path, data_message, pre, post, args)

            if isproof:
                self.logger.info("Subgoal_lemma.reflection_subgoal_lemma成功")
            return isproof, method, formal

        def verify_valid_lemmas(self, data_message, lemmas, args):
            if lemmas == {}:
                return {}
            self.logger.info("-----------------verify_valid_lemmas------------------")
            lemmas_ = {}
            self.logger.info("-----------------lemmas_data_synthesis------------------")
            lemmas_data_message = lemmas_data_synthesis(data_message, lemmas, self.get_collection())
            isuseful = self.__outer_instance.lemmas_method(lemmas_data_message, args, key="valid")
            if not isuseful:
                for lemma_data_message in lemmas_data_message:
                    if not lemma_data_message.get_is_verified():
                        name = lemma_data_message.getData()["theorem name"]
                        lemmas_[name] = lemmas[name]
                        self.logger.info("-----------------没有被证明------------------")
                        self.logger.info(f"-----------------{lemmas[name]}------------------")
            return lemmas_




def save_true_theory(true_proof_data_path, theory_path, name):
    thy = read_thy(theory_path, name)
    write_thy(true_proof_data_path, name, thy)

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



"""if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--direct_lemma_examples_path', type=str, default='../prompt/prompt1/direct_lemma/')
    parser.add_argument('--indirect_lemma_examples_path', type=str, default='../prompt/prompt1/indirect_lemma/')
    parser.add_argument('--subgoal_lemma_examples_path', type=str, default='../prompt/prompt1/subgoal_lemma/')
    parser.add_argument('--reflection_lemma_examples_path', type=str, default='../prompt/prompt1/reflection_lemma/')
    parser.add_argument('--informal_examples_path', type=str, default='../prompt/prompt1/informal/')
    parser.add_argument('--formal_examples_path', type=str, default='../prompt/prompt1/formal/')
    parser.add_argument('--informalizer_examples_path', type=str, default='../prompt/prompt2/informalizer/')
    parser.add_argument('--formalizer_examples_path', type=str, default='../prompt/prompt2/formalizer/')
    parser.add_argument('--system_messages_path', type=str, default='../generator/system_messages.json')
    parser.add_argument('--global_function_defintion_path', type=str, default='../prompt/function_definition/')
    parser.add_argument('--global_function_definition', type=bool, default=True)
    parser.add_argument('--keys_path', type=str, default='../data/keys')

    parser.add_argument('--data_path', type=str, default=f"../data/")

    parser.add_argument('--theory_path', type=str, default=f"../output/with_newlemma/theory")
    parser.add_argument('--true_proof_data_path', type=str, default=f"../output/with_newlemma/true")
    parser.add_argument('--true_proof_trace_path', type=str, default=f"../output/with_newlemma/trace")
    parser.add_argument('--false_proof_trace_path', type=str, default=f"../output/with_newlemma/false")
    parser.add_argument('--lemmas_theory_library', type=str, default=f"../output/with_newlemma")

    parser.add_argument('--run_count', type=int, default=1)

    args = parser.parse_args()

    logger = utils.get_logger()
    args.logger = logger

    api_base = "https://api.xiaoai.plus/v1"

    key: Key = Key(args.keys_path)
    llm = LLM(key=key, model='gpt-3.5-turbo', logger=logger, api_base=api_base)
    prompter = Prompter(2, global_function_definition=[args.global_function_definition, ""], logger=logger)
    prompter.read_all_prompts(args)
    prompter.read_all_examples(args)
    key1 = Key("../chromadb/key")
    embedding_model_name = "text-embedding-3-small"
    collection = Collection(key=key1, api_base=api_base, embedding_model_name=embedding_model_name)

    generator = Generator(llm=llm, prompter=prompter, logger=logger, collection=collection)

    isabelle = Isabelle(logger=logger)
    checker = Checker(isabelle=isabelle, logger=logger)
    
    verifier = Verifier(isabelle=isabelle, logger=logger, collection=collection, checker=checker)

    ruler = Rule(isabelle=isabelle)

    proof_method = Proof_method(generator=generator, checker=checker, verifier=verifier, logger=logger,
                                collection=collection)

    # datasets = ["stack", "boundedstack", "FIFO_queue", "priority_queue"]
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
                logger.info(
                    f"-----------------------开始证明数据 theory {data['theorem name']} --------------------------------")

                data_message = Message(data=data, iterations=2, class_name=dataset, theorem_name=data["theorem name"])
                data_message.set_lemmas_theory_library(args.lemmas_theory_library)
                data_message.set_lemmas_package(f"\"../../{dataset}\"")
                lemmas = {"distinct_alist_of_push":Lemma(name="distinct_alist_of_push",lemma_statement="lemma distinct_alist_of_push:
  assumes a1: "distinct (map fst xs)"
    and a2: "sorted (map snd xs)"
    and a3: "k \<notin> set (values (Abs_pq xs))"
  shows "distinct (map fst (alist_of (push k p (Abs_pq xs))))" ", stage=Role.REFLECTION_LEMMA)}
                proof_method.Subgoal_lemma(proof_method).verify_valid_lemmas(data_message=data_message, lemmas=lemmas, args=args)
    except Exception as e:

        utils.write_valid(data_message, args.true_proof_data_path, "all_invalid_",  data_message.all_formal_proof())
        logger.info(e)
        logger.info("异常")
    finally:
        isabelle.session_stop(isabelle.session_id)"""


def proof_with_newlemma():
    parser = argparse.ArgumentParser()
    parser.add_argument('--direct_lemma_examples_path', type=str, default='../prompt/prompt1/direct_lemma/')
    parser.add_argument('--indirect_lemma_examples_path', type=str, default='../prompt/prompt1/indirect_lemma/')
    parser.add_argument('--subgoal_lemma_examples_path', type=str, default='../prompt/prompt1/subgoal_lemma/')
    parser.add_argument('--reflection_lemma_examples_path', type=str, default='../prompt/prompt1/reflection_lemma/')
    parser.add_argument('--informal_examples_path', type=str, default='../prompt/prompt1/informal/')
    parser.add_argument('--formal_examples_path', type=str, default='../prompt/prompt1/formal/')
    parser.add_argument('--informalizer_examples_path', type=str, default='../prompt/prompt2/informalizer/')
    parser.add_argument('--formalizer_examples_path', type=str, default='../prompt/prompt2/formalizer/')
    parser.add_argument('--system_messages_path', type=str, default='../generator/system_messages.json')
    parser.add_argument('--global_function_defintion_path', type=str, default='../prompt/function_definition/')
    parser.add_argument('--global_function_definition', type=bool, default=True)
    parser.add_argument('--keys_path', type=str, default='../data/keys')

    parser.add_argument('--data_path', type=str, default=f"../data/")

    parser.add_argument('--theory_path', type=str, default=f"../output/with_newlemma/theory")
    parser.add_argument('--true_proof_data_path', type=str, default=f"../output/with_newlemma/true")
    parser.add_argument('--true_proof_trace_path', type=str, default=f"../output/with_newlemma/trace")
    parser.add_argument('--false_proof_trace_path', type=str, default=f"../output/with_newlemma/false")
    parser.add_argument('--lemmas_theory_library', type=str, default=f"../output/with_newlemma")

    parser.add_argument('--run_count', type=int, default=1)

    args = parser.parse_args()

    logger = utils.get_logger()
    args.logger = logger

    api_base = "https://api.xiaoai.plus/v1"

    key: Key = Key(args.keys_path)
    llm = LLM(key=key, model='gpt-3.5-turbo', logger = logger, api_base=api_base)
    prompter = Prompter(2, global_function_definition=[args.global_function_definition, ""],logger=logger)
    prompter.read_all_prompts(args)
    prompter.read_all_examples(args)
    key1 = Key("../chromadb/key")
    embedding_model_name = "text-embedding-3-small"
    collection = Collection(key=key1, api_base=api_base, embedding_model_name=embedding_model_name)

    generator = Generator(llm=llm, prompter=prompter, logger=logger, collection=collection)

    isabelle = Isabelle(logger=logger)
    checker = Checker(isabelle=isabelle, logger=logger)
    """subgoal_lemma = Subgoal_lemma(generator=generator, isabelle=isabelle, checker=checker, logger=logger)
    controller = Controller(subgoal_lemma=subgoal_lemma)"""
    verifier = Verifier(isabelle=isabelle, logger=logger, collection=collection, checker=checker)

    ruler = Rule(isabelle=isabelle)

    proof_method = Proof_method(generator=generator, checker=checker, verifier=verifier, logger=logger, collection=collection)

    #datasets = ["stack", "boundedstack", "FIFO_queue", "priority_queue"]
    datasets = ["FIFO_queue"]

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
            prompter.set_function_attribute("priority_queue")
            #prompter.set_function_attribute(dataset)
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

                data_message = Message(data=data, iterations=2, class_name=dataset, theorem_name=data["theorem name"])
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

                logger.info(format_rule)
                logger.info(format_user_rules)


                #args.iterations = 2
                isproof, formal, formal_lemmas = proof_method.method(data_message, args)
                if isproof:
                    logger.info(f"{data['theorem name']}--验证成功---")

    except Exception as e:

        utils.write_valid(data_message, args.true_proof_data_path, "all_invalid_",  data_message.all_formal_proof())
        logger.info(e)
        logger.info("异常")
    finally:
        isabelle.session_stop(isabelle.session_id)