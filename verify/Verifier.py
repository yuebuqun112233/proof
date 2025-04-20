
#from Controller.Subgoal_lemma import Subgoal_lemma
from Chromadb.Collection import Collection
from Chromadb.ROLE_COLLECTION import Role_collection
from generator.Role import Role
from message.Message import Message

from utils import write_thy, jsonmerge, first_sorry_to_sledgehammer, jsonmerge2, is_sorry, \
    get_theory_with_lemmas, create_lemmas_theory_library
from verify.Isabelle import Isabelle

class Verifier:
    def __init__(self, isabelle:Isabelle, collection:Collection=None,  logger=None, checker=None):
        self.__isabelle = isabelle
        self.__collection = collection
        #self.__controller = controller
        self.logger = logger
        self.__checker = checker
        # self.session_id = isabelle.isabelle_prover.session_start()

    def get_checker(self):
        return self.__checker

    def get_collection(self):
        return self.__collection

    def set_isabelle(self, isabelle:Isabelle):
        self.__isabelle = isabelle

    def get_isabelle(self):
        return self.__isabelle

    """def get_controller(self):
        return self.__controller"""

    def verify(self, theory_path, data_message:Message, args, formal, subgoal_lemma=None):

        while is_sorry(formal):
            pre, post = first_sorry_to_sledgehammer(formal)
            if pre == '' and post == '':  # pre和post同时为空的条件是，文件中没有一个sorry
                return False, "", formal
            thy = get_theory_with_lemmas(data_message, pre,
                                         'sledgehammer [prover=cvc4 vampire verit e spass z3 zipperposition] sorry',
                                         post, verified_midlemmas=data_message.get_all_verified_lemmas(),
                                         unverified_midlemmas=data_message.get_unverified_lemmas())
            write_thy(theory_path, data_message.getData()["theorem name"], thy)
            self.logger.info(thy)

            isProof, method, formal = self.get_isabelle().run_sledgehammer(theory_path, data_message, pre, post, args)
            if isProof:
                continue

            isproof, method, formal = self.extend_sledgehammer(theory_path, data_message, pre, post, args, subgoal_lemma)
            if isproof:
                self.logger.info('------------------------------sledgehammer 证明成功--------------------------------------------')
                continue
            else:
                return False, "sledgehammer验证失败", pre+"sorry"+post
        if formal == "":
            return False, "formal为空", formal
        return True, "成功", formal

    def extend_sledgehammer(self, theory_path, data_message: Message, pre, post, args, subgoal_lemma=None):

        args.logger.info(f"-{data_message.get_iterations()}----extend_sledgehammer-------")

        if data_message.get_iterations() > 0 and subgoal_lemma is not None:
            """
            基于子目标生成中间引理并
            """
            subgoaler = subgoal_lemma
            subgoaler.set_subgoal("")
            if subgoaler is not None:
                isproof, method, formal, valid_lemmas, all_lemmas = subgoaler.verify_subgoal_with_lemma(theory_path, data_message,
                                                                                            pre, post, args)
                """if isproof:
                    args.logger.info(
                        '-------------------------------lemmaofsubgoal 验证通过--------------------------------------')
                    return isproof, method, formal"""

                if method == "无引理生成":
                    return False, "", ""

                args.logger.info('------------------------------all lemmas--------------------------------------')
                args.logger.info(len(all_lemmas))
                args.logger.info(all_lemmas)

                args.logger.info('------------------------------验证 valid lemmas--------------------------------------')
                args.logger.info(len(valid_lemmas))
                args.logger.info(valid_lemmas)


                unverified_valid_lemmas = {}

                if isproof and valid_lemmas != {}:
                    unverified_valid_lemmas = subgoaler.verify_valid_lemmas(data_message, valid_lemmas, args)
                    if unverified_valid_lemmas == {}:
                        args.logger.info(
                            '------------------------------unverified_valid_lemmas----重新验证---------------------------------')
                        data_message.set_all_verified_lemmas(
                            self.get_collection().get_all_lemmas(Role_collection.VERIFIED_LEMMA2,
                                                                 metadata_class=args.dataset))
                        self.logger.info(f"\n\n--------data_message.set_all_verified_lemmas-------\n\n")
                        self.logger.info(data_message.get_all_verified_lemmas())
                        self.logger.info(f"\n\n--------data_message.set_verified_lemmas-------\n\n")
                        self.logger.info(data_message.get_verified_lemmas())
                        create_lemmas_theory_library(args, data_message.get_all_verified_lemmas(),
                                                           self.get_checker())
                        isProof_, method, formal = self.get_isabelle().run_sledgehammer(theory_path, data_message, pre,
                                                                                       post, args)
                        if not isProof_:
                            args.logger.warning("------------------------------subgoal all valid lemmas 都被验证， 但subgoal没有被证明---------------------------------")
                        return isProof_, method, formal

                args.logger.info(
                    '-------------------------------开始reflection-------------------------------------------')

                if isproof and unverified_valid_lemmas != {}:
                    direction = "true"

                    isproof, method, formal = subgoaler.reflection_subgoal_lemma(theory_path, data_message, pre, post,
                                                                                 args, direction=direction, lemmas=unverified_valid_lemmas)

                if not isproof:
                    direction = "false"
                    data_message.add_unverified_lemmas_obj(all_lemmas)
                    isproof, method, formal = subgoaler.reflection_subgoal_lemma(theory_path, data_message, pre, post,
                                                                                 args, direction=direction, lemmas=all_lemmas)

                if isproof:
                    args.logger.info(
                        '-------------------------------reflection_subgoal_lemma 验证通过-------------------------------------------')
                    return isproof, method, formal

        return False, "", ""

