import argparse
import os
import time

import utils
from message.Message import Message
from utils import save_name
from verify.Checker import Checker
from verify.Isabelle import Isabelle
from verify.Verifier import Verifier


class Proof_method():
    def __init__(self, checker:Checker, verifier:Verifier, logger=None):
        self.__checker = checker
        self.__verifier = verifier
        self.logger = logger

    def get_checker(self):
        return self.__checker

    def get_verifier(self):
        return self.__verifier

    def method(self, data_message:Message, args):
        formal = data_message.getData()["formal theorem statement"] + " sorry"
        formal = self.get_checker().check_nitpick_syntax_all_subgoal(formal, args.theory_path, data_message)
        if "" == formal:
            self.logger.info("formal theorem statement错误")
            return False, ""

        isproof, info, formal = self.get_verifier().verify(args.theory_path, data_message, args, formal)
        data_message.set_final_formal_proof(formal)

        if isproof:
            utils.write_valid(data_message, args.true_proof_data_path, "valid_",
                              formal)
            save_name(args.true_proof_data_path_dataset, data_message.getData()["theorem name"], 1, 0, self.logger)
            return True, formal
        return False, ""





if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--data_path', type=str, default=f"../data/")

    parser.add_argument('--theory_path', type=str, default=f"../output/sledgehammer/theory")
    parser.add_argument('--true_proof_data_path', type=str, default=f"../output/sledgehammer/true")


    args = parser.parse_args()

    logger = utils.get_logger()
    args.logger = logger

    isabelle = Isabelle(logger=logger)
    checker = Checker(isabelle=isabelle, logger=logger)
    verifier = Verifier(isabelle=isabelle, logger=logger)
    proof_method = Proof_method(checker=checker, verifier=verifier, logger=logger)
    datasets = ["stack", "boundedstack", "FIFO_queue", "priority_queue"]

    theory_path = args.theory_path
    true_proof_data_path = args.true_proof_data_path

    try:
        for dataset in datasets:
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

                data_message = Message(data=data)

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

                isproof, formal = proof_method.method(data_message, args)
                if isproof:
                    logger.info(f"{data['theorem name']}--验证成功---")
    except Exception as e:
        logger.info(e)
        logger.info("异常")
    finally:
        isabelle.session_stop(isabelle.session_id)