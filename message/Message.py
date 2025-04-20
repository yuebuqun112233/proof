from generator.Role import Role
from message.Lemma import Lemma


class Message:
    def __init__(self,class_name, theorem_name, data=None, informal="", formal="", property = "theorem", dependent_function = "", dependent_rules = "", iterations=0, public_rep="", private_rep=""):
        self.__data = data
        self.__informal = informal
        self.__formal = formal
        self.__property = property
        self.__stage = Role.NONE
        self.__is_verified = False
        self.__dependent_function = dependent_function
        self.__dependent_rules = dependent_rules
        self.__verified_lemmas = {}
        self.__all_verified_lemmas = {}
        self.__unverified_lemmas = {}
        self.__unverified_valid_lemmas = {}
        self.__iterations = iterations
        self.__public_rep = public_rep
        self.__private_rep = private_rep
        self.__final_formal_proof = []
        self.__lemma_messages = []
        self.__class = class_name
        self.__theorem_name = theorem_name
        self.__lemmas_theory_library = "" #路径
        self.__lemmas_package = "" #theorem导包相对路径
        self.__lemmas = {}
        self.__rename_flag = False

    def set_rename_flag(self, flag):
        self.__rename_flag = flag

    def get_rename_flag(self):
        return self.__rename_flag

    def set_stage(self, stage:Role):
        self.__stage = stage

    def get_stage(self):
        return self.__stage

    def set_lemmas_package(self, lemmas_package):
        self.__lemmas_package = lemmas_package

    def get_lemmas_package(self):
        return self.__lemmas_package

    def set_lemmas_theory_library(self, lemmas_theory_library):
        self.__lemmas_theory_library = lemmas_theory_library

    def get_lemmas_theory_library(self):
        return self.__lemmas_theory_library

    def set_class(self, class_name):
        self.__class = class_name

    def get_class(self):
        return self.__class

    def set_theorem_name(self, theorem_name):
        self.__theorem_name = theorem_name

    def get_theorem_name(self):
        return self.__theorem_name

    def set_is_verified(self, is_true):
        self.__is_verified = is_true

    def get_is_verified(self):
        return self.__is_verified

    def add_lemma_messages(self, lemma_messages):
        self.__lemma_messages.append(lemma_messages)

    def get_lemma_messages(self):
        return self.__lemma_messages

    def clean_lemma_messages(self):
        self.__lemma_messages = []

    def set_property(self, property):
        self.__property = property

    def get_property(self):
        return self.__property

    def set_public_rep(self, public_rep):
        self.__public_rep = public_rep

    def set_private_rep(self, private_rep):
        self.__private_rep = private_rep

    def get_public_rep(self):
        return self.__public_rep

    def get_private_rep(self):
        return self.__private_rep

    def set_informal(self, informal):
        self.__informal = informal

    def get_informal(self):
        return self.__informal

    def set_formal(self, formal):
        self.__formal = formal

    def get_formal(self):
        return self.__formal

    def set_final_formal_proof(self, formal):
        self.__final_formal_proof.append(f"\n{formal}\n\n")

    def get_final_formal_proof(self):
        if len(self.__final_formal_proof) > 0:
            return self.__final_formal_proof[-1]
        else:

            return "无formal"

    def get_all_final_formal_proof(self):
        return self.__final_formal_proof

    def all_formal_proof(self):
        all_final_formal = ""
        for count, final_formal in enumerate(self.get_all_final_formal_proof()):
            all_final_formal = all_final_formal + f"\n------------------ count={count} ------------------\n" + final_formal
        return all_final_formal

    def init(self):
        self.set_informal("")
        self.set_formal("")
        self.init_unverified_lemmas()
        self.init_unverified_valid_lemmas()

    def init_informal_and_formal(self):
        self.set_informal("")
        self.set_formal("")

    def getData(self):
        return self.__data

    def set_all_verified_lemmas(self, all_verified_lemmas):
        self.__all_verified_lemmas = all_verified_lemmas

    def get_all_verified_lemmas(self):
        return self.__all_verified_lemmas

    def set_verified_lemmas(self, verified_lemmas):
        self.__verified_lemmas = verified_lemmas

    def get_verified_lemmas(self):
        return self.__verified_lemmas

    def add_unverified_lemmas(self, lemmas, stage:Role):
        for lemma_key, lemma_value in lemmas.items():
            if lemma_key not in self.get_unverified_lemmas():
                self.get_unverified_lemmas()[lemma_key] = Lemma(name=lemma_key, lemma_statement=lemma_value, stage=stage)

    def add_unverified_lemmas_obj(self, lemmas):
        for lemma_key, lemma_value in lemmas.items():
            if lemma_key not in self.get_unverified_lemmas():
                self.get_unverified_lemmas()[lemma_key] = lemma_value

    def get_unverified_lemmas(self):
        return self.__unverified_lemmas

    def init_unverified_lemmas(self):
        self.__unverified_lemmas = {}

    def add_unverified_valid_lemmas(self, lemmas):
        lemma_value:str
        unverified_valid_lemmas = self.get_unverified_valid_lemmas()
        for lemma_key, lemma_value in lemmas.items():
            if lemma_key not in unverified_valid_lemmas:
                unverified_valid_lemmas[lemma_key] = lemma_value

    def get_unverified_valid_lemmas(self):
        return self.__unverified_valid_lemmas

    def init_unverified_valid_lemmas(self):
        self.__unverified_valid_lemmas = {}

    def get_dependent_rules(self):
        return self.__dependent_rules

    def set_dependent_rules(self, dependent_rules):
        self.__dependent_rules = dependent_rules

    def get_dependent_function(self):
        return self.__dependent_function

    def set__dependent_function(self, dependent_function):
        self.__dependent_function = dependent_function

    def get_iterations(self):
        return self.__iterations

    def set_iterations(self, iterations):
        self.__iterations = iterations

    def list_unverified_lemmas(self):
        list_lemmas = []
        unverified_lemmas = self.get_unverified_lemmas()
        for id, lemma in unverified_lemmas.items():
            list_lemmas.append(lemma)
        return list_lemmas



if __name__ == '__main__':
    message = Message()
    message.add_unverified_valid_lemmas({"as":"fsfdds", "gfdg":"gfdgdr"})
    print(message.get_unverified_valid_lemmas())


    print({} is None)

    print(message.get_final_formal_proof())
    message.set_final_formal_proof("fdsfjkd")
    message.set_final_formal_proof("erw4erfesf")
    print(message.get_final_formal_proof())
