from generator.Role import Role


class Lemma():
    def __init__(self, name, lemma_statement, stage:Role):
        self.__name = name
        self.__lemma_statement = lemma_statement
        self.__stage = stage

    def set_name(self, name):
        self.__name = name

    def get_name(self):
        return self.__name

    def set_lemma_statement(self, lemma_statement):
        self.__lemma_statement = lemma_statement

    def get_lemma_statement(self):
        return self.__lemma_statement

    def set_stage(self, stage:Role):
        self.__stage = stage

    def get_stage(self):
        return self.__stage