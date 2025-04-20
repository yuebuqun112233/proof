

class Isabelle_response_message:
    def __init__(self):
        self.__ok = False
        self.__info = ""
        self.__counterexample_messages = []
        self.__syntax_error_messages = []
        self.__method = ""
        self.__formal = ""

    def init(self):
        self.__ok = False
        self.__info = ""
        self.__counterexample_messages = []
        self.__syntax_error_messages = []
        self.__method = ""
        self.__formal = ""


    def set_ok(self, ok):
        self.__ok = ok

    def get_ok(self):
        return self.__ok

    def set_info(self, info):
        self.__info = info

    def get_info(self):
        return self.__info

    def add_counterexample_message(self, counterexample_message):
        self.__counterexample_messages.append(counterexample_message)

    def get_counterexample_messages(self):
        return self.__counterexample_messages

    def add_syntax_error_message(self, syntax_error_message):
        self.__syntax_error_messages.append(syntax_error_message)

    def get_syntax_error_messages(self):
        return self.__syntax_error_messages

    def set_method(self, method):
        self.__method = method

    def get_method(self):
        return self.__method

    def set_formal(self, formal):
        self.__formal = formal

    def get_formal(self):
        return self.__formal