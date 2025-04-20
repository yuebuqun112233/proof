

class Key:
    def __init__(self, path: str) -> object:
        self.path = path
        self.keys = Key._get_keys(path)
        self.key_index = 0

    def get_keys(self) -> list:
        file = None
        keys = []
        try:
            file = open(self.path)
            keys = file.readlines()
        except Exception as e:
            print(e)
        finally:
            if file:
                file.close()
        for index, key in enumerate(keys):
            keys[index] = key.replace("\n", "")
        return keys

    @staticmethod
    def _get_keys(path:str) -> list:
        file = None
        keys = []
        try:
            file = open(path)
            keys = file.readlines()
        except Exception as e:
            print(e)
        finally:
            if file:
                file.close()
        for index, key in enumerate(keys):
            keys[index] = key.replace("\n", "")
        return keys


    def get_key(self, index=0):
        if index <= len(self.keys)-1 and index > -1:
            return self.keys[index]
        else:
            return -1
