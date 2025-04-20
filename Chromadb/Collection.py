from chromadb.utils import embedding_functions

import chromadb


import utils
from Chromadb.ROLE_COLLECTION import Role_collection
from generator.Key import Key
from generator.Role import Role
from message.Lemma import Lemma


class Collection():
    def __init__(self, key: Key=None, api_base: str="", embedding_model_name=""):
        self.key = key
        self.api_base = api_base
        self.embedding_model_name = embedding_model_name
        self.client = chromadb.HttpClient(host='localhost', port=8000)

    def get_ef(self):
        if not self.embedding_model_name:
            #0.15-0.2
            default_ef = embedding_functions.DefaultEmbeddingFunction()
            ef = default_ef
        else:
            """openai_ef = embedding_functions.OpenAIEmbeddingFunction(
                api_key="sk-uySmYl9GYMSE54C7563f40280fE94a519e8fB90c5a0dF5Da",
                api_base="https://api.xiaoai.plus/v1",           
                model_name="text-embedding-3-small"
            )"""
            #0.2
            openai_ef = embedding_functions.OpenAIEmbeddingFunction(
                api_key=self.key.get_key(self.key.key_index),
                api_base=self.api_base,
                model_name=self.embedding_model_name
            )
            ef = openai_ef
        return ef

    def get_or_create_collection(self, collection_name:Role_collection):
        client = self.client
        ef = self.get_ef()
        collection = client.get_or_create_collection(name=collection_name.name.lower(), embedding_function=ef, metadata={"hnsw:space": "cosine"})
        return collection

    def delete_collection(self, collection_name:Role_collection):
        client = self.client
        client.delete_collection(name=collection_name.name.lower())

    def adds(self, collection_name):
        pass

    def add(self, collection_name:Role_collection, document, metadatas, id):
        collection = self.get_or_create_collection(collection_name)

        collection.add(
            documents=[document],
            metadatas=[metadatas],
            ids=[id]
        )

    def count(self, collection_name:Role_collection):
        collection = self.get_or_create_collection(collection_name)
        return collection.count()

    def query(self, collection_name:Role_collection, text, metadata_class="", metadata_theorem="", n_results=3):
        collection = self.get_or_create_collection(collection_name)
        if metadata_class == "" and metadata_theorem == "":
            return collection.query(
                query_texts=[text],
                n_results=n_results,
            )
        elif metadata_class != "" and metadata_theorem == "":
            return self.query_class(collection_name, text, metadata_class, n_results=n_results)
        elif metadata_class == "" and metadata_theorem != "":
            return self.query_theorem(collection_name, text, metadata_theorem, n_results=n_results)
        else:
            return self.query_class_theorem(collection_name, text, metadata_class, metadata_theorem, n_results=n_results)


    def query_class(self, collection_name:Role_collection, text, metadata_class, n_results=3):
        collection = self.get_or_create_collection(collection_name)
        return collection.query(
            query_texts=[text],
            n_results=n_results,
            where={"class": metadata_class}
            )

    def query_theorem(self, collection_name:Role_collection, text, metadata_theorem, n_results=3):
        collection = self.get_or_create_collection(collection_name)
        return collection.query(
            query_texts=[text],
            n_results=n_results,
            where={"theorem": metadata_theorem}
            )

    def query_class_theorem(self, collection_name:Role_collection, text, metadata_class, metadata_theorem,n_results=3):
        collection = self.get_or_create_collection(collection_name)
        return collection.query(
            query_texts=[text],
            n_results=n_results,
            where={"$and":[{"class": metadata_class}, {"theorem": metadata_theorem}]}
            )
    def query_class_theorem2(self, collection_name:Role_collection, text,test2, metadata_class, metadata_theorem,n_results=3):
        collection = self.get_or_create_collection(collection_name)
        return collection.query(
            query_texts=[text, test2],
            n_results=n_results,
            where={"$and":[{"class": metadata_class}, {"theorem": metadata_theorem}]}
            )

    def get(self, collection_name:Role_collection, metadata_class="", metadata_theorem=""):
        collection = self.get_or_create_collection(collection_name)
        if metadata_class == "" and metadata_theorem == "":
            return collection.get()
        elif metadata_class != "" and metadata_theorem == "":
            return collection.get(where={"class": metadata_class})
        elif metadata_class == "" and metadata_theorem != "":
            return collection.get(where={"class": metadata_theorem})
        else:
            return collection.get(where={"$and":[{"class": metadata_class}, {"theorem": metadata_theorem}]})

    def get_id(self, collection_name:Role_collection, id):
        collection = self.get_or_create_collection(collection_name)
        return collection.get(ids=[id])

    def get_class(self, collection_name:Role_collection, metadata_class):
        collection = self.get_or_create_collection(collection_name)
        return collection.get(where={"class": metadata_class})

    def get_theorem(self, collection_name:Role_collection, metadata_theorem):
        collection = self.get_or_create_collection(collection_name)
        return collection.get(where={"theorem": metadata_theorem})

    def delete(self, collection_name:Role_collection, id):
        collection = self.get_or_create_collection(collection_name)
        collection.delete(
            ids=[id]
        )

    def delete_class(self, collection_name:Role_collection, metadata_class):
        collection = self.get_or_create_collection(collection_name)
        collection.delete(
            where={"class": metadata_class}
        )

    def delete_theorem(self, collection_name:Role_collection, metadata_theorem):
        collection = self.get_or_create_collection(collection_name)
        collection.delete(
            where={"theorem": metadata_theorem}
        )

    def delete_id(self, collection_name:Role_collection, id):
        collection = self.get_or_create_collection(collection_name)
        collection.delete(
            where={"id": id}
        )

    def similarity_distance(self, collection_name:Role_collection, lemma, metadata_class="", metadata_theorem=""):
        """index = lemma.find("shows ")
        if index != -1:
            lemma = lemma[index:]"""
        distance = 100
        document = ""
        print(lemma)
        if collection_name == Role_collection.PROBLEM:
            res = self.query(collection_name, lemma, metadata_class, metadata_theorem, n_results=1)
            print(res)
            distances = res["distances"][0]
            if len(distances) > 0:
                distance = distances[0]
                document = res["documents"][0][0]
        elif collection_name == Role_collection.VERIFIED_LEMMA1:
            res = self.query(collection_name, lemma, metadata_class, metadata_theorem, n_results=1)
            print(res)
            distances = res["distances"][0]
            if len(distances) > 0:
                distance = distances[0]
                document = res["documents"][0][0]
        else:
            print(f"错误--Role_collection未配置{collection_name}")

        return distance, document

    def get_all_lemmas(self, collection_name:Role_collection, metadata_class="", metadata_theorem=""):
        res = self.get(collection_name, metadata_class, metadata_theorem)
        print("res-------------------")
        print(res)
        lemmas = {}
        ids = res["ids"]
        print("ids-------------------")
        if ids == []:
            return lemmas
        print(ids)
        #lemmas["ids"] = ids
        #print(lemmas["ids"])
        documents = res["documents"]
        metadatas = res["metadatas"]
        if collection_name == Role_collection.VERIFIED_LEMMA1:
            total_count = self.count(collection_name)
            mid_value = [None for _ in range(total_count)]
            ids_ = ["" for _ in range(total_count)]
            for count, metadata in enumerate(metadatas):
                index = metadata["index"]
                mid_value[index-1] = metadata
                ids_[index-1] = ids[count]
            for count, metadata in enumerate(mid_value):
                if metadata is not None:
                    id = ids_[count]
                    lemmas[id] = Lemma(name=id, lemma_statement=metadata["proof"], stage=utils.return_stage_role(metadata["stage"]))
        elif collection_name == Role_collection.UNVERIFED_LEMMA or collection_name == Role_collection.UNVERIFIED_VALID_LEMMA:
            for index, id in enumerate(ids):
                lemmas[id] = Lemma(name=id, lemma_statement=documents[index],
                                              stage=utils.return_stage_role(metadatas[index]["stage"]))
        else:
            print(f"错误--Role_collection未配置{collection_name}")
        return lemmas

    def query_similar_lemmas(self, collection_name:Role_collection, document:str, metadata_class="", metadata_theorem="", n_results=4):
        """index = document.find("shows ")
        if index != -1:
            document = document[index:]"""
        res = self.query(collection_name, document, metadata_class, metadata_theorem, n_results)
        lemmas = {}
        ids = res["ids"][0]
        documents = res["documents"][0]
        metadatas = res["metadatas"][0]
        for index, id in enumerate(ids):
            lemmas[id] = Lemma(name=id, lemma_statement=documents[index],
                                              stage=utils.return_stage_role(metadatas[index]["stage"]))
        return lemmas


def test():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"
    collection_name = "test"
    collection = Collection(key=key, api_base=api_base, embedding_model_name="")
    # collection.delete_collection(collection_name)
    print(collection)
    print(collection.get_or_create_collection(collection_name))
    print(collection.client.count_collections())
    print(collection.client.list_collections())
    collection.add(collection_name,
                   """
                   lemma min_priority_leq_all_intermediate:
                      assumes "\<not> is_empty q"
                        and "v \<in> set |q|"
                        and "priority q = map_of (alist_of q)"
                        and "min q = fst (hd (alist_of q))"
                      shows "the (map_of (alist_of q) (fst (hd (alist_of q)))) \<le> the (map_of (alist_of q) v)"
                   """,
                   utils.metadata_template("priority_queue", "min_priority_leq_all"),
                   "min_priority_leq_all_intermediate")

    collection.add(collection_name,
                   """
                   lemma min_priority_leq:
                      assumes a1:"\<not> is_empty q"
                        and a2:"v \<in> set (values q)"
                      shows "the (priority q (min q)) \<le> the (priority q v)"
                   """,
                   utils.metadata_template("priority_queue", "min_priority_leq_all"),
                   "min_priority_leq")

    collection.add(collection_name,
                   """
                   lemma priority_min_leq_all:
                      assumes a1: "\<not> is_empty q"
                        and a2: "v \<in> set (values q)"
                      shows "the (map_of (alist_of q) (min q)) \<le> the (map_of (alist_of q) v)"
                   """,
                   utils.metadata_template("priority_queue", "min_priority_leq_all"),
                   "priority_min_leq_all")

    collection.add(collection_name,
                   """
                   theorem min_priority_leq_all:
                    assumes a1:"\<not> is_empty q" and a2:"v \<in> set |q|"
                    shows "the (priority q (min q)) \<le> the (priority q v)"
                   """,
                   utils.metadata_template("priority_queue", "min_priority_leq_all"),
                   "min_priority_leq_all")

    collection.add(collection_name,
                   """
                 jygdhthfghgfd
                   """,
                   utils.metadata_template("priority_queue1", "min_priority_leq_all"),
                   "items")

    collection.add(collection_name,
                   """
                        theorem
                        push_alist_of: "alist_of (push k p q) = insort_key snd (k, p) (alist_of q)"
                   """,
                   utils.metadata_template("priority_queue1", "new_push_priority_correct"),
                   "push_alist_of")

    res = collection.query_class_theorem(collection_name, """
                                                    theorem min_priority_leq_all:
                                                      assumes a1:"\<not> is_empty q" and a2:"v \<in> set |q|"
                                                      shows "the (priority q (min q)) \<le> the (priority q v)"
                                                    """, utils.metadata_template("priority_queue1", "min_priority_leq_all"), 5)

    print(res)
    collection.delete(collection_name, "min_priority_leq")
    """print(res)
    print(collection.get(collection_name))
    print("____")
    print(collection.get_class(collection_name, "priority_queue1"))
    print("____")
    print(collection.get_class(collection_name, "priority_que"))
    print("____")
    print(collection.get_theorem(collection_name, "new_push_priority_correct"))
    print("____")
    print(collection.get_theorem(collection_name, "min_priority_leq_all"))

    print("**********")
    print(collection.get(collection_name))
    collection.delete_theorem(collection_name, "min_priority_leq_all")
    print(collection.get(collection_name))"""

def construct_chromadb_problem():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"
    collection_name = Role_collection.PROBLEM
    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)

    datasets = ["stack", "boundedstack", "FIFO_queue", "priority_queue"]
    for dataset in datasets:
        datas = utils.read_dir("../data/" + dataset + "/", 'json')
        for count, data in enumerate(datas):
            collection.add(collection_name, data["formal theorem statement"], utils.metadata_template_problem(dataset, data["theorem name"], data["theorem name"]), data["theorem name"])

    print(collection.get(collection_name))

def construct_chromadb_problem_shows():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"
    collection_name = Role_collection.PROBLEM
    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)

    datasets = ["stack", "boundedstack", "FIFO_queue", "priority_queue"]
    for dataset in datasets:
        datas = utils.read_dir("../data/" + dataset + "/", 'json')
        for count, data in enumerate(datas):
            document = data["formal theorem statement"]
            index = document.find("shows")
            if index != -1:
                document = document[index:]
            collection.add(collection_name, document, utils.metadata_template_problem(dataset, data["theorem name"],data["theorem name"]+"_shows"), data["theorem name"]+"_shows")

    print(collection.get(collection_name))

def test1():
    # construct_chromadb_problem()
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name="")
    lemma = """
            theorem priority_min_leq_all:
      assumes a1: "\<not> is_empty q"
        and a2: "v \<in> set (values q)"
      shows "the (map_of (alist_of q) (min q)) \<le> the (map_of (alist_of q) v)"
        """
    print(collection.similarity_distance(Role_collection.PROBLEM, lemma, "priority_queue", "min_priority_leq_all")[0])
    print(collection.client.list_collections())
    print(collection.client.count_collections())
    verified_lemma_collection = collection.get(Role_collection.VERIFIED_LEMMA)
    print(verified_lemma_collection)
    # print(collection.get(Role_collection.VERIFIED_LEMMA.name.lower()))
    # print(collection.get(Role_collection.PROBLEM.name.lower()))
    ids = verified_lemma_collection["ids"]
    embeddings = verified_lemma_collection["embeddings"]
    metadatas = verified_lemma_collection["metadatas"]
    documents = verified_lemma_collection["documents"]

    for id in ids:
        print("__________________________________")
        col = collection.get_id(Role_collection.VERIFIED_LEMMA, id)
        print(col)
        print(col["ids"])
        print(col["metadatas"][0])
        print(col["metadatas"][0]["class"])
        print(col["metadatas"][0]["theorem"])
        print(col["metadatas"][0]["proof"])
        print(col["documents"])
        print("__________________________________")

    print("++++++++++++++++++++++++++++++++++++++++++++++++++")

    col_problem = collection.get_id(Role_collection.PROBLEM, "min_priority_leq_all")
    print(col_problem)
    print(col_problem["documents"])
    problem = col_problem["documents"][0]
    print(problem)

    res = collection.query_class_theorem(Role_collection.VERIFIED_LEMMA, problem, "priority_queue",
                                         "min_priority_leq_all", n_results=5)
    print(res)
    ids = res["ids"][0]
    for id in ids:
        print("__________________________________")
        col = collection.get_id(Role_collection.VERIFIED_LEMMA, id)
        print(col)
        print(col["ids"])
        print(col["metadatas"][0])
        print(col["metadatas"][0]["class"])
        print(col["metadatas"][0]["theorem"])
        print(col["metadatas"][0]["proof"])
        print(col["documents"])
        print("__________________________________")

    collection.add(Role_collection.VERIFIED_LEMMA,
                   "lemma distinct_fst_alist_of:\"distinct (map fst (alist_of q))\""
                   , utils.metadata_template_proof("priority_queue", "min_priority", ""), "distinct_fst_alist_of")

    lemma = """
           lemma distinct_fst_alist_of:\"distinct (map fst (alist_of q))
        """
    print(
        collection.similarity_distance(Role_collection.VERIFIED_LEMMA, lemma, "priority_queue", "min_priority_leq_all")[0])
def test3():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name="")
    print(collection.client.list_collections())
    print(collection.client.count_collections())
    """verified_lemma_collection = collection.get(Role_collection.VERIFIED_LEMMA.name.lower())
    print(verified_lemma_collection)
    collection.delete_collection(Role_collection.VERIFIED_LEMMA.name.lower())
    print(collection.client.list_collections())
    print(collection.client.count_collections())"""

    print(collection.get(Role_collection.VERIFIED_LEMMA))
    print(collection.similarity_distance(Role_collection.VERIFIED_LEMMA, "a", "d")[0])
    s = {"a": [[]]}
    print(len(s["a"]))
    lemma = """
        lemma priority_leq_defined: assumes "priority q k \<noteq> None" and "priority q v \<noteq> None"
      shows "the (priority q k) \<le> the (priority q v)"
        """
    dintance, document = collection.similarity_distance(Role_collection.PROBLEM, lemma, "priority_queue",
                                                        "min_priority_leq_all")
    print(dintance)
    print(document)


def test4():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)
    print(collection.client.list_collections())
    print(collection.client.count_collections())
    collection_name = Role_collection.test_sequnce
    verified_lemma_collection = collection.get(collection_name)
    collection.add(collection_name,
                   """

                      shows "the (map_of (alist_of q) (min q)) \<le> the (map_of (alist_of q) v)"
                   """,
                   utils.metadata_template("priority_queue", "min_priority_leq_all"),
                   "priority_min_leq_all1")
    print(collection.get(collection_name))

def test5():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)
    print(collection.client.list_collections())
    print(collection.client.count_collections())
    """collection.delete_collection(Role_collection.VERIFIED_LEMMA)
    collection.delete_collection(Role_collection.PROBLEM)
    collection.delete_collection(Role_collection.test_sequnce)
    print(collection.client.list_collections())
    print(collection.client.count_collections())"""
    """construct_chromadb_problem()
    collection_name = Role_collection.PROBLEM
    res = collection.get(collection_name)
    print(res)
    print(len(res['ids']))"""
    # collection.delete_collection(Role_collection.VERIFIED_LEMMA)

    """res = collection.get(collection_name)
    print(res)
    print(len(res['ids']))"""
    # construct_chromadb_problem_shows()
    """res = collection.get(collection_name)
    print(res)
    print(len(res['ids']))
    documents = res["documents"]
    for document in documents:
        print("_____=============================______")
        print(document)"""
    lemma1 = """
        lemma priority_ordering:
      assumes "v \<in> set |q|"
      shows "the (priority q (min q)) \<le> the (priority q v)"
        """
    lemma2 = """
        shows "the (priority q (min q)) \<le> the (priority q v)"
        """
    lemma3 = """
        theorem min_priority_leq_all: assumes a1:"\\<not> is_empty q" and a2:"v \\<in> set |q|"\n shows "the (priority q (min q)) \\<le> the (priority q v)"
        """
    """print(collection.similarity_distance(Role_collection.PROBLEM, lemma3, "priority_queue","min_priority_leq_all"))
    print(collection.similarity_distance(Role_collection.PROBLEM, lemma2, "priority_queue", "min_priority_leq_all"))
    print(collection.query_class_theorem(Role_collection.PROBLEM, lemma1, "priority_queue",
                                          "min_priority_leq_all"))
    print(collection.query_class_theorem(Role_collection.PROBLEM, lemma2, "priority_queue",
                                         "min_priority_leq_all"))
    print(collection.query_class_theorem2(Role_collection.PROBLEM, lemma1, lemma2, "priority_queue", "min_priority_leq_all"))
"""
    """verified_lemma = collection.get(Role_collection.VERIFIED_LEMMA)
    print(verified_lemma)
    print(collection.get(Role_collection.UNVERIFED_LEMMA))
    print(collection.get(Role_collection.PROBLEM))"""
    # print(collection.get_all_lemmas(Role_collection.VERIFIED_LEMMA,"priority_queue"))
    """collection.delete_collection(Role_collection.VERIFIED_LEMMA)
    collection.delete_collection(Role_collection.UNVERIFED_LEMMA)"""

    # print(collection.query_similar_lemmas(Role_collection.VERIFIED_LEMMA, lemma, metadata_class="priority_queue"))

    """collection_name_ = Role_collection.UNVERIFED_LEMMA

    lemma = "fkjdsfgdskgdffkj"
    metadatas = utils.metadata_template("priority_queue",
                                        "", stage=Role.SUBGOAL_LEMMA)
    collection.add(collection_name=collection_name_, document=lemma, metadatas=metadatas,
                              id="cc1")

    print(collection.get(Role_collection.UNVERIFED_LEMMA))"""

    """collection.delete_collection(Role_collection.test_sequnce)

    collection_name_ = Role_collection.test_sequnce

    lemma = "fkjdsfgdskgdffkj"
    metadatas = utils.metadata_template("priority_queue",
                                        "", stage=Role.SUBGOAL_LEMMA)
    metadatas = {"class": "priority_queue", "theorem": "", "stage": Role.SUBGOAL_LEMMA.name.lower()}
    collection.add(collection_name=collection_name_, document=lemma, metadatas=metadatas,
                   id="cc1")

    print(collection.get(Role_collection.test_sequnce))"""

    print("+++++++++++++++++")
    """print(collection.query(Role_collection.UNVERIFED_LEMMA, "rrresdfsdfsf"))
    print(collection.query(Role_collection.test_sequnce, "rrresdfsdfsf"))"""

    collection.add(Role_collection.VERIFIED_LEMMA, "tgdfg", {"class": "", "theorem": "", "stage": ""}, "a")

    print(collection.get(Role_collection.VERIFIED_LEMMA))

    """print(collection.query(Role_collection.VERIFIED_LEMMA, "lemma min_not_in_tl_fst_alist_of: \"min q \<notin> set (tl (map fst (alist_of q)))\""),
          )"""

    collection1 = collection.get_or_create_collection(Role_collection.VERIFIED_LEMMA)
    print(collection1.count())

    collection.delete_collection(Role_collection.test_sequnce)
    print(collection.count(Role_collection.test_sequnce))

def test6():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)
    print(collection.client.list_collections())
    print(collection.client.count_collections())
    collection.delete_collection(Role_collection.VERIFIED_LEMMA)

    collection_name = Role_collection.VERIFIED_LEMMA
    print("___________________")
    total_count = collection.count(collection_name)
    name = "f"
    metadatas = utils.metadata_template_proof("", "",
                                              proof=name, stage=Role.SUBGOAL_LEMMA, index=total_count + 1)

    collection.add(collection_name, name, metadatas, name)
    print("___________________")
    total_count = collection.count(collection_name)
    name = "z"
    metadatas = utils.metadata_template_proof("", "",
                                              proof=name, stage=Role.SUBGOAL_LEMMA, index=total_count + 1)

    collection.add(collection_name, name, metadatas, name)
    print("___________________")
    total_count = collection.count(collection_name)
    name = "d"
    metadatas = utils.metadata_template_proof("", "",
                                              proof=name, stage=Role.SUBGOAL_LEMMA, index=total_count + 1)

    collection.add(collection_name, name, metadatas, name)

    print("___________________")
    total_count = collection.count(collection_name)
    name = "e"
    metadatas = utils.metadata_template_proof("", "",
                                              proof=name, stage=Role.SUBGOAL_LEMMA, index=total_count + 1)

    collection.add(collection_name, name, metadatas, name)

    print("*************************")
    print(collection.get(collection_name))

    print(collection.get_all_lemmas(collection_name))

def add_lemma():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"
    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)
    print(collection.client.list_collections())
    print(collection.client.count_collections())



    collection_name = Role_collection.VERIFIED_LEMMA1

    formal = '''lemma head_push_alist_abs:
  assumes "\<not> isfull s"
  shows "hd (fst (alist_of (push v s))) = hd (v # fst (alist_of s))"
proof -
  (* Step 2: Compute hd (fst (alist_of (push v s))) *)
  have h1: "push v s = Abs_bstack (v # fst (alist_of s), snd (alist_of s))" by (simp add: assms push_def)
  then have h2: "alist_of (push v s) = (v # fst (alist_of s), snd (alist_of s))"  using alist_of by (metis (mono_tags, lifting) Abs_bstack_inverse Suc_leI assms capacity_def dual_order.strict_iff_order eq_snd_iff fstI isfull_def length_Cons mem_Collect_eq size_def)
  then have h3: "fst (alist_of (push v s)) = v # fst (alist_of s)" by simp
  then have h4: "hd (fst (alist_of (push v s))) = hd (v # fst (alist_of s))" by simp
  (* Step 3: Conclusion *)
  thus ?thesis by simp
qed
    '''
    lemma = '''lemma head_push_alist_abs:
  assumes "\<not> isfull s"
  shows "hd (fst (alist_of (push v s))) = hd (v # fst (alist_of s))" '''
    print("***********************")

    print(collection.get(collection_name))
    print(collection.count(collection_name))
    print("***********************")
    index = collection.count(collection_name)
    metadatas = utils.metadata_template_proof("boundedstack", "bounded_stack_push_updates_top",
                                              proof=formal, stage=Role.INDIRECT_LEMMA, index=index + 1)

    collection.add(collection_name=collection_name, document=lemma, metadatas=metadatas,
                   id="head_push_alist_abs")

    print(collection.get(Role_collection.VERIFIED_LEMMA))
    print(collection.count(Role_collection.VERIFIED_LEMMA))
"""if __name__ == '__main__':
    add_lemma()"""
def delete_problem():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)
    print(collection.count(Role_collection.PROBLEM))
    problem = collection.get(Role_collection.PROBLEM)
    print(problem)
    ids = problem['ids']
    metadatas = problem["metadatas"]
    documents = problem["documents"]
    names = [ "abs_pq_alist_of_tl","alist_of_Abs_pq_eq","alist_of_inverse","alist_of_preserves_stack_elements","alist_of_push",
              "alist_of_tl_Abs_pq","distinct_alist_of","non_empty_after_push","non_empty_not_full","non_full_after_pop",
              "pop_after_push_not_full","pop_not_in_alist_of","pop_preserves_length_constraint","pop_preserves_stack",
              "pop_simplification","push_Abs_bstack_equiv","push_abs_bstack_relation","push_alist_of_Abs_bstack",
              "push_alist_of_Abs_bstack_refined","push_pop_inverse_hd_tl","push_preserves_non_full","push_preserves_stack",
              "push_preserves_stack_empty","push_stack_structure","size_less_capacity_after_pop","size_less_capacity_not_full",
              "sorted_alist_of","stack_representation_equal","tl_map_fst_eq","top_push","top_push_updated","top_push_updates"
             ]
    for metadata in metadatas:
        print("****************************************************")
        print(metadata)
    for name in names:
        collection.delete_id(Role_collection.PROBLEM, name)
    print(collection.count(Role_collection.PROBLEM))

def delete_verified_index():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)
    print(collection.client.list_collections())
    print(collection.client.count_collections())

    verified = collection.get(Role_collection.VERIFIED_LEMMA)
    print(verified)
    print(collection.count(Role_collection.VERIFIED_LEMMA))
    collection_ = collection.get_or_create_collection(Role_collection.VERIFIED_LEMMA)
    collection_.delete(
        where={"index": 24}
    )
    verified = collection.get(Role_collection.VERIFIED_LEMMA)
    print(verified)
    print(collection.count(Role_collection.VERIFIED_LEMMA))

def add_lemma1():
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)
    print(collection.client.list_collections())
    print(collection.client.count_collections())
    lemma = """
        lemma alist_of_push_insort_key:
      assumes "v \<notin> set (values q)"
      shows "alist_of (push v a q) = insort_key snd (v, a) (alist_of q)"
    proof -
      (* Step 1: Evaluate push when v is not in the queue *)
      have "push v a q = Abs_pq (insort_key snd (v, a) (alist_of q))"
        by (simp add: assms push_abs_pq_relation)
      (* Step 2: Show that the list representation of push v a q is equal to insort_key snd (v, a) (alist_of q) *)
      then have "alist_of (push v a q) = alist_of (Abs_pq (insort_key snd (v, a) (alist_of q)))"
        by simp
      (* Step 3: Use alist_of_inverse *)
      also have "... = insort_key snd (v, a) (alist_of q)"
         using alist_of using alist_of_Abs_pq assms distinct_insort_key_fst sorted_insort_key_alist_of by fastforce
      (* Step 4: Conclude *)
      finally show ?thesis by simp
    qed
        """
    metadatas = utils.metadata_template_proof("priority_queue", "push_commute",
                                              proof=lemma, stage=Role.SUBGOAL_LEMMA, index=30)
    collection.add(collection_name=Role_collection.VERIFIED_LEMMA, document="""
        lemma alist_of_push_insort_key:
      assumes "v \<notin> set (values q)"
      shows "alist_of (push v a q) = insort_key snd (v, a) (alist_of q)" """, metadatas=metadatas,
                   id="alist_of_push_insort_key")

    print(collection.count(Role_collection.VERIFIED_LEMMA))
    print(collection.get(Role_collection.VERIFIED_LEMMA))

if __name__ == '__ain__':
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)
    col = collection.get_or_create_collection(Role_collection.VERIFIED_LEMMA)
    col.update(
        ids=["min_priority_leq_all_aux"],
        metadatas=[{'class': 'priority_queue', 'index': 11,
                    'proof': 'lemma min_priority_leq_all_aux:\n  assumes a1: "sorted (map snd (alist_of q))"\n    and a2: "distinct (map fst (alist_of q))"\n    and a3: "v \\<noteq> fst (hd (alist_of q))"\n    and a4: "v \\<in> set (map fst (alist_of q))"\n  shows "the (map_of (alist_of q) (fst (hd (alist_of q)))) \\<le> the (map_of (alist_of q) v)"\nproof -\n  (* Step 1: Definitions *)\n  define min_key where "min_key = fst (hd (alist_of q))"\n  \n  (* Step 2.1: Analysis of a1 *)\n  have min_priority_leq_all: "\\<forall>p. (min_key, p) \\<in> set (alist_of q) \\<longrightarrow> the (map_of (alist_of q) min_key) \\<le> p"\n    using a1 unfolding min_key_def\n    by (simp add: a2)\n  \n  (* Step 2.2: Analysis of a2 *)\n  have v_priority_defined: "\\<exists>p. (v, p) \\<in> set (alist_of q)"\n    using a4 by auto\n  \n  (* Step 2.3: Analysis of a3 *)\n  have min_key_neq_v: "min_key \\<noteq> v"\n    using a3 unfolding min_key_def\n    by auto\n  \n  (* Step 3: Conclusion *)\n  show ?thesis\n    using min_priority_leq_all v_priority_defined min_key_neq_v\n    by (smt (verit, best) a1 a2 empty_iff empty_set hd_conv_nth in_set_conv_nth length_map length_pos_if_in_set list.set_cases map_of_Cons_code(2) map_of_is_SomeI nth_map option.sel prod.collapse sndI sorted_nth_mono zero_le)\nqed\n',
                    'stage': 'subgoal_lemma',
                    'theorem': 'min_priority_leq_all'}
                   ],
        documents=[
            'lemma min_priority_leq_all_aux:\n  assumes a1: "sorted (map snd (alist_of q))"\n    and a2: "distinct (map fst (alist_of q))"\n    and a3: "v \\<noteq> fst (hd (alist_of q))"\n    and a4: "v \\<in> set (map fst (alist_of q))"\n  shows "the (map_of (alist_of q) (fst (hd (alist_of q)))) \\<le> the (map_of (alist_of q) v)'],
    )

if __name__ == '__main__':
    api_base = "https://api.xiaoai.plus/v1"
    key = Key("./key")
    model = "text-embedding-3-small"

    collection = Collection(key=key, api_base=api_base, embedding_model_name=model)
    print(collection.client.list_collections())
    print(collection.client.count_collections())
    """problem = collection.get(Role_collection.PROBLEM)
    print(problem)

    print(collection.count(Role_collection.PROBLEM))
    for id in problem["ids"]:
        print(id)"""



    """delete_problem()
    print("*********************************")
    print(collection.client.list_collections())
    print(collection.client.count_collections())
    problem = collection.get(Role_collection.PROBLEM)
    print(problem)

    print(collection.count(Role_collection.PROBLEM))
    for id in problem["ids"]:
        print(id)"""

    """delete_problem()
    
    print(collection.client.count_collections())"""
    """ col_name = Role_collection.VERIFIED_LEMMA1
    verifed_lemma = collection.get(col_name)
    print(collection.count(col_name))
    print(verifed_lemma)
    col = collection.get_or_create_collection(col_name)

    metadatas = verifed_lemma["metadatas"]
    ids = verifed_lemma["ids"]
    direct_count = 0
    direct =  []
    indirecct_count = 0
    indirect = []
    subgoal_count = 0
    subgoal = []
    reflection_count = 0
    reflection = []
    print(metadatas)
    print("****************************")
    for count, metadata in enumerate(metadatas):
        if metadata['stage'] == "DIRECT_LEMMA".lower():
            direct_count = direct_count +1
            direct.append(ids[count])
            print(f"direct {ids[count]}")
            print(metadata["proof"])
        elif metadata['stage'] == "INDIRECT_LEMMA".lower():
            indirecct_count = indirecct_count + 1
            indirect.append(ids[count])
            print("****************************")
            #print(metadata["proof"])
            print("****************************")
        elif metadata['stage'] == "SUBGOAL_LEMMA".lower():
            subgoal_count = subgoal_count + 1
            subgoal.append(ids[count])
            print("****************************")
            print(metadata["proof"])
            print("****************************")
        elif metadata['stage'] == "REFLECTION_LEMMA".lower():
            reflection_count = reflection_count + 1
            reflection.append(ids[count])
            print("****************************")
            #print(metadata["proof"])
            print("****************************")
        else:
            print("错误")
            print(metadata)
    print("****************************")"""
    #print(f"""direct_count = {direct_count}\n
#indirecct_count = {indirecct_count}\n
#subgoal_count = {subgoal_count}\n
#reflection_count = {reflection_count}""")

    #print("---------------------------------")
    #print(f"""direct_count = {direct}\n
    #indirecct_count = {indirect}\n
    #subgoal_count = {subgoal}\n
    #reflection_count = {reflection}""")

    """col.update(
        ids=["sorted_insort_key_snd_rename"],
        metadatas=[{'class': 'priority_queue', 'index': 28, 'proof': 'lemma sorted_insort_key_snd_rename:\n  assumes "sorted (map snd (alist_of q))"\n  shows "sorted (map snd (insort_key snd (v, a) (alist_of q)))"\n  (* Base Case: Empty list *)\nproof (cases "alist_of q")\n  case Nil\n  then show ?thesis\n    by auto\nnext\n  (* Inductive Step *)\n  case (Cons x xs)\n  then show ?thesis\n  proof (induction xs)\n    case Nil\n    then show ?case\n      by (metis assms sorted_insort_key_alist_of)\n  next\n    case (Cons y ys)\n    then show ?case\n    proof (cases "a \\<le> snd x")\n      case True\n      then show ?thesis\n        by (simp add: assms sorted_insort_key_alist_of)\n    next\n      case False\n      then show ?thesis\n        by (simp add: assms sorted_insort_key_alist_of)\n    qed\n  qed\nqed', 'stage': 'reflection_lemma', 'theorem': 'push_commute'}
],
        documents=['lemma sorted_insort_key_snd_rename:\n  assumes "sorted (map snd (alist_of q))"\n  shows "sorted (map snd (insort_key snd (v, a) (alist_of q)))'],
    )"""
    """print(collection.similarity_distance(Role_collection.VERIFIED_LEMMA, "lemma values_push_preserves_existing_element:
  assumes "v \<in> set (values q)"
  shows "values (push v a q) = values q" "))"""
    """col.delete(
        where={"index": 30}
    )"""

    problem = collection.get(Role_collection.PROBLEM)
    print(problem)

    print(collection.count(Role_collection.PROBLEM))
    for id in problem["ids"]:
        print(id)
    delete_problem()
    #print(collection.query_similar_lemmas(Role_collection.VERIFIED_LEMMA, """lemma sorted_insort_key_snd_rename:\n  assumes 'sorted (map snd (alist_of q))"\n  shows "sorted (map snd (in """, metadata_class="priority_queue"))
    #reflection alist_of_push_case1 alist_of_remove_min_eq_tl remove_min_preserves_properties  alist_of_push_insort_key
    #log-2024-09-01-08-14-52        log-2024-09-07-09-41-01     log-2024-08-29-15-06-28         og-2024-09-01-08-14-52
