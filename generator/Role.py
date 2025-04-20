from enum import Enum


class Role(Enum):
    ####中间引理

    ## 直接请求中间引理
    DIRECT_LEMMA= 1

    ## 间接请求中间引理
    INDIRECT_LEMMA = 2

    ## 形式化子目标请求中间引理
    SUBGOAL_LEMMA = 3

    ## 请求非形式证明
    INFORMAL = 4

    ## 请求形式证明
    FORMAL = 5

    #### 无需中间引理

    ## 请求非形式证明
    INFORMALIZER = 6

    ## 请求形式证明
    FORMALIZER = 7

    ## 反思引理
    REFLECTION_LEMMA = 8

    NONE = 9

if __name__ == '__main__':
    print(Role.SUBGOAL_LEMMA.name == "SUBGOAL_LEMMA".lower())
    print("SUBGOAL_LEMMA".lower())