theory min_priority_leq_all_aux
     imports Main
begin

typedef (overloaded) ('a, 'b::linorder) pri_queue =
  "{xs :: ('a \<times> 'b) list. distinct (map fst xs) \<and> sorted (map snd xs)}"
  morphisms alist_of Abs_pq
proof -
  have "[] \<in> ?pri_queue" by simp
  then show ?thesis by blast
qed 


definition is_empty :: "('a, 'b::linorder) pri_queue \<Rightarrow> bool" where
  "is_empty q \<equiv> alist_of q = []"

definition empty :: "('a, 'b::linorder) pri_queue" where 
  "empty \<equiv> Abs_pq []"

definition "values" :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a list" ("|(_)|") where
  "values q = map fst (alist_of q)"

definition priority :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "priority q \<equiv> map_of (alist_of q)"

definition min :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a" where
  "min q \<equiv> fst (hd (alist_of q))"

theorem min_priority_leq_all_aux:
  assumes a1: "sorted (map snd (alist_of q))"
    and a2: "distinct (map fst (alist_of q))"
    and a3: "v \<noteq> fst (hd (alist_of q))"
    and a4: "v \<in> set (map fst (alist_of q))"
  shows "the (map_of (alist_of q) (fst (hd (alist_of q)))) \<le> the (map_of (alist_of q) v)"
proof -
  (* Step 1: Definitions *)
  define min_key where "min_key = fst (hd (alist_of q))"
  
  (* Step 2.1: Analysis of a1 *)
  have min_priority_leq_all: "\<forall>p. (min_key, p) \<in> set (alist_of q) \<longrightarrow> the (map_of (alist_of q) min_key) \<le> p"
    using a1 unfolding min_key_def
    by (simp add: a2)
  
  (* Step 2.2: Analysis of a2 *)
  have v_priority_defined: "\<exists>p. (v, p) \<in> set (alist_of q)"
    using a4 by auto
  
  (* Step 2.3: Analysis of a3 *)
  have min_key_neq_v: "min_key \<noteq> v"
    using a3 unfolding min_key_def
    by auto
  
  (* Step 3: Conclusion *)
  show ?thesis
    using min_priority_leq_all v_priority_defined min_key_neq_v
    by (smt (verit, best) a1 a2 empty_iff empty_set hd_conv_nth in_set_conv_nth length_map length_pos_if_in_set list.set_cases map_of_Cons_code(2) map_of_is_SomeI nth_map option.sel prod.collapse sndI sorted_nth_mono zero_le)
qed





end
## Informal proof
To prove the theorem min_priority_leq_all_aux, we need to carefully analyze the assumptions and the properties of the functions involved. Here's the step-by-step proof in Isabelle with clear English explanations.

Theorem: min_priority_leq_all_aux

Statement:
Given the assumptions:
- a1: q is sorted by priority
- a2: q has distinct keys
- a3: v is not the minimum key in q
- a4: v is present in q
We need to show that the priority of the minimum key in q is less than or equal to the priority of v.

Proof step:
Consider the assumptions:
a1: sorted (map snd (alist_of q))
a2: distinct (map fst (alist_of q))
a3: v ≠ fst (hd (alist_of q))
a4: v ∈ set (map fst (alist_of q))

We need to show:
the (map_of (alist_of q) (fst (hd (alist_of q)))) ≤ the (map_of (alist_of q) v)

Step 1: Definitions
Let's start by defining some key terms and functions used in the theorem:
- q: the priority queue
- alist_of q: the association list representation of q, where each element is a pair (key, priority)
- map_of (alist_of q): a function that returns the priority associated with a given key in the association list representation of q
- fst (hd (alist_of q)): the minimum key in q

Step 2: Analysis
We will analyze the assumptions and the properties of the functions involved to derive the desired conclusion.

Step 2.1: Analysis of a1 - sorted (map snd (alist_of q))
From the assumption a1, we know that the priorities in q are sorted in ascending order. This implies that the priority of the minimum key is less than or equal to the priority of any other key in q.

Step 2.2: Analysis of a2 - distinct (map fst (alist_of q))
From the assumption a2, we know that the keys in q are distinct. This ensures that the map_of function can uniquely associate each key with its priority.

Step 2.3: Analysis of a3 - v ≠ fst (hd (alist_of q))
From the assumption a3, we know that v is not equal to the minimum key in q. This implies that the priority of the minimum key is not equal to the priority of v.

Step 2.4: Analysis of a4 - v ∈ set (map fst (alist_of q))
From the assumption a4, we know that v is present in q. This implies that there exists a priority associated with v in q.

Step 3: Conclusion
Based on our analysis of the assumptions and the properties of the functions involved, we can conclude that the priority of the minimum key in q is less than or equal to the priority of v
