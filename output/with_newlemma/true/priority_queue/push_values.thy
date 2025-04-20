theory push_values
     imports Main 
begin

typedef (overloaded) ('a, 'b::linorder) pri_queue =
  "{xs :: ('a \<times> 'b) list. distinct (map fst xs) \<and> sorted (map snd xs)}"
  morphisms alist_of Abs_pq
proof -
  have "[] \<in> ?pri_queue" by simp
  then show ?thesis by blast
qed 


definition "values" :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a list" ("|(_)|") where
  "values q = map fst (alist_of q)"

definition push :: "'a \<Rightarrow> 'b::linorder \<Rightarrow> ('a, 'b) pri_queue \<Rightarrow> ('a, 'b) pri_queue" where
  "push k p q \<equiv> Abs_pq (if k \<notin> set (values q)
           then insort_key snd (k, p) (alist_of q)
           else alist_of q)"


*********************** all_count=0 ***********************

theorem push_values:
  "set |push k p q| = set |q| \<union> {k}"
proof -
  (* Unfolding the definition of push *)
  have "set |push k p q| = set (map fst (alist_of (push k p q)))"
    by (simp add: values_def)
  also have "... = set (map fst (if k \<notin> set (values q) then insort_key snd (k, p) (alist_of q) else alist_of q))"
    by (smt (verit) List.finite_set alist_of_inverse distinct_fst_alist_of distinct_insort_key_fst finite_distinct_list list.set_map list.set_sel(1) map_of_alist_of_Abs_pq map_of_eq_dom non_empty_queue push_def sorted_alist_of sorted_insort_key)
  (* Case analysis on whether k is in values q or not *)
  show ?thesis
  proof (cases "k \<in> set (values q)")
    case True
    (* If k is in values q, pushing k doesn't change the set of values *)
    then have "push k p q = q"
      by (simp add: alist_of_inverse push_def)
    then show ?thesis
      using True by auto
  next
    case False
    (* If k is not in values q, pushing k adds k to the set of values *)
    then have "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
      by (simp add: push_abs_pq_relation)
    then have "set |push k p q| = set (map fst (insort_key snd (k, p) (alist_of q)))"
      using False \<open>set (map fst (alist_of (push k p q))) = set (map fst (if k \<notin> set |q| then insort_key snd (k, p) (alist_of q) else alist_of q))\<close> calculation by presburger
    also have "... = set (map fst (alist_of q)) \<union> {k}"
      by (metis Domain_insert Un_insert_right boolean_algebra.disj_zero_right fst_eq_Domain image_set set_insort_key)
    finally show ?thesis
      by (simp add: values_def)
  qed
qed




end