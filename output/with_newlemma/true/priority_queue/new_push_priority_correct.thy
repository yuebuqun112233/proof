theory new_push_priority_correct
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

definition priority :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "priority q \<equiv> map_of (alist_of q)"

definition push :: "'a \<Rightarrow> 'b::linorder \<Rightarrow> ('a, 'b) pri_queue \<Rightarrow> ('a, 'b) pri_queue" where
  "push k p q \<equiv> Abs_pq (if k \<notin> set (values q)
           then insort_key snd (k, p) (alist_of q)
           else alist_of q)"

(*log-2024-08-31-14-58-43.txt*)
*********************** all_count=0 ***********************

theorem new_push_priority_correct:
  assumes a1:"k \<notin> set |q|"
  shows "priority (push k p q) k = Some p"
proof -
  (* Step 1: Unfolding the push function *)
  have "push k p q = Abs_pq (if k \<notin> set (values q) then insort_key snd (k, p) (alist_of q) else alist_of q)"
    by (simp add: push_def)
  (* Step 2: Case Analysis on k \<notin> set (values q) *)
  show ?thesis
  proof (cases "k \<notin> set (values q)")
    (* Step 2.1: Assume k \<notin> set (values q) is true *)
    case True
    (* In this case, the if statement in the push definition evaluates to true *)
    then have "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
      by (simp add: \<open>push k p q = Abs_pq (if k \<notin> set |q| then insort_key snd (k, p) (alist_of q) else alist_of q)\<close>)
    (* Show priority (push k p q) k = Some p *)
    then have "priority (push k p q) k = map_of (insort_key snd (k, p) (alist_of q)) k"
       using alist_of using assms k_notin_set_values by fastforce
    (* Since k \<notin> set (values q), it follows that k is not already present in the priority queue *)
    then have "map_of (insort_key snd (k, p) (alist_of q)) k = Some p"
      by (metis assms distinct_fst_alist_of map_of_insort_key priority_queue.is_empty_def push_empty_list sorted_alist_of values_def)
    (* Hence, priority (push k p q) k = Some p *)
    then show ?thesis
      by (simp add: \<open>priority (push k p q) k = map_of (insort_key snd (k, p) (alist_of q)) k\<close>)
  next
    (* Step 3: Case Analysis on k \<notin> set (values q) *)
    case False
    (* In this case, the if statement in the push definition evaluates to false *)
    then have "push k p q = Abs_pq (alist_of q)"
      by (simp add: assms)
    (* Show priority (push k p q) k = Some p *)
    then have "priority (push k p q) k = map_of (alist_of q) k"
      using False assms by blast
    (* Since k \<notin> set (values q), it follows that k is not already present in the priority queue *)
    then have "map_of (alist_of q) k = Some p"
      using False assms by blast
    (* Hence, priority (push k p q) k = Some p *)
    then show ?thesis
      by (simp add: \<open>priority (push k p q) k = map_of (alist_of q) k\<close>)
  qed
qed




end