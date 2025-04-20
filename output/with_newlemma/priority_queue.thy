theory priority_queue
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


definition priorities :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'b list" ("\<parallel>(_)\<parallel>") where
  "priorities q = map snd (alist_of q)"


definition is_empty :: "('a, 'b::linorder) pri_queue \<Rightarrow> bool" where
  "is_empty q \<equiv> alist_of q = []"


definition priority :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "priority q \<equiv> map_of (alist_of q)"


definition min :: "('a, 'b::linorder) pri_queue \<Rightarrow> 'a" where
  "min q \<equiv> fst (hd (alist_of q))"


definition empty :: "('a, 'b::linorder) pri_queue" where
  "empty \<equiv> Abs_pq []"


definition push :: "'a \<Rightarrow> 'b::linorder \<Rightarrow> ('a, 'b) pri_queue \<Rightarrow> ('a, 'b) pri_queue" where
  "push k p q \<equiv> Abs_pq (if k \<notin> set (values q)
           then insort_key snd (k, p) (alist_of q)
           else alist_of q)"


definition remove_min :: "('a, 'b::linorder) pri_queue \<Rightarrow> ('a, 'b::linorder) pri_queue" where
  "remove_min q \<equiv> (if is_empty q then empty else Abs_pq (tl (alist_of q)))"


definition pop :: "('a, 'b::linorder) pri_queue \<Rightarrow> ('a \<times> ('a, 'b) pri_queue) option" where
  "pop q = (if is_empty q then None else Some (min q, remove_min q))"

 lemma dom_map_of_alist_of:
  shows "dom (map_of (alist_of q)) = set (map fst (alist_of q))"
proof -
  (* Step 2: Analysis of dom (map_of (alist_of q)) *)
  have h1: "dom (map_of (alist_of q)) = {k. map_of (alist_of q) k \<noteq> None}"
    by (simp add: dom_def)
  (* Step 3: Analysis of set (map fst (alist_of q)) *)
  have h2: "set (map fst (alist_of q)) = {k. \<exists>v. (k, v) \<in> set (alist_of q)}"
    by (smt (verit) Collect_cong domD dom_map_of_conv_image_fst h1 list.set_map map_of_SomeD mem_Collect_eq set_zip_leftD zip_map_fst_snd)
  (* Step 4: Establishing equality *)
  (* Step 4.1: Showing that every element in dom (map_of (alist_of q)) is an element in set (map fst (alist_of q)) *)
  have h3: "\<forall>k. k \<in> dom (map_of (alist_of q)) \<longrightarrow> k \<in> set (map fst (alist_of q))"
    by (simp add: dom_map_of_conv_image_fst)
  (* Step 4.2: Showing that every element in set (map fst (alist_of q)) is an element in dom (map_of (alist_of q)) *)
  have h4: "\<forall>k. k \<in> set (map fst (alist_of q)) \<longrightarrow> k \<in> dom (map_of (alist_of q))"
    by (simp add: dom_map_of_conv_image_fst)
  (* Combining the results *)
  from h1 h2 h3 h4 show ?thesis
    by blast
qed

lemma key_in_list:
  assumes a1: "v \<in> set |q|"
  shows "v \<in> set (map fst (alist_of q))"
proof -
  (* Step 1: Definition of values and alist_of *)
  have h1: "values q = map fst (alist_of q)" by (simp add: values_def)
  
  (* Step 2: Mapping the value v *)
  from a1 have "v \<in> set (values q)" by simp
  
  (* Step 3: Conclusion *)
  with h1 show "v \<in> set (map fst (alist_of q))" by simp
qed

lemma ordering_of_values:
  assumes a1: "the (map_of (alist_of q) (priority_queue.min q)) \<le> the (map_of (alist_of q) v)"
  shows "the (priority q (priority_queue.min q)) \<le> the (priority q v)"
proof -
  have "the (priority q (priority_queue.min q)) = the (map_of (alist_of q) (priority_queue.min q))"
    by (simp add: priority_def)
  also have "\<dots> \<le> the (map_of (alist_of q) v)"
    by (simp add: assms)
  finally show ?thesis
    by (simp add: priority_def)
qed

lemma distinct_fst_alist_of:
  assumes "\<not> is_empty q"
  shows "distinct (map fst (alist_of q))"
proof (cases "alist_of q")
  case Nil
  then have "is_empty q" by (simp add: priority_queue.is_empty_def)
  then show ?thesis by (simp add: assms)
next
  case (Cons a list)
  then have "q \<noteq> empty"  using alist_of by (metis (no_types, lifting) Abs_pq_inverse assms distinct.simps(1) map_is_Nil_conv mem_Collect_eq priority_queue.empty_def priority_queue.is_empty_def sorted0)
  then have "distinct (map fst (alist_of q))"  using alist_of by auto
  then show ?thesis by simp
qed

lemma non_empty_queue:
  assumes a1: "v \<in> set (map fst (alist_of q))"
  shows "\<not> is_empty q"
proof -
  (* Step 1: By the definition of is_empty *)
  have h1: "is_empty q \<equiv> alist_of q = []" 
    by (simp add: priority_queue.is_empty_def)
  
  (* Step 2: By the definition of alist_of *)
  have h2: "alist_of q \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}"
    using alist_of by auto
    
  (* Step 3: By the assumption a1 *)
  have h3: "v \<in> set (map fst (alist_of q))"
    using assms by auto
    
  (* Step 4: By the set membership definition *)
  then obtain p where h4: "(v, p) \<in> set (alist_of q)"
    by auto
    
  (* Step 5: Since (v, _) is in the list (alist_of q), the list (alist_of q) is not empty *)
  then have h5: "alist_of q \<noteq> []"
    by auto
    
  (* Step 6: Therefore, alist_of q is not empty *)
  then have h6: "alist_of q \<noteq> []"
    by simp
    
  (* Step 7: Since alist_of q is not empty, is_empty q is False *)
  then have h7: "\<not> is_empty q"
    using h1 by auto
    
  (* Step 8: Conclusion *)
  show ?thesis
    by (simp add: h7)
qed

lemma remove_min_preserves_properties:
  assumes "\<not> is_empty q"
  shows "distinct (map fst (alist_of (remove_min q)))"
    and "sorted (map snd (alist_of (remove_min q)))"
proof -
  have h1: "remove_min q = Abs_pq (tl (alist_of q))"
    unfolding remove_min_def by (simp add: assms)
  have h2: "distinct (map fst (alist_of (remove_min q)))"
    unfolding h1
    using distinct_fst_alist_of priority_queue.is_empty_def by force
  have h3: "sorted (map snd (alist_of (remove_min q)))"
    unfolding h1
    using alist_of by blast
  show "distinct (map fst (alist_of (remove_min q)))" by (simp add: h2)
  show "sorted (map snd (alist_of (remove_min q)))" by (simp add: h3)
qed

lemma distinct_alist_of : "distinct (alist_of q)"
proof -
  have "distinct (map fst (alist_of q))" and "sorted (map snd (alist_of q))"using alist_of
    apply auto[1]using alist_of
    by auto
  then show ?thesis by (metis distinct_zipI1 zip_map_fst_snd)
qed

lemma alist_of_Abs_pq:
  assumes "distinct (map fst xs)"
    and "sorted (map snd xs)"
  shows "alist_of (Abs_pq xs) = xs"
proof -
  have "xs \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}" using assms by simp
  then have "Abs_pq (alist_of (Abs_pq xs)) = Abs_pq xs" by (simp add: alist_of_inverse)
  then show ?thesis using Abs_pq_inject assms by (simp add: Abs_pq_inverse)
qed

lemma sorted_alist_of:"sorted (map snd (alist_of q))"
  (* By the definition of alist_of *)
proof -
  have "sorted (map snd (alist_of q))"
    using alist_of
    by auto
  then show ?thesis
    by simp
qed

lemma priority_fst:
  assumes "xp \<in> set (alist_of q)"
  shows "priority q (fst xp) = Some (snd xp)"
proof -
  (* Step 1: Unfold the definition of alist_of *)
  have "xp \<in> set (alist_of q)" by (simp add: assms)
  then have "xp \<in> set (map (\<lambda>(x, y). (x, y)) (alist_of q))" by simp
  then have "xp \<in> set (map (\<lambda>p. (fst p, snd p)) (alist_of q))" by auto
  then have "xp \<in> set (map (\<lambda>p. (fst p, snd p)) (map (\<lambda>(x, y). (x, y)) (alist_of q)))" by simp
  then have "xp \<in> set (map (\<lambda>p. (fst p, snd p)) (alist_of q))" by simp
  then have "xp \<in> set (map (\<lambda>p. (fst p, snd p)) (map (\<lambda>(x, y). (x, y)) (alist_of q)))" by simp
  then have "xp \<in> set (map (\<lambda>p. (fst p, snd p)) (alist_of q))" by simp
  then have "xp \<in> set (map (\<lambda>p. (fst p, snd p)) (alist_of q))" by simp
  (* Step 2: Unfold the definition of priority *)
  then have "xp \<in> set (map (\<lambda>p. (fst p, snd p)) (alist_of q))" by simp
  then have "map_of (map (\<lambda>p. (fst p, snd p)) (alist_of q)) (fst xp) = Some (snd xp)" using alist_of map_of_eq_Some_iff by fastforce
  then have "map_of (alist_of q) (fst xp) = Some (snd xp)" by simp
  then show ?thesis by (metis priority_def)
qed

lemma min_priority_leq_all_aux:
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


lemma value_in_alist_of:
  assumes a1: "v \<in> set |q|"
  shows "\<exists>p. (v, p) \<in> set (alist_of q)"
  (* Step 1: Unfold the definition of values *)
proof -
  have h1: "|q| = map fst (alist_of q)"
    unfolding values_def by simp
  (* Step 2: Rewrite the assumption *)
  from a1 have "v \<in> set (map fst (alist_of q))"
    using h1 by auto
  (* Step 3: Use the map property *)
  then obtain p where "(v, p) \<in> set (alist_of q)"
    by force
  (* Step 4: Conclusion *)
  then show ?thesis
    by auto
qed


lemma value_in_map_of_alist_of:
  assumes "v \<in> set (values q)"
  shows "\<exists>p. map_of (alist_of q) v = Some p"
proof -
  (* Step 4: Using map_of on alist_of q *)
  have "map_of (alist_of q) v \<noteq> None" 
    using assms
    unfolding values_def
    by (simp add: map_of_eq_None_iff)
  (* Step 5: Conclusion *)
  then obtain p where "map_of (alist_of q) v = Some p"
    by blast
  thus ?thesis 
    by simp
qed


lemma priority_leq_same:
  assumes a1: "sorted (map snd (alist_of q))"
    and a2: "distinct (map fst (alist_of q))"
    and a3: "v \<noteq> fst (hd (alist_of q))"
    and a4: "v \<in> set (map fst (alist_of q))"
  shows "the (map_of (alist_of q) (fst (hd (alist_of q)))) \<le> the (map_of (alist_of q) v)"
proof -
  have "(fst (hd (alist_of q))) \<in> set (map fst (alist_of q))"
    using a2 by (metis a4 empty_set equals0D list.map_sel(1) list.set_sel(1) list.simps(8))
  moreover have "v \<in> set (map fst (alist_of q))"
    using a4 by simp
  moreover have "the (map_of (alist_of q) (fst (hd (alist_of q)))) \<le> the (map_of (alist_of q) v)"
    using a1 a2 a3 by (smt (verit) a4 empty_iff empty_set hd_conv_nth in_set_conv_nth length_map length_pos_if_in_set map_of_zip_nth nth_map option.sel sorted_nth_mono zero_le zip_map_fst_snd)
  ultimately show ?thesis by blast
qed


theorem push_empty_list:
  assumes "alist_of q = []"
  shows "priority (push k p q) k = Some p"
proof -
  (* Step1: Unfold the priority and push functions *)
  have h1: "priority (push k p q) k = map_of (alist_of (push k p q)) k"
    by (simp add: priority_def)
  have h2: "alist_of (push k p q) = insort_key snd (k, p) []"
     using alist_of by (simp add: alist_of_Abs_pq assms push_def values_def)
  have h3: "map_of (insort_key snd (k, p) []) k = Some p"
    by auto
  (* Step2: Substitute the values in Step1 with the values in Step2 *)
  then have "priority (push k p q) k = Some p"
    by (simp add: h1 h2)
  then show ?thesis by simp
qed

lemma push_eq_Abs_pq:
  assumes "k \<notin> set (values q)"
  shows "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
proof -
  (* Step 1: Case Analysis on k \<notin> set (values q) *)
  show ?thesis
  proof (cases "k \<notin> set (values q)")
    case True
    (* Step 2: Case 1: k \<notin> set (values q) *)
    have h1: "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
      unfolding push_def by (simp add: assms)
    (* Step 3: Conclusion *)
    then show ?thesis by simp
  next
    case False
    (* Step 2: Case 2: k \<in> set (values q) *)
    then have h2: "push k p q = q"
      unfolding push_def by (simp add: assms)
    (* Step 3: Conclusion *)
    then show ?thesis using False assms by blast
  qed
qed

lemma push_Abs_pq:
  assumes "k \<notin> set (values q)"
  shows "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
  (* Step 1: Assume that k is not in the set of values of q *)
proof -
  (* Step 2: By the definition of push, when k is not in set (values q), push k p q is defined as Abs_pq (insort_key snd (k, p) (alist_of q)) *)
  have "push k p q = Abs_pq (if k \<notin> set (values q) then insort_key snd (k, p) (alist_of q) else alist_of q)"
    unfolding push_def by simp
  (* Step 3: We need to show that push k p q is equal to Abs_pq (insort_key snd (k, p) (alist_of q)) *)
  moreover have "Abs_pq (if k \<notin> set (values q) then insort_key snd (k, p) (alist_of q) else alist_of q) = Abs_pq (insort_key snd (k, p) (alist_of q))"
  proof(cases "k \<notin> set (values q)")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "push k p q = Abs_pq (alist_of q)"
      unfolding push_def by simp
    also have "... = q"
      by (simp add: alist_of_inverse)
    finally have "push k p q = q" .
    moreover have "Abs_pq (insort_key snd (k, p) (alist_of q)) = q"
      using False assms by auto
    ultimately show ?thesis
      by (simp add: assms)
  qed
  (* Step 4: By the assumption that k is not in the set of values of q, we can conclude that push k p q is equal to Abs_pq (insort_key snd (k, p) (alist_of q)) *)
  ultimately show ?thesis
    by simp
qed

lemma push_abs_pq_relation:
  assumes "k \<notin> set (values q)"
  shows "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
  (* Step 1: Expand the definition of push *)
proof -
  (* Step 2: Case analysis on `k \<notin> set (values q)` *)
  show ?thesis
  proof (cases "k \<notin> set (values q)")
    case True
    then have "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
      by (simp add: push_eq_Abs_pq)
    then show ?thesis by simp
  next
    case False
    then have "push k p q = Abs_pq (alist_of q)"
      by (simp add: assms)
    also have "... = Abs_pq (insort_key snd (k, p) (alist_of q))"
      using False assms by auto
    finally show ?thesis by simp
  qed
qed

lemma sorted_insort_key_alist_of:
  assumes "sorted (map snd (alist_of q))"
  shows "sorted (map snd (insort_key snd (k, p) (alist_of q)))"
proof(induction "alist_of q" arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have IH: "sorted (map snd (insort_key snd (k, p) xs))" by (metis list.sel(3) map_tl priorities_def sorted_alist_of sorted_insort_key sorted_tl)
  show ?case
  proof(cases "snd x \<le> p")
    case True
    then show ?thesis by (simp add: sorted_alist_of sorted_insort_key)
  next
    case False
    then show ?thesis by (simp add: sorted_alist_of sorted_insort_key)
  qed
qed

lemma push_preserves_properties:
  assumes "distinct (map fst (alist_of q))"
    and "sorted (map snd (alist_of q))"
    and "k \<notin> set (values q)"
  shows "distinct (map fst (alist_of (push k p q)))"
    and "sorted (map snd (alist_of (push k p q)))"
proof -
  (* Step 1: Establish the properties of the initial queue q *)
  have props_q: "distinct (map fst (alist_of q))" and "sorted (map snd (alist_of q))"
    apply (simp add: assms(1))
by (simp add: assms(2))

  (* Step 2: Evaluate push when the element k is not in the queue *)
  have push_not_in_q: "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
    by (simp add: assms(3) push_abs_pq_relation)
  (* Step 3: Show that the properties are preserved after the push operation *)
  (* Step 4: Evaluate push k p q *)
  have keys_distinct: "distinct (map fst (alist_of (push k p q)))"
    unfolding push_not_in_q
    using distinct_fst_alist_of priority_queue.is_empty_def by force
  (* Step 5: Prove distinctness of keys *)
  have priorities_sorted: "sorted (map snd (alist_of (push k p q)))"
    unfolding push_not_in_q
    by (simp add: sorted_alist_of)
  (* Step 6: Prove sortedness of priorities *)
  (* Conclusion *)
  show "distinct (map fst (alist_of (push k p q)))"
    by (simp add: keys_distinct)
  show "sorted (map snd (alist_of (push k p q)))"
    by (simp add: priorities_sorted)
qed

lemma sorted_distinct_alist_of_Abs_pq:
  assumes "distinct (map fst xs)"
    and "sorted (map snd xs)"
  shows "distinct (map fst (alist_of (Abs_pq xs)))" (* Proof of distinct values *)
    and "sorted (map snd (alist_of (Abs_pq xs)))"  (* Proof of sorted priorities *)
proof -
  (* Proof of distinct values *)
  have "alist_of (Abs_pq xs) = xs" by (simp add: alist_of_Abs_pq assms(1) assms(2))
  then show "distinct (map fst (alist_of (Abs_pq xs)))" by (simp add: assms(1))

  (* Proof of sorted priorities *)
  have "alist_of (Abs_pq xs) = xs" by (simp add: \<open>alist_of (Abs_pq xs) = xs\<close>)
  then show "sorted (map snd (alist_of (Abs_pq xs)))" by (simp add: assms(2))
qed

lemma fst_pair_eq: "fst (k, p) = k"
proof -
  (* Step 1: By the definition of fst, we have fst (k, p) = k. *)
  have "fst (k, p) = k" by simp
  (* Step 2: Therefore, we have shown that fst (k, p) = k, which completes the proof. *)
  then show ?thesis by simp
qed

theorem map_of_insort_key:
  assumes "distinct (map fst xs)" and "sorted (map snd xs)" and "k \<notin> set (map fst xs)"
  shows "map_of (insort_key snd (k, p) xs) k = Some p"
proof (cases "k \<notin> set (map fst xs)")
  case True
    (* Step 2.1: Case k \<notin> set (map fst xs) = True *)
  have h1: "map_of (insort_key snd (k, p) xs) k = map_of ((k, p) # xs) k"
    by (metis (mono_tags, lifting) True assms(1) distinct.simps(2) distinct_insort distinct_map fst_conv list.simps(15) list.simps(9) map_of_inject_set set_insort_key)
    (* Step 2.1.1: Proving map_of ((k, p) # xs) k = Some p *)
  have h2: "map_of ((k, p) # xs) k = Some p"
    by simp
    (* Step 3: Conclusion *)
  then show ?thesis
    by (simp add: h1)
next
  case False
    (* Step 2.2: Case k \<notin> set (map fst xs) = False *)
  have h3: "map_of (insort_key snd (k, p) xs) k = map_of xs k"
    using False assms(3) by auto
    (* Step 2.2.1: Proving map_of xs k = Some p *)
  have h4: "map_of xs k = None"
    using False assms(3) by auto
  then show ?thesis
    using False assms(3) by auto
qed

lemma sorted_insort_key_snd:
  assumes a1: "sorted (map snd (alist_of q))"
    and a2: "distinct (map fst (alist_of q))"
  shows "sorted (map snd (insort_key snd (k, p) (alist_of q)))"
proof(induction "alist_of q" arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons a list)
  then have a3: "sorted (map snd list)"
    by (metis list.simps(9) sorted_alist_of sorted_simps(2))
  have a4: "distinct (map fst list)"
    by (metis Cons.hyps(2) distinct.simps(2) distinct_fst_alist_of list.discI list.simps(9) priority_queue.is_empty_def)
  show ?case
  proof (cases "p \<le> snd a")
    case True
    then have "sorted (map snd (insort_key snd (k, p) (a # list)))"
      by (simp add: Cons.hyps(2) sorted_alist_of sorted_insort_key_alist_of)
    then show ?thesis
      by (simp add: Cons.hyps(2))
  next
    case False
    then have "sorted (map snd (insort_key snd (k, p) list))"
      by (simp add: a3 sorted_insort_key)
    then show ?thesis
      by (simp add: sorted_alist_of sorted_insort_key_alist_of)
  qed
qed

lemma distinct_insort_key_fst:
  assumes a1: "distinct (map fst (alist_of q))"
    and a2: "k \<notin> set (values q)"
  shows "distinct (map fst (insort_key snd (k, p) (alist_of q)))"
proof -
  (* Step 1: Assumptions *)
  have a1: "distinct (map fst (alist_of q))" by (simp add: a1)
  have a2: "k \<notin> set (values q)" by (simp add: a2)

  (* Step 2: Definition of insort_key *)
  define xs' where "xs' = insort_key snd (k, p) (alist_of q)"

  (* Step 3: Mapping keys *)
  have map_fst_xs': "map fst xs' = map fst (insort_key snd (k, p) (alist_of q))" by (simp add: xs'_def)

  (* Step 4: Distinctness Preservation *)
  {
    assume "k \<in> set (map fst (alist_of q))"
    then have "distinct (map fst xs')" by (metis a2 values_def)
  }
  moreover
  {
    assume "k \<notin> set (map fst (alist_of q))"
    then have "distinct (map fst xs')" by (metis a1 distinct_insort distinct_map dom_map_of_alist_of fst_conv fun_upd_triv graph_domD graph_map_of_if_distinct_dom graph_map_upd image_set inj_on_fst_graph map_fst_xs' map_of_eq_None_iff set_insort_key)
  }
  ultimately show ?thesis using xs'_def by blast
qed

lemma map_of_alist_of_Abs_pq:
  assumes a1: "distinct (map fst xs)"
    and a2: "sorted (map snd xs)"
  shows "map_of (alist_of (Abs_pq xs)) = map_of xs"
proof -
  (* Step 1: Given the assumptions *)
  have "distinct (map fst xs)" and "sorted (map snd xs)" apply (simp add: a1)
by (simp add: a2)

  (* Step 2: Apply the definition of alist_of *)
  then have "alist_of (Abs_pq xs) = xs" using alist_of_Abs_pq by auto
  (* Step 3: Substitute the result *)
  then have "map_of (alist_of (Abs_pq xs)) = map_of xs" by simp
  (* Step 4: Apply the definition of map_of *)
  then have "map_of (alist_of (Abs_pq xs)) = map_of xs" by simp
  (* Step 5: Substitute xs *)
  then show ?thesis by simp
qed

lemma k_notin_set_values:
  assumes a1:"k \<notin> set (values q)"
  shows "priority (push k p q) k = map_of (insort_key snd (k, p) (alist_of q)) k"
proof -
  have h1: "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
    by (simp add: assms push_abs_pq_relation)
  show ?thesis
  proof (cases "k \<in> set (values q)")
    case True
    then have h2: "priority (push k p q) k = priority q k"
      by (simp add: assms)
    have h3: "map_of (insort_key snd (k, p) (alist_of q)) k = map_of (alist_of q) k"
      using True assms by auto
    then show ?thesis
      unfolding h2 h3 by (simp add: priority_def)
  next
    case False
    then have h4: "priority (push k p q) k = Some p"
      by (metis (no_types, lifting) alist_of_Abs_pq distinct_fst_alist_of distinct_insort_key_fst h1 map_of_insort_key priority_def priority_queue.is_empty_def push_empty_list sorted_alist_of sorted_insort_key_alist_of values_def)
    have h5: "map_of (insort_key snd (k, p) (alist_of q)) k = Some p"
      by (metis assms distinct_fst_alist_of insort_key.simps(1) map_of_Cons_code(2) map_of_insort_key priority_queue.is_empty_def sorted_alist_of values_def)
    then show ?thesis
      unfolding h4 h5 by simp
  qed
qed

lemma sorted_insort_key_snd_rename:
  assumes "sorted (map snd (alist_of q))"
  shows "sorted (map snd (insort_key snd (v, a) (alist_of q)))"
  (* Base Case: Empty list *)
proof (cases "alist_of q")
  case Nil
  then show ?thesis
    by auto
next
  (* Inductive Step *)
  case (Cons x xs)
  then show ?thesis
  proof (induction xs)
    case Nil
    then show ?case
      by (metis assms sorted_insort_key_alist_of)
  next
    case (Cons y ys)
    then show ?case
    proof (cases "a \<le> snd x")
      case True
      then show ?thesis
        by (simp add: assms sorted_insort_key_alist_of)
    next
      case False
      then show ?thesis
        by (simp add: assms sorted_insort_key_alist_of)
    qed
  qed
qed

lemma values_push_preserves_existing_element:
  assumes "v \<in> set (values q)"
  shows "values (push v a q) = values q"
proof -
  (* Step 1: New Queue Construction *)
  have h1: "push v a q = Abs_pq (alist_of q)"
    by (simp add: assms push_def)
  (* Step 2: Values of the New Queue *)
  have h2: "values (push v a q) = map fst (alist_of (Abs_pq (alist_of q)))"
    by (simp add: h1 values_def)
  then have h3: "... = map fst (alist_of q)"
    by (simp add: alist_of_inverse)
  (* Step 3: Conclusion *)
  then show ?thesis
    by (metis h2 values_def)
qed


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
    

lemma alist_of_push_case1:
  assumes "v \<in> set (values q)"
  shows "alist_of (push v a q) = alist_of q"
proof-
  (* Step 1: Definition of push *)
  have h1: "push v a q = Abs_pq (alist_of q)"
    by (simp add: assms push_def)

  (* Step 2: Mapping alist_of for the New Queue *)
  then have h2: "alist_of (push v a q) = alist_of (Abs_pq (alist_of q))"
    by simp

  (* Step 3: Substituting the Definition of push *)
  then have h3: "alist_of (Abs_pq (alist_of q)) = alist_of q"
    by (simp add: alist_of_inverse)

  (* Step 4: Conclusion *)
  from h1 h2 h3 show ?thesis
    by simp
qed

lemma alist_of_push_case2:
  assumes "v \<notin> set (values q)"
  shows "alist_of (push v a q) = insort_key snd (v, a) (alist_of q)"
proof -
  (* By unfolding the definition of push and empty *)
  have "push v a q = Abs_pq (if v \<notin> set (values q) then insort_key snd (v, a) (alist_of q) else alist_of q)"
    unfolding push_def empty_def by simp
  (* Using the inverse function property alist_of_inverse *)
  then have "alist_of (push v a q) = (if v \<notin> set (values q) then insort_key snd (v, a) (alist_of q) else alist_of q)"
    by (meson alist_of_push_insort_key assms)
  (* Performing a case analysis on the condition v \<notin> set (values q) *)
  then show ?thesis
  proof (cases "v \<notin> set (values q)")
    (* Case 1: v \<notin> set (values q) is True *)
    case True
    then show ?thesis by (simp add: \<open>alist_of (push v a q) = (if v \<notin> set |q| then insort_key snd (v, a) (alist_of q) else alist_of q)\<close>)
  next
    (* Case 2: v \<notin> set (values q) is False *)
    case False
    then have "v \<in> set (values q)" by simp
    then obtain i where "values q ! i = v"
      by (simp add: assms)
    (* By the definition of values *)
    then have "values q = map fst (alist_of q)" using \<open>v \<in> set |q|\<close> assms by auto
    (* By the properties of map *)
    then have "map fst (alist_of q) ! i = v" using \<open>|q| ! i = v\<close> by auto
    (* By the definition of alist_of *)
    then have "fst (alist_of q ! i) = v"
      using \<open>v \<in> set |q|\<close> assms by auto
    (* By the properties of insort_key *)
    then have "insort_key snd (v, a) (alist_of q) = alist_of q"
      using \<open>v \<in> set |q|\<close> assms by auto
    then show ?thesis using \<open>v \<in> set |q|\<close> assms by blast
  qed
qed

lemma push_sortedness_preservation:
  assumes "sorted (map snd (alist_of q))"
  shows "sorted (map snd (alist_of (push w b q)))"
proof -
  (* Step 1: Understanding the push function *)
  (* Step 2: Proof by cases *)
  show ?thesis
  proof (cases "w \<in> set (values q)")
    case True
    (* Step 5: Case 2: w is present in the queue q *)
    then have "push w b q = q" by (simp add: alist_of_inverse push_def)
    then show ?thesis by (simp add: assms)
  next
    case False
    (* Step 3: Case 1: w is not present in the queue q *)
    then have "push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))" by (simp add: push_abs_pq_relation)
    (* Step 4: Proving sortedness preservation for Case 1 *)
    moreover have "sorted (map snd (alist_of q)) \<Longrightarrow> sorted (map snd (insort_key snd (w, b) (alist_of q)))" by (simp add: sorted_insort_key_snd_rename)
    ultimately show ?thesis using sorted_alist_of by auto
  qed
qed

lemma push_distinctness_preservation:
  assumes "distinct (map fst (alist_of q))"
    and "w \<notin> set (values q)"
  shows "distinct (map fst (alist_of (push w b q)))"
proof -
  (* Step 1: Evaluate push when w is not in the list of values *)
  have "push w b q = Abs_pq (if w \<notin> set (values q)
    then insort_key snd (w, b) (alist_of q)
    else alist_of q)" by (simp add: assms(2) push_abs_pq_relation)

  (* Step 2: Show that the resulting list is distinct *)
  (* Step 3: Case Analysis *)
  show ?thesis
  proof (cases "w \<notin> set (values q)")
    (* Step 4: Apply alist_of_inverse *)
    case True
    then have "push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))"
      by (simp add: \<open>push w b q = Abs_pq (if w \<notin> set |q| then insort_key snd (w, b) (alist_of q) else alist_of q)\<close>)

    (* Step 5: Apply distinctness preservation *)
    have "distinct (map fst (insort_key snd (w, b) (alist_of q)))"
      by (simp add: True assms(1) distinct_insort_key_fst)

    (* Step 6: Use insort_key properties *)
    then have "distinct (map fst (alist_of (push w b q)))"
      by (simp add: True assms(1) push_preserves_properties(1) sorted_alist_of)

    then show ?thesis by simp
  next
    case False
    (* Step 7: Conclude *)
    then show ?thesis
      by (simp add: assms(2))
  qed
qed

lemma v_not_equal_w:
  assumes a1: "v \<noteq> w"
  shows "v \<noteq> w"
proof -
  from a1 show "v \<noteq> w" by simp
qed

lemma w_not_in_values_q:
  assumes a1: "w \<notin> set (values q)"
  shows "w \<notin> set (values q)"
proof -
  (* By assumption, we know that w is not in the set of values of q *)
  have h1: "w \<notin> set (values q)" by (simp add: assms)
  (* Since the values of q are obtained by mapping the fst function over the list alist_of q *)
  (* We can rewrite the assumption as: w \<notin> set (map fst (alist_of q)) *)
  (* To prove that w is not in the values of q, we will show that w is not in the set of elements obtained by mapping fst over alist_of q *)
  (* By the definition of the values function, we have values q = map fst (alist_of q) *)
  (* Therefore, to prove that w is not in the values of q, it is sufficient to show that w is not in the set obtained by mapping fst over alist_of q *)
  (* By assumption, we know that w is not in the set obtained by mapping fst over alist_of q: w \<notin> set (map fst (alist_of q)) *)
  (* Therefore, w is not in the values of q: w \<notin> set (values q) *)
  then show ?thesis by auto
qed

lemma sorted_snd_alist_of_q:
  assumes "sorted (map snd (alist_of q))"
  shows "sorted (map snd (alist_of q))"
proof -
  (* Step1: Apply the assumption *)
  from assms show ?thesis
    by simp
qed

lemma w_not_in_values_q_refined:
  assumes "w \<notin> set (values q)"
  shows "w \<notin> set (values q)"
proof -
  from assms show ?thesis by simp
qed

lemma distinct_keys_alist_of_q:
  assumes "distinct (map fst (alist_of q))"
  shows "distinct (map fst (alist_of q))"
proof -
  show ?thesis by (simp add: assms)
qed

lemma sorted_priorities_alist_of_q:
  assumes "sorted (map snd (alist_of q))"
  shows "sorted (map snd (alist_of q))"
proof -
  (* Step 1: Assume that the priorities of the elements in the priority queue q are sorted *)
  have "sorted (map snd (alist_of q))" by (simp add: sorted_alist_of)
  (* Step 2: We need to show that the priorities of the elements in the list representation of q are also sorted *)
  then show "sorted (map snd (alist_of q))" by simp
qed

lemma push_existing_element:
  assumes a1: "w \<in> set (values q)"
  shows "push w b q = q"
proof -
  have "w \<in> set (values q)" by (simp add: assms)
  then have "push w b q = Abs_pq (alist_of q)" by (simp add: push_def)
  also have "... = q"  using alist_of by (simp add: alist_of_inverse)
  finally show ?thesis by simp
qed

lemma push_same_key_unchanged:
  assumes "w \<in> set (values q)"
  shows "push w b q = q"
proof (cases "w \<notin> set (values q)")
  case True
  (* Case 1: w is not already in the set of values of q *)
  have h1: "push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))"
    using True assms by auto
  (* Since w is already in the set of values of q, it implies that w will be in the set of values of push w b q *)
  then have h2: "w \<in> set (values (push w b q))"
    using True assms by auto
  (* Therefore, the push operation will insert w with priority b into the queue q *)
  then show ?thesis
    using True assms by auto
next
  case False
  (* Case 2: w is already in the set of values of q *)
  (* In this case, the push function will return q unchanged *)
  then have "push w b q = q"
    by (simp add: push_existing_element)
  then show ?thesis
    by simp
qed

lemma push_existing_key_unchanged:
  assumes "k \<in> set (values q)"
  shows "push k p q = q"
proof -
  (* Step 1: Definition of push *)
  have "push k p q = Abs_pq (if k \<notin> set (values q) then insort_key snd (k, p) (alist_of q) else alist_of q)"
    by (simp add: push_def)

  (* Step 2: Case Analysis *)
  consider "k \<notin> set (values q)" | "k \<in> set (values q)"
    by auto
  then show ?thesis
  proof cases
    (* Subcase 1: k \<notin> set (values q) *)
    case 1
    then have "push k p q = Abs_pq (insort_key snd (k, p) (alist_of q))"
      by (simp add: assms)
    also have "... = Abs_pq (alist_of q)"
      using "1" assms by auto
    also have "... = q"
      using "1" assms by auto
    finally show ?thesis
      by simp
  next
    (* Subcase 2: k \<in> set (values q) *)
    case 2
    then have "push k p q = Abs_pq (alist_of q)"
      by (simp add: \<open>push k p q = Abs_pq (if k \<notin> set |q| then insort_key snd (k, p) (alist_of q) else alist_of q)\<close>)
    also have "... = q"
      by (simp add: alist_of_inverse)
    finally show ?thesis
      by auto
  qed
qed

lemma Abs_pq_push_commute:
  assumes distinct_values: "v ≠ w" "a ≠ b" "w ∉ set (values q)"
    and h2: "push v a q = Abs_pq (insort_key snd (v, a) (alist_of q))"
    and h3: "push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))"
  shows "Abs_pq (if v ∉ set (values q) then insort_key snd (v, a) (alist_of q) else alist_of q) = Abs_pq (insort_key snd (v, a) (alist_of q))"
proof -
  (* Case Analysis *)
  {
    (* If v is not in the set of values of q *)
    assume h4: "v ∉ set (values q)"
    have "Abs_pq (if v ∉ set (values q) then insort_key snd (v, a) (alist_of q) else alist_of q) = Abs_pq (insort_key snd (v, a) (alist_of q))"
      by (simp add: h4)
  }
  moreover
  {
    (* If v is in the set of values of q *)
    assume h5: "v ∈ set (values q)"
    have "Abs_pq (if v ∉ set (values q) then insort_key snd (v, a) (alist_of q) else alist_of q) = Abs_pq (insort_key snd (v, a) (alist_of q))"
      by (metis h2 push_def)
  }
  ultimately show ?thesis
    by simp
qed

lemma distinct_elements:
  assumes distinct_values: "v \<noteq> w"
  shows "v \<noteq> w"
proof -
  (* Step 1: Given assumption *)
  have h1: "v \<noteq> w" by (simp add: distinct_values)
  (* Step 2: Goal to prove *)
  then show ?thesis by simp
qed

lemma distinct_priorities:
  assumes distinct_values: "a \<noteq> b"
  shows "a \<noteq> b"
proof -
  (* Step 1: By the assumption distinct_values: a ≠ b *)
  have h1: "a \<noteq> b" by (simp add: distinct_values)
  (* Step 2: We aim to show that a ≠ b, which aligns with the statement of the theorem *)
  show "a \<noteq> b" using h1 .
qed

lemma push_same_key_unchanged_rename:
  assumes "v \<in> set (values q)"
  shows "push v a q = q"
proof (cases "v \<in> set (values q)")
  assume "v \<in> set (values q)"
  then show "push v a q = q"
    unfolding push_def values_def
    using alist_of_inverse by auto
next
  assume "\<not> (v \<in> set (values q))"
  then show "push v a q = q" by (simp add: assms)
qed

lemma unique_values_push:
  assumes "distinct (map fst (alist_of q))"
    and "w \<notin> set (values q)"
  shows "distinct (map fst (insort_key snd (w, b) (alist_of q)))"
proof -
  (* Step 1: Proof Setup *)
  have dist: "distinct (map fst (alist_of q))" by (simp add: assms(1))
  have notin: "w \<notin> set (values q)" by (simp add: assms(2))
  
  (* Step 2: Push Operation *)
  define new_q where "new_q = insort_key snd (w, b) (alist_of q)"
  
  (* Step 3: Distinctness Preservation *)
  (* Step 4: Detailed Proof Steps *)
  {
    assume "\<not> distinct (map fst new_q)"
    then obtain x y xs where "new_q = xs @ [(x, y)] @ (w, b) # xs" and "x = w"
      by (simp add: dist distinct_insort_key_fst new_q_def notin)
    then have "w \<in> set (values q)" unfolding new_q_def by (metis \<open>\<not> distinct (map fst new_q)\<close> \<open>new_q = xs @ [(x, y)] @ (w, b) # xs\<close> dist distinct_insort_key_fst)
    then have False by (simp add: notin)
  }
  
  (* Step 5: Conclusion *)
  then show ?thesis using new_q_def by blast
qed

lemma Abs_pq_alist_of_inverse: "A \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)} \<Longrightarrow> alist_of (Abs_pq A) = A"
proof -
  assume "A \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}"
  have "Abs_pq (alist_of (Abs_pq A)) = Abs_pq A" 
    by (simp add: alist_of_inverse)
  then have "alist_of (Abs_pq A) = alist_of (Abs_pq (alist_of (Abs_pq A)))" 
    by simp
  then show ?thesis 
     using alist_of using \<open>A \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}\<close> alist_of_Abs_pq by auto
qed

lemma Abs_pq_inject_same: "A \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)} \<Longrightarrow> B \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)} \<Longrightarrow> (Abs_pq A = Abs_pq B) = (A = B)"
proof -
  assume "A \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}" and "B \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}"
  then have "alist_of (Abs_pq A) = A" and "alist_of (Abs_pq B) = B"
    apply (simp add: Abs_pq_inverse)
using Abs_pq_alist_of_inverse \<open>B \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}\<close> by auto

  then show "(Abs_pq A = Abs_pq B) = (A = B)"
    by metis
qed

lemma push_alist_of: "alist_of (push v a q) \<in> {xs. distinct (map fst xs) \<and> sorted (map snd xs)}"
proof(cases "v \<notin> set (values q)")
  case True
  then have "alist_of (push v a q) = insort_key snd (v, a) (alist_of q)"
    unfolding push_def
    by (metis alist_of_push_insort_key push_def)
  then show ?thesis
    using alist_of by blast
next
  case False
  then have "alist_of (push v a q) = alist_of q"
    unfolding push_def
    by (simp add: alist_of_inverse)
  then show ?thesis
    using alist_of by auto
qed

lemma push_not_in_values:
  assumes "w \<notin> set |q|"
  shows "push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))"
  (* Step 1: Expand the definition of push *)
proof -
  have "push w b q = Abs_pq (if w \<notin> set (values q) then insort_key snd (w, b) (alist_of q) else alist_of q)"
    by (simp add: assms push_abs_pq_relation)
  (* Step 2: Case Analysis on w \<notin> set (values q) *)
  moreover have "w \<notin> set (values q) \<Longrightarrow> push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))"
    (* Case 1: Assume w \<notin> set (values q) = True *)
    using calculation by auto
  moreover have "w \<in> set (values q) \<Longrightarrow> push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))"
    (* Case 2: Assume w \<notin> set (values q) = False *)
  proof -
    assume "w \<in> set (values q)"
    then have "w \<in> set (map fst (alist_of q))"
      by (simp add: assms)
    moreover have "w \<notin> set (map fst (alist_of q))"
      using \<open>w \<in> set |q|\<close> assms by auto
    ultimately show "push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))"
      by auto
  qed
  (* Step 3: Conclusion *)
  ultimately show ?thesis by blast
qed

lemma push_not_in_values_alist_of:
  assumes "w \<notin> set (values q)"
  shows "alist_of (push w b q) = insort_key snd (w, b) (alist_of q)"
  (* Step 1: Definition of push *)
proof -
  have "push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))"
    unfolding push_def by (simp add: assms)
  then have "alist_of (push w b q) = alist_of (Abs_pq (insort_key snd (w, b) (alist_of q)))"
    by simp
  (* Step 2: Unfolding the alist_of for the New Queue *)
  also have "... = insort_key snd (w, b) (alist_of q)"
    by (metis \<open>push w b q = Abs_pq (insort_key snd (w, b) (alist_of q))\<close> alist_of_push_insort_key assms)
  (* Step 3: Properties of Abs_pq and alist_of *)
  finally show ?thesis by simp
qed

lemma push_in_values_alist_of:
  assumes "w \<in> set (values q)"
  shows "alist_of (push w b q) = alist_of q"
proof (cases "is_empty q")
  case True
  then show ?thesis by (simp add: assms push_same_key_unchanged)
next
  case False
  then show ?thesis
  proof (cases "w \<notin> set (values q)")
    case True
    then show ?thesis by (simp add: assms)
  next
    case False
    then show ?thesis by (simp add: alist_of_push_case1)
  qed
qed

lemma insort_key_empty:
  "insort_key f x [] = [x]"
proof -
  (* By the definition of insort_key *)
  have "insort_key f x [] = [x]"
    by simp
  (* Therefore, insort_key f x [] is equal to [x] *)
  then show ?thesis
    by simp
qed

lemma pop_eq_min_imp_eq:
  assumes "pop q = Some (v, q1)" and "v = min q"
  shows "pop q = Some (min q, q1)"
proof-
  (* Unfolding the definition of pop *)
  have h1:"pop q = Some (min q, remove_min q)"
    by (metis assms(1) option.distinct(1) pop_def)
  (* Unfolding the definition of remove_min *)
  then have h2:"remove_min q = q1"
    by (simp add: assms(1))
  (* Using the given assumptions *)
  have h3:"q1 = Abs_pq (tl (alist_of q))" and h4:"v = min q"
    apply (metis assms(1) h2 option.distinct(1) pop_def remove_min_def)
by (simp add: assms(2))

  (* Exploring the head and tail of the list *)
  have h5:"min q = fst (hd (alist_of q))"
    by (simp add: priority_queue.min_def)
  have h6:"v = fst (hd (alist_of q))"
    by (simp add: h4 h5)
  (* Conclusion *)
  then show ?thesis
    by (simp add: assms(1) h4)
qed

lemma equal_min_imp_min_in_pop:
  assumes "pop q = Some (v, q1)" 
    and "v = min q"
  shows "min q = min q"
proof-
  (* Step 1: Unfolding the definition of pop *)
  have h1: "pop q = (if is_empty q then None else Some (min q, remove_min q))"
    by (simp add: pop_def)
  (* Step 2: Case analysis on is_empty q *)
  show ?thesis
  proof(cases "is_empty q")
    (* Step 2.1: Case is_empty q = True *)
    assume a: "is_empty q"
    (* Step 2.1.1: Contradiction *)
    have h2: "pop q = None"
      by (simp add: a h1)
    have h3: "pop q ≠ Some (v, q1)"
      by (simp add: h2)
    then show ?thesis
      by simp
  next
    (* Step 2.2: Case is_empty q = False *)
    assume b: "¬ is_empty q"
    (* Step 3: Comparing v and min q *)
    have h4: "pop q = Some (min q, remove_min q)"
      by (meson b h1)
    then have h5: "v = min q"
      by (simp add: assms(2))
    (* Step 4: Conclusion *)
    then show ?thesis
      by simp
  qed
qed

lemma non_empty_queue_rename:
  assumes "q \<noteq> empty"
  shows "\<not> is_empty q"
proof -
  (* Unfolding definitions *)
  have h1: "empty = Abs_pq []"
    by (simp add: priority_queue.empty_def)
  (* Using the assumption and the definition of empty *)
  from assms and h1 have "q \<noteq> Abs_pq []"
    by metis
  (* Applying the definition of is_empty *)
  then have "alist_of q \<noteq> []"
    by (metis alist_of_inverse)
  (* Converting the inequality to the desired conclusion *)
  then show "\<not> is_empty q"
    by (simp add: priority_queue.is_empty_def)
qed

lemma min_equals_hd_alist_of:
  assumes "is_empty q = False"
  shows "min q = fst (hd (alist_of q))"
  (* 1. Definition of min *)
  (* 2. Unfolding min and hd *)
proof -
  (* 3. Case analysis on the structure of q *)
  show ?thesis
  proof (cases "alist_of q")
    case Nil
    then have "is_empty q = True"
      (* Proof of Nil case *)
      by (simp add: priority_queue.is_empty_def)
    then show ?thesis
      by (simp add: assms)
  next
    case (Cons a list)
    then have "is_empty q = False"
      (* Proof of Cons case *)
      by (simp add: assms)
    then have "min q = fst a"
      (* Proof of unfolding min *)
      by (simp add: local.Cons priority_queue.min_def)
    also have "fst a = fst (hd (alist_of q))"
      by (metis calculation priority_queue.min_def)
    finally show ?thesis by simp
  qed
qed

lemma min_is_hd_alist_of:
  assumes "q1 \<noteq> empty"
    and "sorted (map snd (alist_of q1))"
    and "distinct (map fst (alist_of q1))"
  shows "min q1 = fst (hd (alist_of q1))"
proof -
  (* Step 1: Case analysis on q1 *)
  obtain xs where xs_def: "alist_of q1 = xs"
    by simp
  show ?thesis
  proof(cases xs)
    (* Case 1: xs is empty *)
    assume "xs = []"
    then have "q1 = empty"
      by (metis alist_of_inverse priority_queue.empty_def xs_def)
    then show ?thesis
      by (simp add: assms(1))
  next
    (* Case 2: xs is not empty *)
    fix a list
    assume xs_not_empty: "xs = a # list"
    then have "hd xs = a"
      by simp
    then have "min q1 = fst a"
      by (simp add: priority_queue.min_def xs_def)
    also have "... = fst (hd xs)"
      by (simp add: \<open>hd xs = a\<close>)
    finally show ?thesis
      by (simp add: xs_def)
  qed
qed

lemma remove_min_alist_of_eq_tl:
  assumes "\<not> is_empty q1"
  shows "alist_of (remove_min q1) = tl (alist_of q1)"
proof -
  (* Step 1: Definition of remove_min *)
  have "remove_min q1 = Abs_pq (tl (alist_of q1))"
    unfolding remove_min_def
    by (simp add: assms)
  (* Step 2: Mapping alist_of for the New Queue *)
  then have "alist_of (remove_min q1) = alist_of (Abs_pq (tl (alist_of q1)))"
    by simp
  (* Step 3: Unfolding the alist_of for q1 *)
  also have "... = tl (alist_of q1)"
     using alist_of by (simp add: alist_of_Abs_pq assms distinct_fst_alist_of distinct_tl map_tl sorted_alist_of sorted_tl)
  (* Step 4: Behavior of tl with alist_of *)
  finally have "alist_of (remove_min q1) = tl (alist_of q1)"
    by simp
  (* Step 5: Final Conclusion *)
  then show ?thesis
    by simp
qed

lemma distinct_alist_of_remove_min:
  assumes "\<not> is_empty q"
  shows "distinct (map fst (alist_of (remove_min q)))"
proof -
    (* Step 1: Case Analysis *)
  { 
    assume "\<not> is_empty q"
    (* Step 2: Apply remove_min Definition *)
    then have "remove_min q = Abs_pq (tl (alist_of q))" 
      by (simp add: remove_min_def)
    (* Step 3: Unfold Definitions *)
    then have "map fst (alist_of (remove_min q)) = map fst (tl (alist_of q))"
      using assms remove_min_alist_of_eq_tl by fastforce
    (* Step 4: Prove Distinctness *)
    moreover have "distinct (map fst (tl (alist_of q)))"
      by (metis assms calculation remove_min_preserves_properties(1))
    ultimately have "distinct (map fst (alist_of (remove_min q)))"
      by simp
    }
  then show ?thesis
    by (simp add: assms)
qed

lemma min_hd_alist_of:
  assumes "\<not> is_empty q"
  shows "min q = fst (hd (alist_of q))"
proof -
  (* Unfolding the definition of min *)
  have h1: "min q = fst (hd (alist_of q))"
    unfolding min_def by simp
  (* Applying the hd function to the non-empty list representation *)
  have h2: "hd (alist_of q) = hd (alist_of q)"
    by simp
  (* Simplifying the goal *)
  have h3: "fst (hd (alist_of q)) = fst (hd (alist_of q))"
    by simp
  (* Combining the previous steps *)
  from h1 h2 h3 show ?thesis
    by simp
qed

lemma queue_remove_min_eq:
  assumes "q \<noteq> empty"
  shows "q = push (min q) (the (priority q (min q))) (remove_min q)"
  (* Step 1: Check the non-empty assumption *)
proof-
  (* Step 2: Define the minimum element and priority *)
  let ?m = "min q"
  let ?p = "the (priority q ?m)"
  (* Step 3: Evaluate the push operation *)
  have "push ?m ?p (remove_min q) = Abs_pq (insort_key snd (?m, ?p) (tl (alist_of q)))"
    unfolding push_def remove_min_def min_def priority_def
     using alist_of by (smt (z3) Orderings.order_eq_iff alist_of_Abs_pq assms distinct_alist_of distinct_alist_of_remove_min distinct_fst_alist_of distinct_insort dom_map_of_alist_of graph_domD graph_map_of_if_distinct_dom hd_Cons_tl insort_is_Cons list.set_sel(1) list.set_sel(2) map_of_eq_Some_iff min_priority_leq_all_aux non_empty_queue_rename option.sel priority_queue.is_empty_def prod.collapse remove_min_alist_of_eq_tl sorted_alist_of value_in_alist_of)
  (* Step 4: Verify the equality *)
  have "q = push ?m ?p (remove_min q)"
    by (metis (no_types, lifting) \<open>push (priority_queue.min q) (the (priority q (priority_queue.min q))) (remove_min q) = Abs_pq (insort_key snd (priority_queue.min q, the (priority q (priority_queue.min q))) (tl (alist_of q)))\<close> alist_of_inverse assms distinct_fst_alist_of insort_is_Cons list.collapse list.set_sel(1) list.set_sel(2) min_priority_leq_all_aux option.sel order_refl priority_def priority_fst priority_queue.empty_def priority_queue.is_empty_def priority_queue.min_def prod.collapse set_zip_leftD sorted_alist_of zip_map_fst_snd)
  (* Step 5: Apply Definitions *)
  then show ?thesis by simp
qed

lemma alist_of_remove_min_eq_tl:
  assumes "q \<noteq> empty"
  shows "alist_of (remove_min q) = tl (alist_of q)"
proof (cases "is_empty q")
  case True
  then have "remove_min q = empty" by (simp add: assms non_empty_queue_rename)
  then show ?thesis using True assms non_empty_queue_rename by auto
next
  case False
  then have "remove_min q = Abs_pq (tl (alist_of q))" by (simp add: remove_min_def)
  then show ?thesis using False remove_min_alist_of_eq_tl by blast
qed

lemma pop_Some_imp_ex:
  assumes "pop q = Some (v, q1)"
  shows "\<exists>q'. q1 = q'"
  (* Case Analysis on is_empty q *)
proof (cases "is_empty q")
  case True
  (* If is_empty q is True, pop q should return None *)
  have "pop q = None" by (simp add: True pop_def)
  hence False using assms by auto
  thus ?thesis by simp
next
  case False
  (* If is_empty q is False, pop q = Some (min q, remove_min q) *)
  obtain q' where "q' = Abs_pq (tl (alist_of q))"
    by simp
  (* Unfolding remove_min function *)
  have "q1 = remove_min q" by (metis False assms option.sel pop_def prod.inject)
  (* Resulting queue q' *)
  hence "q1 = q'" by (simp add: False \<open>q' = Abs_pq (tl (alist_of q))\<close> remove_min_def)
  thus ?thesis by simp
qed

lemma distinct_alist_of_rename:
  assumes "distinct (map fst (alist_of q1))"
  shows "distinct (map fst (tl (alist_of (Abs_pq (alist_of q1)))))"
proof -
  (* Step 1: Establishing the properties of q1 *)
  have h1: "distinct (map fst (alist_of q1))" by (simp add: assms)
  
  (* Step 2: Converting alist_of q1 to a priority queue and back to a list *)
  have h2: "alist_of (Abs_pq (alist_of q1)) = alist_of q1" by (simp add: alist_of_inverse)
  
  (* Step 3: Taking the tail of alist_of (Abs_pq (alist_of q1)) *)
  have h3: "tl (alist_of (Abs_pq (alist_of q1))) = tl (alist_of q1)" by (simp add: h2)
  
  (* Step 4: Extracting the keys from the tail of alist_of (Abs_pq (alist_of q1)) *)
  have h4: "map fst (tl (alist_of (Abs_pq (alist_of q1)))) = map fst (tl (alist_of q1))" by (simp add: h2)
  
  (* Step 5: Proving the distinctness of the list of keys in the tail *)
  from h1 have "distinct (map fst (alist_of q1)) \<Longrightarrow> distinct (map fst (tl (alist_of q1)))" by (simp add: distinct_tl map_tl)
  then have "distinct (map fst (tl (alist_of (Abs_pq (alist_of q1)))))" by (simp add: h1 h2)
  
  thus ?thesis by simp
qed

lemma alist_of_Abs_pq_tl:
  "alist_of (Abs_pq (tl (alist_of q))) = tl (alist_of q)"
  (* Proof Step 1: Expand the definitions *)
proof -
  (* Proof Step 2: Use the Abs_pq_inverse lemma *)
  have "alist_of (Abs_pq (tl (alist_of q))) = tl (alist_of q)" by (metis alist_of_inverse list.sel(2) priority_queue.is_empty_def remove_min_alist_of_eq_tl)
  (* Proof Step 3: Conclude *)
  thus ?thesis by simp
qed

lemma tl_alist_of_remove_min:
  assumes "is_empty q1"
  shows "alist_of q1 = tl (alist_of (remove_min q1))"
proof -
  (* Step 1: Assume is_empty q1 *)
  (* Step 2: By the definition of is_empty, we have alist_of q1 = []. *)
  have h1: "alist_of q1 = []"
    using assms priority_queue.is_empty_def by auto
  (* Step 3: By the definition of remove_min, we have remove_min q1 = empty if is_empty q1 is true. *)
  (* Step 4: By the definition of empty, we have empty = Abs_pq []. *)
  (* Step 5: By the definition of alist_of, we have alist_of (Abs_pq []) = []. *)
  (* Step 6: By comparing the left-hand side and right-hand side of the equation in the theorem statement, we can see that alist_of q1 = [] and tl (alist_of (remove_min q1)) = tl (alist_of (Abs_pq [])). Therefore, we have alist_of q1 = tl (alist_of (remove_min q1)), which completes the proof. *)
  then show ?thesis
    by (metis alist_of_remove_min_eq_tl assms list.sel(2) remove_min_def)
qed

lemma tl_alist_of_pop:
  assumes a1: "pop q = Some (v, q1)"
    and a2: "\<not> is_empty q"
  shows "tl (alist_of q) = alist_of q1"
proof -
  (* Step 1: Definition of pop *)
  obtain q' where "pop q = Some (v, q1)" by (simp add: a1)
  (* Step 2: Definition of is_empty *)
  have "is_empty q = False" by (simp add: a2)
  (* Step 3: Mapping alist_of for the New Queue *)
  have "tl (alist_of q) = alist_of (remove_min q)" by (simp add: a2 remove_min_alist_of_eq_tl)
  (* Step 4: Unfolding the definitions *)
  moreover have "q1 = remove_min q" by (metis a1 a2 option.sel pop_def prod.inject)
  (* Step 5: Using remove_min definition *)
  ultimately have "tl (alist_of q) = alist_of q1" by simp
  (* Step 7: Final Conclusion *)
  then show ?thesis by simp
qed

lemma tl_alist_of_pop_rename:
  assumes a1: "pop q = Some (v, q1)"
    and a2: "\<not> is_empty q"
  shows "tl (alist_of q) = alist_of q1"
proof -
  (* Step 1: Given assumptions *)
  (* Step 2: Unfold pop definition *)
  obtain k p where h1:"min q = k" and h2:"remove_min q = q1" by (simp add: a1 a2 alist_of_inverse remove_min_def tl_alist_of_pop)
  (* Step 3: Unfold remove_min definition *)
  have "remove_min q = Abs_pq (tl (alist_of q))" by (simp add: a2 remove_min_def)
  (* Step 4: Apply the definition of remove_min *)
  hence "Abs_pq (tl (alist_of q)) = q1" by (simp add: h2)
  (* Step 5: Apply alist_of_inverse *)
  hence "Abs_pq (alist_of q1) = q1" by (simp add: alist_of_inverse)
  (* Step 6: Conclude the proof *)
  hence "tl (alist_of q) = alist_of q1" by (metis \<open>Abs_pq (tl (alist_of q)) = q1\<close> alist_of_Abs_pq_tl)
  thus ?thesis by simp
qed
(*direct_count = 1

indirecct_count = 15

subgoal_count = 26

reflection_count = 31*)

end