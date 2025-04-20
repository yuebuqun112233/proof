theory pop_remove_elememt_notin_queue
     imports Main "../../priority_queue"
begin





theorem pop_remove_elememt_notin_queue:
  assumes a1:"pop q = Some (v, q1)"
  shows "v \<notin> set (values q1)"
proof -
  (* Step 1: Definition of pop *)
  obtain q' where "q1 = q'" by simp
  (* Step 2: Unfolding the values function *)
  have "values q1 = map fst (alist_of q1)" by (simp add: values_def)
  (* Step 3: Unfolding the alist_of for q1 *)
  have "values q1 = map fst (alist_of (remove_min q))" by (metis \<open>|q1| = map fst (alist_of q1)\<close> assms option.distinct(1) pop_def tl_alist_of_pop)
  (* Step 4: Definition of remove_min *)
  have "alist_of (remove_min q) = tl (alist_of q)" by (metis assms option.distinct(1) pop_def tl_alist_of_pop)
  (* Step 5: Case 1: q is empty *)
  show ?thesis
  proof (cases "is_empty q")
    case True
    hence "q = empty" using non_empty_queue_rename by auto
    hence "alist_of (remove_min q) = []" by (metis True \<open>alist_of (remove_min q) = tl (alist_of q)\<close> list.sel(2) priority_queue.is_empty_def)
    hence "values q1 = []" by (simp add: \<open>|q1| = map fst (alist_of (remove_min q))\<close>)
    thus ?thesis by auto
  next
    (* Step 6: Case 2: q is not empty *)
    case False
    hence "tl (alist_of q) = alist_of q1" by (simp add: assms tl_alist_of_pop)
    hence "values q1 = map fst (tl (alist_of q))" by (simp add: \<open>|q1| = map fst (alist_of q1)\<close>)
    hence "values q1 = map fst (alist_of q1)" by (simp add: \<open>|q1| = map fst (alist_of q1)\<close>)
    thus ?thesis by (metis False \<open>tl (alist_of q) = alist_of q1\<close> assms distinct.simps(2) distinct_fst_alist_of fst_pair_eq list.exhaust_sel list.simps(9) option.sel pop_def priority_queue.is_empty_def priority_queue.min_def)
  qed
qed




end