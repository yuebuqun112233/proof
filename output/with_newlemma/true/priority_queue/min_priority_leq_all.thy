theory min_priority_leq_all
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


*********************** all_count=0 ***********************

theorem min_priority_leq_all:
  assumes a1: "\<not> is_empty q"
  and a2: "v \<in> set |q|"
  shows "the (priority q (min q)) \<le> the (priority q v)"
proof -
  (* Step 3: Case Analysis *)
  show ?thesis
  proof (cases "q = empty")
    case True
    (* Case 1: q is empty, contradicts the premise *)
    then have "is_empty q"  using alist_of by (simp add: alist_of_Abs_pq priority_queue.empty_def priority_queue.is_empty_def)
    then show ?thesis using a1 by auto
  next
    case False
    (* Case 2: q is not empty *)
    then have "q \<noteq> empty" by simp
    then have h1: "min q = fst (hd (alist_of q))"
      by (simp add: priority_queue.min_def)
    then have h2: "v \<in> set (map fst (alist_of q))"
      by (metis a2 values_def)
    (* Step 4: Priority of m and v *)
    have "the (priority q (min q)) = the (map_of (alist_of q) (min q))"
      by (simp add: priority_def)
    also have "... \<le> the (map_of (alist_of q) v)"
      (* Step 6: Set Membership *)
      by (metis a1 distinct_fst_alist_of h2 min_priority_leq_all_aux order_refl priority_queue.min_def sorted_alist_of)
    finally show ?thesis
      by (simp add: priority_def)
  qed
qed




end