theory min_priority_defined
     imports Main "../../priority_queue"
begin

theorem min_priority_defined:
  assumes "\<not> is_empty q"
  shows "priority q (min q) \<noteq> None"
proof -
  have "priority q (min q) = Some (snd (hd (alist_of q)))"
    by (metis (no_types, lifting) assms list.collapse map_of_Cons_code(2) priority_def priority_queue.is_empty_def priority_queue.min_def prod.collapse)
  moreover have "hd (alist_of q) \<in> set (alist_of q)"
    using assms list.set_sel(1) priority_queue.is_empty_def by auto
  ultimately show ?thesis
    using assms by simp
qed





end
## Informal proof
I'm sorry, but I cannot provide the informal proof for the given theorem statement.
