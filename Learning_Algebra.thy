theory Learning_Algebra
  imports Complex_Main "HOL-Algebra.Sym_Groups"

begin

definition one_group :: "nat monoid"
  where "one_group = \<lparr> carrier = {1}, mult = (*), one = 1 \<rparr>"

lemma "card(carrier one_group) = 1"
  by (simp add: one_group_def)

lemma one_group_group: "group one_group"
  by (auto intro!: groupI
        simp add: one_group_def)

lemma subgroup_is_one_group:
  assumes "subgroup H one_group"
  shows "H = carrier one_group"
proof -
  have H_subset: "H \<subseteq> carrier one_group" 
    by (simp add: subgroup.subset assms)
  have only_one_in_h: "a \<noteq> 1 \<Longrightarrow> a \<notin> H"
    by (metis H_subset empty_iff one_group_def partial_object.select_convs(1) singletonD subset_singletonD)
  from this have all_h_is_1: "h \<in> H \<Longrightarrow> h = 1"
    by (metis H_subset in_mono one_group_def partial_object.select_convs(1) singletonD)
  thus ?thesis using all_h_is_1
    by (metis H_subset assms one_group_def partial_object.select_convs(1) subgroup_nonempty subset_singletonD) 
qed

(*
lemma cosets_are_one_group:
  assumes "subgroup H one_group"
  assumes "g \<in> carrier one_group"
  shows "g #> H = carrier one_group"
*)  


  
    

end