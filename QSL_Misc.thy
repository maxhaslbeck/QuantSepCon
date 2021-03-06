\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
chapter \<open>Miscellaneous for QSL\<close>
theory QSL_Misc
  imports   Sep_Algebra_Add
  "HOL-Library.Extended_Nonnegative_Real"
begin


paragraph \<open>Summary\<close>

text \<open>This theory collects some miscellaneous material for the verification of
     Quantitative Separation Logic (QSL).\<close>


section \<open>Misc\<close>





subsection \<open>stuff about complete lattices:\<close>


lemma nn: "(\<not> x < (top::'b::{complete_lattice})) = (x = top)" 
  using top.not_eq_extremum by blast
lemma nn_bot: "(\<not> x > (bot::'b::{complete_lattice})) = (x = bot)" 
  using bot.not_eq_extremum by blast


thm Inf_mono
(* I think this rule is actually stronger than Inf_mono *)
lemma (in complete_lattice) 
  assumes "\<And>b. b \<in> B \<Longrightarrow> b < top \<Longrightarrow> \<exists>a\<in>A. a \<le> b"
  shows Inf_mono_strong: "Inf A \<le> Inf B"
proof (rule Inf_greatest)
  fix b assume bB: "b \<in> B"
  show "Inf A \<le> b" proof (cases "b<top")
    case True       
    with bB assms obtain a where "a \<in> A" and "a \<le> b" by blast
    from \<open>a \<in> A\<close> have "Inf A \<le> a" by (rule Inf_lower)

    with \<open>a \<le> b\<close>  show ?thesis  by simp
  next
    case False 
    then have "b=top" 
      using top.not_eq_extremum by blast  
    then show ?thesis  by simp
  qed
qed 

subsection \<open>Stuff about SUP and various operations\<close>


lemma Sup_cong: "\<And>S S'. S=S' \<Longrightarrow> Sup S = Sup S'"
  by simp

lemma SUP_plus_subdistrib: "\<And>S. \<And>f g::_\<Rightarrow>'b::{complete_lattice,ordered_ab_semigroup_add }. (SUP x\<in>S. f x + g x) \<le> (SUP x\<in>S. f x) + (SUP x\<in>S. g x)"
  by (simp add: SUP_least SUP_upper add_mono)




term sup_continuous
thm mult_mono

text \<open>enable multiplication on functions\<close>

instance "fun" :: (type,zero) zero
  by standard  

instantiation "fun" :: (type,times) times
begin
definition [simp]: "(f1 * f2) x = f1 x * f2 x"
instance by standard
end 
 

end