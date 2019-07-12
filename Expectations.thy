theory Expectations
imports
 QuantSepCon
begin

section \<open>Misc\<close>

subsection \<open>Stuff about ennreal\<close>


lemma ennreal_mult_divide: "b > 0 \<Longrightarrow> b < (\<infinity>::ennreal) \<Longrightarrow> b * (a / b) = a" 
  apply(cases a; cases b) apply (auto simp: divide_ennreal ennreal_mult[symmetric])
   by (simp add: ennreal_divide_eq_top_iff ennreal_mult_eq_top_iff)    

lemma ennreal_div_one: "x / 1 = (x::ennreal)"
  by (metis ennreal_top_neq_one mult.right_neutral mult_divide_eq_ennreal one_neq_zero)

lemma SUP_plus_subdistrib2:
  "(SUP (h1,h2):A.  f h1 h2 + g h1 h2 :: ennreal) \<le> (SUP (h1,h2):A.  f h1 h2) + (SUP (h1,h2):A.  g h1 h2)"
  apply(rule Sup_least) apply auto 
  apply(rule add_mono) by(auto intro: SUP_upper2)  

lemma SUP_plus_subdistrib_ennreal: "\<And>S. \<And>f g::_\<Rightarrow>ennreal. (SUP x:S. f x + g x) \<le> (SUP x:S. f x) + (SUP x:S. g x)"
      by (simp add: SUP_least SUP_upper add_mono)


subsubsection \<open>some experiments\<close>

experiment
begin 

thm ereal_mult_divide

lemma "(P::_\<Rightarrow>ennreal) h' * (Y (h + h') / P h') = FF \<Longrightarrow> G"
  apply(subst (asm) ennreal_mult_divide) oops

 
lemma "\<infinity> / (\<infinity>::ennreal) = 0"
  by simp

lemma "x / (\<infinity>::ennreal) = 0"
  by simp

lemma "x>0 \<Longrightarrow> x * (\<infinity>::ennreal) = \<infinity>" 
  using ennreal_mult_eq_top_iff by auto

lemma "0 * (\<infinity>::ennreal) = 0"
  by auto

thm ennreal_mult_divide
 

thm mult_left_mono


(* for bool
    "(bot < A \<or> bot < B )" and 2: "(A < top \<or> B < top)"
  is 
    A \<or> B and ~A \<or> ~B
  equiv with
    (A\<and>~B) or (~A\<and>B)
*)


lemma "x>0 \<Longrightarrow> x / 0 = (\<infinity>::ennreal)" by simp    
lemma "x=0 \<Longrightarrow> x / 0 = (0::ennreal)" by simp  

lemma "x / \<infinity> = (0::ennreal)" by simp  

lemma "x = \<infinity> \<Longrightarrow>  \<infinity> / x = (0::ennreal)" using ennreal_top_divide by simp (* AAAHHHH *)
lemma "x < \<infinity> \<Longrightarrow>  \<infinity> / x = (\<infinity>::ennreal)" using ennreal_top_divide by simp

lemma "x=\<infinity> \<Longrightarrow> x - \<infinity> = (\<infinity>::ennreal)" by simp  
lemma "x<\<infinity> \<Longrightarrow> x - \<infinity> = (0::ennreal)" apply simp    
  by (simp add: diff_eq_0_iff_ennreal)  

lemma "x - 0 = (x::ennreal)" by simp    

lemma "x = 0 \<Longrightarrow> 0 - x = (0::ennreal)" by simp   (* AAAHHHH *)
lemma "x > 0 \<Longrightarrow> 0 - x = (0::ennreal)" by simp  



end



section \<open>Instantiating the general theory for specific Domains\<close>

subsection \<open>Ennreal with multiplication\<close>


subsubsection \<open>Interpretation of locale quant_sep_con\<close>

lemma ennreal_inverse_antimono:
  "(a::ennreal) \<le> b \<Longrightarrow> inverse b \<le> inverse a"
  apply(cases a; cases b; cases "a=0"; cases "b=0") 
     apply simp_all
   apply(simp add: inverse_ennreal)   
  using ennreal_neq_top top.extremum_uniqueI by blast   


lemma ennreal_div_antimono:
  "(a::ennreal) \<le> b \<Longrightarrow> c / b \<le> c / a"
  unfolding divide_ennreal_def apply(rule mult_mono)
     apply simp
    apply(rule ennreal_inverse_antimono)
  apply simp apply simp by simp
  

lemma eq79_ennreal: fixes A B C :: ennreal
  shows "(bot < C \<or> bot < B )  \<Longrightarrow> (C < top \<or> B < top) \<Longrightarrow> ( A \<le> B / C) \<longleftrightarrow> A * C \<le> B "
  apply(cases "C<bot")
  subgoal by auto
  apply(cases "C < top")
  subgoal   
    by (metis bot.extremum bot_ennreal divide_less_ennreal  
              ennreal_divide_eq_0_iff ennreal_divide_eq_top_iff
              ennreal_times_divide leD le_less_linear top_greatest)   
  subgoal  
    by (metis bot.extremum_strict bot_ennreal ennreal_divide_top 
              ennreal_mult_eq_top_iff mult_eq_0_iff nn nn_bot not_le)  
  done

interpretation Exp: quant_sep_con "( * )" "1::ennreal"  "(/)"   
  apply standard subgoal  
    by (simp add: ennreal_div_one)  
  subgoal  
    by (simp add: bot_ennreal)  
  subgoal using ennreal_top_divide by simp
  subgoal
    by (simp add: divide_right_mono_ennreal)      
  subgoal for a b c
    using ennreal_div_antimono by simp
  subgoal 
    by (simp add: bot_ennreal)  
  subgoal     
    using SUP_mult_left_ennreal[where f=id] by simp 
  subgoal 
    by (auto simp: mult_mono)  
  subgoal apply(rule eq79_ennreal) by auto
  subgoal 
    by (simp add: bot_ennreal)  
  done

subsubsection \<open>Star and Magic Wand\<close>

abbreviation sep_conj_e (infixr "**\<^sub>e" 35) where "sep_conj_e == Exp.sep_conj_q"
abbreviation sep_impl_e (infixr "-*\<^sub>e" 35) where "sep_impl_e == Exp.sep_impl_qq"
abbreviation "sep_empty\<^sub>e \<equiv> Exp.sep_empty_q"
abbreviation "emb\<^sub>e \<equiv> Exp.emb" 
 
lemma sep_conj_e_def:
  "(P **\<^sub>e Q) = (\<lambda>h. Sup { P x * Q y | x y. h=x+y \<and> x ## y})"
  by (simp add: Exp.sep_conj_q_def)

lemma sep_impl_e_def:
  "(P -*\<^sub>e Q) = (\<lambda>h. INF h': { h'. h ## h' \<and> (bot < P h' \<or> bot < Q (h+h') )
                                \<and> (P h' < top \<or> Q (h+h') < top)}. 
                                    (Q (h + h')) / (P h'))"
  by (simp add: Exp.sep_impl_qq_def)


lemma quant_wand_conservative:
  "(P  \<longrightarrow>* Q) h  \<longleftrightarrow> inf 1 (((emb\<^sub>e P) -*\<^sub>e (emb\<^sub>e Q)) h) = 1"
  using Exp.quant_wand_conservative by blast

lemma sep_impl_q_alt_general:
  "inf 1 ((emb\<^sub>e P -*\<^sub>e Q) h) = inf 1 (INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
  using Exp.sep_impl_q_alt_general by blast 



subsubsection \<open>Star is Commutative Monoid\<close>

lemma sep_conj_e_assoc:
  fixes x y z :: "'a::{sep_algebra} \<Rightarrow> ennreal"
  shows 
   "(x **\<^sub>e (y **\<^sub>e z))  = ((x **\<^sub>e y) **\<^sub>e z)"
  using Exp.star_assoc by blast

lemma sep_conj_e_comm:
  fixes X Y :: "'a::{sep_algebra} \<Rightarrow> ennreal"
  shows  "(X **\<^sub>e Y) = (Y **\<^sub>e X)"
  using Exp.star_comm by blast

lemma sep_conj_e_emp_neutral:
  fixes X   :: "'a::{sep_algebra} \<Rightarrow> ennreal"
  shows "(X **\<^sub>e sep_empty\<^sub>e) = X"
        "(sep_empty\<^sub>e **\<^sub>e X) = X"
  using Exp.emp_neutral by auto

lemma sep_conj_e_left_commute:
  fixes P Q R :: "'a::{sep_algebra} \<Rightarrow> ennreal"
  shows  "(P **\<^sub>e Q **\<^sub>e R) = (Q **\<^sub>e P **\<^sub>e R)"
  using Exp.sep_conj_q_left_commute by auto

lemmas sep_conj_e_c = sep_conj_e_comm sep_conj_e_left_commute

subsubsection \<open>monotonicity of @{term "( **\<^sub>e)"} and  @{term "(-*\<^sub>e)"}\<close>

lemma sep_conj_e_mono:
  fixes X X' :: "'a::{sep_algebra} \<Rightarrow> ennreal"
  shows 
   "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (X **\<^sub>e Y) \<le> (X' **\<^sub>e Y')" 
  using Exp.sep_conj_q_mono by auto 


lemma sep_impl_e_mono: 
  fixes P' P Y' Y :: "'a::{sep_algebra} \<Rightarrow> ennreal"
  shows "P' \<le> P \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (P -*\<^sub>e Y) \<le> (P' -*\<^sub>e Y')"  
  using Exp.sep_impl_q_mono by auto 

subsubsection \<open>adjointness of @{term "( **\<^sub>e)"} and  @{term "(-*\<^sub>e)"}\<close>


lemma sep_conj_sep_impl_e_adjoint:
  fixes X Y Z :: "'a::{sep_algebra} \<Rightarrow> ennreal"
  shows "(X **\<^sub>e Y) \<le> Z \<longleftrightarrow> X \<le> (Y -*\<^sub>e Z)"
  using Exp.adjoint_general by auto 

subsubsection \<open>quantitative modus ponens\<close>

lemma quant_modus_ponens_general:
  shows "( P **\<^sub>e (P -*\<^sub>e X)) \<le> X" 
  using Exp.quant_modus_ponens_general by auto 


subsubsection \<open>Intuitionistic Expectations\<close>

abbreviation "intuitionistic\<^sub>e \<equiv> Exp.intuitionistic_q"
abbreviation sep_true_q ("1\<^sub>e")  where "1\<^sub>e \<equiv> (emb\<^sub>e sep_true)"

lemma intuitionistic_e_emb_intuitionistic_iff: 
  "intuitionistic\<^sub>e (emb\<^sub>e P) \<longleftrightarrow> intuitionistic P"
  using Exp.intuitionistic_q_emb_intuitionistic_iff by auto 

theorem tightest_intuitionistic_expectations_star:
  fixes X :: "'a::{sep_algebra} \<Rightarrow> ennreal"
  shows
    "intuitionistic\<^sub>e (X **\<^sub>e 1\<^sub>e)"
    "X \<le> (X **\<^sub>e 1\<^sub>e)"
    "\<And>X'. intuitionistic\<^sub>e X' \<Longrightarrow> X \<le> X' \<Longrightarrow> (X **\<^sub>e 1\<^sub>e) \<le> X'"
  using Exp.tightest_intuitionistic_expectations_star by auto

lemma tightest_intuitionistic_expectations_wand:
  fixes X :: "'a::{sep_algebra} \<Rightarrow> ennreal"
  shows
    "intuitionistic\<^sub>e (1\<^sub>e -*\<^sub>e X)" 
    "(1\<^sub>e -*\<^sub>e X) \<le> X"
    "\<And>X'. intuitionistic\<^sub>e X' \<Longrightarrow> X' \<le> X \<Longrightarrow>  X' \<le> (1\<^sub>e -*\<^sub>e X)"
  using Exp.tightest_intuitionistic_expectations_wand by auto



end