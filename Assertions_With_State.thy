\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
chapter \<open>Quantitative Assertion Language with State\<close>
theory Assertions_With_State
imports Quantitative_Separation_Connectives
begin

paragraph \<open>Summary\<close>

text \<open>In this theory we augment the quantitative assertion language over a separation algebra 
      (we now call "heap") to a an assertion language over a pair of state and heap.

      We lift the quantitative separating connectives to pairs of state and heap.
      \<close>



subsection \<open>Assertion Language With state\<close>


context  quant_sep_con
begin
context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin

lemma plus_fun_alt: "(\<lambda>x. (f1 x + f2 x)) = (f1 + f2)"
  by auto
lemma mult_fun_alt: "(\<lambda>x. (f1 x * f2 x)) = (f1 * f2)"
  by auto

abbreviation embb ("\<lbrakk>_\<rbrakk>") where "embb b \<equiv> (\<lambda>(s,h). emb b s)"
abbreviation embn ("\<lbrakk>~_\<rbrakk>") where "embn b \<equiv> (\<lambda>(s,h). emb (\<lambda>s. \<not> b s) s)"

 


definition
  sep_impl_s_q  (infixr "-\<star>" 60)
  where
  "sep_impl_s_q P Q \<equiv> \<lambda>(s,h). sep_impl_qq (\<lambda>h. P(s,h)) (\<lambda>h. Q(s,h)) h "



definition
  sep_conj_s_q  (infixr "\<star>" 60)
  where
  "P \<star> Q \<equiv> \<lambda>(s,h). sep_conj_q (\<lambda>h. P(s,h)) (\<lambda>h. Q(s,h)) h "


lemma sep_conj_s_q_range: "(emb P \<star> emb Q) (s,h) \<in> {bot, \<^bold>1}"
  unfolding sep_conj_s_q_def 
  using sep_conj_q_range[where P=" (\<lambda>h. P(s,h))" and Q=" (\<lambda>h. Q(s,h))"]
  apply (simp add: emb_def) done

definition "sep_empty_s_q = (\<lambda>(s,h). sep_empty_q h)"

lemma sep_conj_s_q_assoc: 
  fixes x y z :: "_ \<times> 'a \<Rightarrow> 'b"
  shows "(x \<star> (y \<star> z))  = ((x \<star> y) \<star> z) "
  unfolding sep_conj_s_q_def by (auto simp: star_assoc)

lemma sep_conj_s_q_commute:
    "P \<star> Q = Q \<star> P"
  unfolding sep_conj_s_q_def
  apply(rule ext) apply auto apply(subst star_comm) by simp

term sep_empty_q
thm emp_neutral[no_vars]

lemma sep_conj_s_q_neutral:
  fixes X :: "_ \<times> 'a \<Rightarrow> 'b"
  shows "(X \<star> sep_empty_s_q) = X"
  "(sep_empty_s_q \<star> X) = X"
  unfolding sep_conj_s_q_def sep_empty_s_q_def
  by (auto simp: emp_neutral)   



lemma sep_conj_q_left_commute_s:
  fixes P Q R :: "_ * 'a \<Rightarrow> 'b"
  shows  "(P \<star> Q \<star> R) = (Q  \<star> P \<star> R)"
  apply(subst sep_conj_s_q_assoc)
  apply(subst sep_conj_s_q_commute)
  apply(subst sep_conj_s_q_assoc) by simp


lemmas sep_conj_q_s_c = sep_conj_s_q_commute sep_conj_q_left_commute_s

lemma emb_alt: "(\<lambda>h. emb \<phi> (a, h)) = emb (\<lambda>h. \<phi> (a,h))"
  by(auto simp: emb_def)

lemma theorem_3_6_s:
  fixes P Q R :: "_ \<times> 'a \<Rightarrow> 'b"
  shows 
  "P \<star> fsup Q R = (\<lambda>s. sup ((P \<star> Q) s) ((P \<star> R) s))"
  (*  "(P \<star> (\<lambda>s. Q s + R s)) \<le> (\<lambda>s. (P \<star> Q) s + (P \<star> R) s)" *)
  "( (emb \<phi>) \<star> (\<lambda>h. Q h \<^bold>* R h)) h \<le> ((emb \<phi>) \<star> Q) h \<^bold>* ((emb \<phi>) \<star> R) h"
  unfolding sep_conj_s_q_def
  subgoal  apply(rule ext)  
    subgoal for s apply(cases s) apply simp  
      apply(subst theorem_3_6(1)) by auto 
    done 
  subgoal    apply(cases h) apply simp     
    apply(rule order.trans)  
    unfolding emb_alt
     apply(rule theorem_3_6(2)  ) by auto  
  done   


lemma sep_impl_s_q_Rmono:
    "(\<And>h. X h \<le> Y h) \<Longrightarrow> (A -\<star> X) sh \<le> (A -\<star> Y) sh" 
  unfolding sep_impl_s_q_def
  apply(cases sh) apply simp 
  apply(rule sep_impl_q_left_mono) 
  by (auto simp: le_fun_def emb_def)  

lemma sep_impl_s_q_mono:
    "(\<And>sh. B sh \<le> A sh) \<Longrightarrow> (\<And>sh. X sh \<le> Y sh) \<Longrightarrow> (A -\<star> X) sh \<le> (B -\<star> Y) sh" 
  unfolding sep_impl_s_q_def
  apply(cases sh) by(auto intro!: sep_impl_q_mono)
  

lemma sep_conj_s_q_mono:
    "(\<And>sh. A sh \<le> B sh) \<Longrightarrow> (\<And>sh. X sh \<le> Y sh) \<Longrightarrow> (A \<star> X) sh \<le> (B \<star> Y) sh"
    unfolding sep_conj_s_q_def
    apply(cases sh) by (auto intro: sep_conj_q_mono) 

lemma sep_conj_s_q_mono_more:
    "(\<And>h. A (s,h) \<le> B (s,h)) \<Longrightarrow> (\<And>h. X (s,h) \<le> Y (s,h)) \<Longrightarrow> (A \<star> X) (s,h)\<le> (B \<star> Y) (s,h)"
    unfolding sep_conj_s_q_def  by (auto intro: sep_conj_q_mono) 

subsubsection \<open>Adjointness\<close>


lemma adjoint_general'1:
  shows "(\<And>h. (X **q P) h \<le> Y h) \<Longrightarrow> (\<And>h. X h \<le> (P -*qq Y) h)"
  using adjoint_general  unfolding le_fun_def by blast

lemma adjoint_general'2:
  shows "(\<And>h. X h \<le> (P -*qq Y) h) \<Longrightarrow> (\<And>h. (X **q P) h \<le> Y h)"
  using adjoint_general  unfolding le_fun_def by blast

lemma adjoint_general_s:
  shows "(\<forall>h. (X \<star> P) h \<le> Y h) \<longleftrightarrow> (\<forall>h. X h \<le> (P -\<star> Y) h)" 
  unfolding sep_conj_s_q_def sep_impl_s_q_def
  unfolding le_fun_def apply auto
  subgoal     apply(rule adjoint_general'1) by auto 
  subgoal     apply(rule adjoint_general'2) by auto 
  done 
lemma adjoint_general_s_liberal:
  shows "(\<forall>h. (X \<star> P) (s,h) \<le> Y (s,h)) \<longleftrightarrow> (\<forall>h. X (s,h) \<le> (P -\<star> Y) (s,h))" 
  unfolding sep_conj_s_q_def sep_impl_s_q_def
  unfolding le_fun_def apply auto
  subgoal     apply(rule adjoint_general'1) by auto 
  subgoal     apply(rule adjoint_general'2) by auto 
  done 


lemma quant_modus_ponens_general_s:
  shows "( P \<star> (P -\<star> X)) sh \<le> X sh"
proof -
  have "(\<forall>sh. (P -\<star> X) sh \<le> (P -\<star> X) sh)" by simp
  then have "(\<forall>sh. (((P -\<star> X) \<star>  P) sh \<le> X sh))"
    using adjoint_general_s[symmetric, where X="(P -\<star> X)" and P=P and Y=X]  by auto
  then show ?thesis apply(subst sep_conj_s_q_commute) by blast
qed 

subsubsection \<open>Algebraic Laws for * under purity\<close>



definition pure_q :: "(_ * 'a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "pure_q X \<longleftrightarrow> (\<forall>s h1 h2. X (s,h1) = X (s,h2))"

lemma pure_qD: "\<And> s h1 h2. pure_q X \<Longrightarrow>  X (s, h1) = X (s, h2)" 
  unfolding pure_q_def by auto

lemma pure_q_const[simp]: "pure_q (\<lambda>s. x2)" 
  unfolding pure_q_def by auto

lemma pure_q_emmb[simp]: "pure_q (embb b)"
    "pure_q (embn b)"
  unfolding pure_q_def emb_def by auto

lemma pure_q_norm: "pure_q X \<Longrightarrow> X (s,h) = X(s,h')"
  unfolding pure_q_def by auto

lemma pure_q_normto0: "pure_q X \<Longrightarrow> X (s,h) = X(s,0)"
  unfolding pure_q_def by auto

lemma  theorem_3_11_1:
  assumes "pure_q X"
  shows      
  "X sh \<^bold>* Y sh \<le> (X \<star> Y) sh"
  unfolding sep_conj_s_q_def sep_conj_q_alt
  apply(cases sh)
  apply auto
  subgoal for s h 
    apply(rule SUP_upper2[where i="(0,h)"])
      using assms[THEN pure_qD] apply auto  
      by (metis eq_iff) 
    done


lemma theorem_3_11_2:
  assumes "pure_q X" "pure_q Y"
  shows "(\<lambda>sh. X sh \<^bold>* Y sh) = (sep_conj_s_q X Y)"
  oops


lemma theorem_3_11_3:
  assumes "pure_q X" 
  shows "((\<lambda>sh. X sh \<^bold>* Y sh) \<star> Z) = (\<lambda>sh. X sh \<^bold>* (Y \<star> Z) sh)"
proof -
  {
    fix s h 
  have "(sep_conj_s_q (\<lambda>sh. X sh \<^bold>* Y sh) Z) (s,h)
      =  (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>(x, y). X (s, x) \<^bold>* Y (s, x) \<^bold>* Z (s, y)))"
    apply auto unfolding sep_conj_s_q_def 
    apply simp unfolding sep_conj_q_alt by auto
  also have "\<dots> = (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>(x, y). X (s, h) \<^bold>* Y (s, x) \<^bold>* Z (s, y)))"
    apply(subst pure_q_norm[OF assms, where h'=h]) by simp
  also have "\<dots> = X (s, h) \<^bold>* (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>(x, y).  Y (s, x) \<^bold>* Z (s, y)))"
    by(auto simp: SUP_mult_left_distrib  assoc intro!: SUP_cong) 
  also have "\<dots> = X (s, h) \<^bold>* (sep_conj_s_q Y Z) (s,h)"
    apply auto unfolding sep_conj_s_q_def 
    apply simp unfolding sep_conj_q_alt 
    by auto 
  finally have "(sep_conj_s_q (\<lambda>sh. X sh \<^bold>* Y sh) Z) (s,h) = (\<lambda>sh. X sh \<^bold>* (sep_conj_s_q Y Z) sh) (s,h)"
    .
} then show ?thesis apply(intro ext) by auto
qed

lemma theorem_3_11_3':
  assumes "pure_q X" 
  shows "(sep_conj_s_q Z (\<lambda>sh. X sh \<^bold>* Y sh)) = (\<lambda>sh. X sh \<^bold>* (sep_conj_s_q Z Y) sh)"
      apply(subst sep_conj_s_q_commute)
      apply(simp add: theorem_3_11_3 assms) 
      apply(subst sep_conj_s_q_commute) by simp


end
end


(*
context normed_sep_algebra
begin                                          

term SIZE
definition SIZE where
    "SIZE = (\<lambda>(s,h). Size h)"

lemma "a ## b \<longleftrightarrow> (dom (theheap a)) \<inter> (dom (theheap b)) =  {}"
  by simp


definition map_of_heap :: "('c\<Rightarrow>'d tsa_opt) \<Rightarrow> 'c \<Rightarrow> 'd option"  where
  "map_of_heap h a = (case h a of ZERO \<Rightarrow> None | TRIV a \<Rightarrow> Some a)"


lemma pp: "(dom (  a)) \<inter> (dom (  b)) =  {} 
        \<longleftrightarrow> (\<forall>x. a x = None \<or> b x = None)" 
  by (metis disjoint_iff_not_equal domIff)  

lemma fixes
  a b :: "'c \<Rightarrow> 'd tsa_opt"
  shows "a ## b \<longleftrightarrow> (dom (map_of_heap  a)) \<inter> (dom (map_of_heap  b)) =  {}"
  unfolding sep_disj_fun_def sep_disj_option.simps pp map_of_heap_def
  apply auto subgoal  
    by (metis option.distinct(1) sep_disj_tsa_opt_def tsa_opt.case_eq_if)  
  subgoal for x apply(cases "a x";cases "b x")
    by (auto split: tsa_opt.splits simp: sep_disj_tsa_opt_def )
  done

lemma 
  fixes P :: "('b*'a) \<Rightarrow> ennreal"
  shows "SIZE \<star> P = P \<star> SIZE"
  oops


end*)

end 