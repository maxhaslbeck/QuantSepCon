theory QuantSepConState
imports QuantSepCon
begin


lemma plus_fun_alt: "(\<lambda>x. (f1 x + f2 x)) = (f1 + f2)"
  by auto
lemma mult_fun_alt: "(\<lambda>x. (f1 x * f2 x)) = (f1 * f2)"
  by auto

abbreviation embb ("\<lbrakk>_\<rbrakk>") where "embb b \<equiv> (\<lambda>(s,h). emb b s)"
abbreviation embn ("\<lbrakk>~_\<rbrakk>") where "embn b \<equiv> (\<lambda>(s,h). emb (\<lambda>s. \<not> b s) s)"


context sep_algebra
begin

subsection \<open>With state\<close>

definition
  sep_impl_s_q  (infixr "-\<star>" 60)
  where
  "sep_impl_s_q P Q \<equiv> \<lambda>(s,h). sep_impl_q (\<lambda>h. P(s,h)) (\<lambda>h. Q(s,h)) h "



definition
  sep_conj_s_q  (infixr "\<star>" 60)
  where
  "P \<star> Q \<equiv> \<lambda>(s,h). sep_conj_q (\<lambda>h. P(s,h)) (\<lambda>h. Q(s,h)) h "


definition "sep_empty_s_q = (\<lambda>(s,h). sep_empty_q h)"

lemma sep_conj_s_q_assoc: 
  "(x \<star> (y \<star> z))  = ((x \<star> y) \<star> z) "
  unfolding sep_conj_s_q_def by (auto simp: star_assoc)

lemma sep_conj_s_q_commute:
    "P \<star> Q = Q \<star> P"
  unfolding sep_conj_s_q_def
  apply(rule ext) apply auto apply(subst star_comm) by simp

term sep_empty_q
thm emp_neutral[no_vars]

lemma sep_conj_s_q_neutral: "(X \<star> sep_empty_s_q) = X"
  "(sep_empty_s_q \<star> X) = X"
  unfolding sep_conj_s_q_def sep_empty_s_q_def
    using emp_neutral by auto

lemma emb_alt: "(\<lambda>h. emb \<phi> (a, h)) = emb (\<lambda>h. \<phi> (a,h))"
  by(auto simp: emb_def)

lemma theorem_3_6_s:
  "(sep_conj_s_q P  (sup Q R)) = (\<lambda>s. sup (sep_conj_s_q P Q s) (sep_conj_s_q P R s))"
  "(P \<star> (\<lambda>s. Q s + R s)) \<le> (\<lambda>s. (P \<star> Q) s + (P \<star> R) s)"
  "( (emb \<phi>) \<star> (Q * R)) \<le> ((emb \<phi>) \<star> Q) * ((emb \<phi>) \<star> R)"
  unfolding sep_conj_s_q_def
  subgoal  apply(rule ext)  
    subgoal for s apply(cases s) apply simp 
      apply(subst sup_fun_def[symmetric])
      apply(subst theorem_3_6(1)) by auto 
    done
  subgoal apply(rule le_funI)  
    subgoal for s apply(cases s) apply simp     
      apply(rule order.trans) 
      apply(subst plus_fun_alt) 
       apply(rule theorem_3_6(2)[THEN le_funD] ) by auto  
    done
  subgoal apply(rule le_funI)  
    subgoal for s apply(cases s) apply simp     
      apply(rule order.trans) 
       apply(subst mult_fun_alt) 
      unfolding emb_alt
       apply(rule theorem_3_6(3)[THEN le_funD] ) by auto  
    done  
  done


lemma sep_impl_s_q_Rmono:
    " X \<le> Y \<Longrightarrow> sep_impl_s_q A X sh \<le> sep_impl_s_q A Y sh" 
  unfolding sep_impl_s_q_def
  apply(cases sh) apply simp 
  apply(rule sep_impl_q_monoR[THEN le_funD]) 
  by (auto simp: le_fun_def emb_def)  

lemma sep_impl_s_q_mono:
    "B \<le> A \<Longrightarrow> X \<le> Y \<Longrightarrow> sep_impl_s_q A X sh \<le> sep_impl_s_q B Y sh" 
  unfolding sep_impl_s_q_def
  apply(cases sh) apply simp oops (*
  apply(rule sep_impl_q_mono[THEN le_funD]) 
  by (auto simp: le_fun_def emb_def) *)

term "a::'b::{times,complete_distrib_lattice,linear_continuum,semiring_1_no_zero_divisors}"


print_classes

lemma sep_conj_s_q_mono:
    "A \<le> B \<Longrightarrow> X \<le> Y \<Longrightarrow> sep_conj_s_q A X sh \<le> sep_conj_s_q B Y sh"
    unfolding sep_conj_s_q_def
  apply(cases sh) apply simp
  apply(rule sep_conj_q_mono[THEN le_funD]) 
  by (auto simp: le_fun_def emb_def) 

lemma sep_conj_s_q_mono':
    "A \<le> B \<Longrightarrow> X \<le> Y \<Longrightarrow>   A\<star> X   \<le>   B\<star> Y  "
  apply(rule le_funI) apply(rule sep_conj_s_q_mono) by auto

subsubsection \<open>Algebraic Laws for * under purity\<close>



definition pure_q :: "('b * 'a \<Rightarrow> ennreal) \<Rightarrow> bool" where
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
  "(\<lambda>sh. X sh * Y sh) \<le> (sep_conj_s_q X Y)"
  unfolding sep_conj_s_q_def sep_conj_q_alt
  apply(rule le_funI) apply auto
  subgoal for s h 
    apply(rule SUP_upper2[where i="(0,h)"])
      using assms[THEN pure_qD] apply auto  
      by (metis eq_iff) 
    done


lemma theorem_3_11_2:
  assumes "pure_q X" "pure_q Y"
  shows "(\<lambda>sh. X sh * Y sh) = (sep_conj_s_q X Y)"
  sorry


lemma theorem_3_11_3:
  assumes "pure_q X" 
  shows "((\<lambda>sh. X sh * Y sh) \<star> Z) = (\<lambda>sh. X sh * (Y \<star> Z) sh)"
proof -
  {
    fix s h 
  have "(sep_conj_s_q (\<lambda>sh. X sh * Y sh) Z) (s,h)
      =  (SUP (x, y):{(x, y). h = x + y \<and> x ## y}. X (s, x) * Y (s, x) * Z (s, y))"
    apply auto unfolding sep_conj_s_q_def 
    apply simp unfolding sep_conj_q_alt by auto
  also have "\<dots> = (SUP (x, y):{(x, y). h = x + y \<and> x ## y}. X (s, h) * Y (s, x) * Z (s, y))"
    apply(subst pure_q_norm[OF assms, where h'=h]) by simp
  also have "\<dots> = X (s, h) * (SUP (x, y):{(x, y). h = x + y \<and> x ## y}.  Y (s, x) * Z (s, y))"
    by(auto simp: SUP_mult_left_ennreal mult.assoc intro!: SUP_cong) 
  also have "\<dots> = X (s, h) * (sep_conj_s_q Y Z) (s,h)"
    apply auto unfolding sep_conj_s_q_def 
    apply simp unfolding sep_conj_q_alt 
    by auto 
  finally have "(sep_conj_s_q (\<lambda>sh. X sh * Y sh) Z) (s,h) = (\<lambda>sh. X sh * (sep_conj_s_q Y Z) sh) (s,h)"
    .
} then show ?thesis apply(intro ext) by auto
qed

lemma theorem_3_11_3':
  assumes "pure_q X" 
  shows "(sep_conj_s_q Z (\<lambda>sh. X sh * Y sh)) = (\<lambda>sh. X sh * (sep_conj_s_q Z Y) sh)"
      apply(subst sep_conj_s_q_commute)
      apply(simp add: theorem_3_11_3 assms) 
      apply(subst sep_conj_s_q_commute) by simp


end


end