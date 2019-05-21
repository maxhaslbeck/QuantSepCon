(*
  Author: Maximilian P. L. Haslbeck
  Author: 
*)
theory QuantSepCon
  imports
  "Sep_Algebra_Add"
 "Separation_Algebra.Separation_Algebra" "HOL-Library.Extended_Nat"
  "HOL-Library.Extended_Nonnegative_Real" 
begin


definition emb :: "('b \<Rightarrow> bool) \<Rightarrow> 'b  \<Rightarrow> ennreal" where
  "emb P x = (if P x then 1 else 0)"


context sep_algebra
begin


definition
  sep_empty_q :: "'a \<Rightarrow> ennreal"  where
  "sep_empty_q \<equiv> emb (\<lambda>h. h = 0)"

subsection \<open>Quantitative Separating Conjunction\<close>

definition
  sep_conj_q :: "('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal)" (infixr "**q" 35)
  where
  "P **q Q \<equiv> \<lambda>h. Sup { P x * Q y | x y. h=x+y \<and> x ## y}" (* why not Sup ? *)

definition qStar :: "('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> 'a \<Rightarrow> ennreal" where
"qStar P Q = (\<lambda>h. ( SUP (h1,h2):{(h1,h2)| h1 h2. h1 ## h2 \<and> h1 + h2 = h} . P h1 * Q h2))"

lemma "qStar P Q = (P **q Q)"
  unfolding qStar_def sep_conj_q_def
  thm ext
  apply(rule ext)
  thm arg_cong
  apply(rule arg_cong[where f=Sup])
  apply auto
  done

lemma sep_conj_q_alt : "(P **q Q) = (\<lambda>h. (SUP (x,y): {(x,y). h=x+y \<and> x ## y}. P x * Q y))"
  unfolding  sep_conj_q_def
  apply auto apply(rule ext)
  apply(rule arg_cong[where f=Sup]) by auto


thm Sup_mono

term "Sup (f ` S)"
term "SUP s:S. f s"

find_theorems name: Sup_cong
lemma (in -) Sup_cong: "\<And>S S'. S=S' \<Longrightarrow> Sup S = Sup S'"
  by simp
find_theorems name: Sup_cong

thm SUP_cong

lemma "Sup (f ` S) = (SUP s:S. f s)"
  apply(rule arg_cong[where f=Sup]) by simp

lemmas Sup_cong2 = arg_cong[where f=Sup]
thm Sup_cong2
find_theorems "Sup"

lemma "Sup (f ` S) = (SUP s:S. f s)"
  apply(rule Sup_cong) by simp




lemma sep_conj_q_impl1:
  assumes P: "\<And>h. P h \<le> I h"
  shows "(P **q R) h \<le> (I **q R) h"
  unfolding sep_conj_q_alt
  sorry



lemma sep_conj_q_impl :
  assumes P: "\<And>h. P h \<le> P' h"
  assumes Q: "\<And>h. Q h \<le> Q' h"
  shows "(P **q Q) h \<le> (P' **q Q') h"
  sorry



lemma sep_conj_q_SUP: "(P **q Q) = (\<lambda>h. (SUP i:{(x,y)| x y. h=x+y \<and> x ## y}. (\<lambda>(x,y). P x * Q y) i))"
  unfolding sep_conj_q_def apply auto  apply (rule ext)
  apply(rule Sup_cong) by auto 



subsection \<open>Quantitative Separating Implication - Magic Wand\<close>

definition
  sep_impl_q :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal)" (infixr "-*q" 35)
  where
  "P -*q Q \<equiv> undefined"



subsection \<open>Properties of Quantitative Separating Connectives\<close> 

subsubsection \<open>Commutative monoid\<close>

lemma star_assoc: "(x **q (y **q z))  = ((x **q y) **q z) "
proof (rule ext)
  fix h
  have "(x **q (y **q z)) h    = (SUP (xa, ya):{(x, y) |x y. h = x + y \<and> x ## y}. x xa * (SUP (x, ya):{(x, y) |x y. ya = x + y \<and> x ## y}. y x * z ya))" 
    unfolding sep_conj_q_SUP by auto 
  also have "\<dots> = (SUP xa:{(x, y). h = x + y \<and> x ## y}. case xa of (xa, ya) \<Rightarrow> SUP i:{(x, y). ya = x + y \<and> x ## y}. (case i of (h21, h22) \<Rightarrow> x xa * y h21 * z h22))"
    by(simp add: SUP_mult_left_ennreal prod.case_distrib mult.assoc)
 
  also have "\<dots> = (SUP xa:{(x, y). h = x + y \<and> x ## y}. SUP i:{((fst xa),x, y)| x y . snd xa = x + y \<and> x ## y}. (case i of (b, h21, h22) \<Rightarrow> x b * y h21 * z h22))"
    apply(rule SUP_cong) apply simp
    apply safe
    apply(rule arg_cong[where f=Sup]) apply safe
    subgoal by force 
    subgoal  apply auto done
    done
  also have "\<dots> = (SUP xa:{(h1, h2, h3). h = h1 + h2 + h3 \<and> h1 ## h2 + h3 \<and> h1 ## h2 \<and> h1 ## h3 \<and> h3 ## h2 }. case xa of (h1, h2, h3) \<Rightarrow> x h1 * y h2 * z h3)"
    apply(subst SUP_UNION[symmetric]) 
    apply(rule SUP_cong)
    subgoal apply (auto simp: sep_add_assoc sep_conj_assoc sep_disj_commute dest: sep_disj_addD )
      subgoal  
        by (metis  sep_add_assoc  sep_disj_addD1  sep_disj_addD2) 
      done
    apply auto done
  also have "\<dots> = (SUP xa:{(x, y). h = x + y \<and> x ## y}. SUP i:{(h1,h2, snd xa)| h1 h2 . fst xa = h1 + h2 \<and> h1 ## h2}. (case i of (h1, h2, h3) \<Rightarrow> x h1 * y h2 * z h3))"
    apply(subst SUP_UNION[symmetric]) 
    apply(rule SUP_cong)
    subgoal apply (auto simp: sep_add_assoc sep_conj_assoc sep_disj_commute dest: sep_disj_addD )
      subgoal   
        using  sep_disj_addI1  sep_disj_commuteI by blast   
      subgoal   
        using sep_disj_addI3 sep_disj_commuteI by blast   
      done
    apply auto done
  also have "\<dots> = (SUP xa:{(h12, h3). h = h12 + h3 \<and> h12 ## h3}. case xa of (h12, h3) \<Rightarrow> SUP h12:{(x, y). h12 = x + y \<and> x ## y}. (case h12 of (h1, h2) \<Rightarrow> (x h1 * y h2 * z h3)))"
    apply(rule SUP_cong) apply simp
    apply safe
    apply(rule arg_cong[where f=Sup]) apply safe
    subgoal by force 
    subgoal by force 
    done 
  also have "\<dots> = ((x **q y) **q z) h"
    unfolding sep_conj_q_SUP apply  (auto simp:  SUP_mult_right_ennreal) 
    apply(rule SUP_cong) apply simp
    apply auto apply(rule SUP_cong) by (auto simp: mult.assoc) 
  finally show "(x **q (y **q z)) h  = ((x **q y) **q z) h " .
qed


lemma emp_neutral[sep_algebra_simps]:
  "(X **q sep_empty_q) = X"
  "(sep_empty_q **q X) = X"
  unfolding sep_conj_q_def
   apply(rule ext)
  unfolding  sep_empty_q_def
  unfolding emb_def
   apply(rule antisym)
  subgoal
  thm Sup_least
    apply(rule Sup_least)
    apply(simp)
  apply auto
  done
  subgoal
  thm Sup_upper
   apply(rule Sup_upper)
   apply(simp)
   apply auto
  done

  

  
(*  thm Complete_Lattices.complete_lattice_class.Sup_le_iff
  apply(simp only:Complete_Lattices.complete_lattice_class.Sup_le_iff)
  *)  
  done


lemma star_comm: "(X **q Y) = (Y **q X)"
  sorry


lemma sep_conj_q_left_commute: "(P **q Q **q R) = (Q **q P **q R)"
  apply(subst  star_assoc)
  apply(subst  star_comm)
  apply(subst  star_assoc) by simp


lemmas sep_conj_q_c = star_comm sep_conj_q_left_commute


subsubsection \<open>(Sub)distributivity Laws\<close>

lemma theorem_3_6:
  "(P **q (sup Q R)) = sup (P **q Q) (P **q R)"
  "(P **q (Q + R)) \<le> (P **q Q) + (P **q R)"
proof -
  have "\<And>f q x. sup f q x = sup (f x) (q x)" by simp
  have A: "\<And>a b :: ennreal. sup a b = Sup ({a} \<union> {b})"  
    apply(subst Sup_union_distrib) by simp

  have supmax: "\<And>x y::ennreal. sup x y = max x y" 
    by (simp add: antisym)

  have "\<And> a b c. (a::ennreal) * max b c = max (a*b) (a*c)" 
    unfolding max_def apply auto  
     apply (auto simp add: mult_left_mono) 
    by (smt ennreal_mult_less_top ennreal_mult_strict_right_mono ennreal_mult_top ennreal_zero_less_mult_iff le_less mult.commute not_less top.extremum)
 
  have sup_times_distrib: "\<And> a b c. (a::ennreal) * sup b c = sup (a*b) (a*c)" 
    unfolding supmax by fact

      
  { fix h
  have "(P **q (sup Q R)) h = Sup {P x * sup Q R y |x y. h = x + y \<and> x ## y}"
  
    unfolding sep_conj_q_def by simp
  also have "\<dots> = Sup {P x * sup (Q y) (R y) |x y. h = x + y \<and> x ## y}"
    by simp
  also have "\<dots> = Sup { sup (P x * Q y) (P x * R y) |x y. h = x + y \<and> x ## y}"
    apply(subst  sup_times_distrib)  by simp
  also have "\<dots> = (SUP x:{(x, y). h = x + y \<and> x ## y}. case x of (x,y) \<Rightarrow> sup (P x * Q y) (P x * R y))" 
    apply (rule arg_cong[where f=Sup]) by auto
  also have "\<dots> = (SUP x:{(x, y). h = x + y \<and> x ## y}. sup (P (fst x) * Q (snd x)) (P (fst x) * R (snd x)))"
    apply (rule arg_cong[where f=Sup])  
    by (meson prod.case_eq_if)    
  also have "\<dots> = sup (SUP x:{(x, y). h = x + y \<and> x ## y}. P (fst x) * Q (snd x))
     (SUP x:{(x, y). h = x + y \<and> x ## y}. P (fst x) * R (snd x))"
    apply(subst SUP_sup_distrib[symmetric])
    subgoal apply auto apply(rule exI[where x=h])  apply(rule exI[where x=0]) by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done 
  also have "\<dots> = sup (P **q Q) (P **q R) h"
    unfolding sep_conj_q_alt apply simp
     
    by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
  finally have "(P **q sup Q R) h = sup (P **q Q) (P **q R) h ".
}
  then show "(P **q (sup Q R)) = sup (P **q Q) (P **q R)" by auto

next
  show "(P **q Q + R) \<le> (P **q Q) + (P **q R)" 
    sorry
qed

end