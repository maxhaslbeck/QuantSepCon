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


text \<open>enable multiplication on functions\<close>

instantiation "fun" :: (type,times) times
begin
definition [simp]: "(f1 * f2) x = f1 x * f2 x"
instance by standard
end 


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
  "P -*q Q \<equiv> \<lambda>h. Inf {  Q (h + h') | h'. h ## h' \<and> P h'}"

lemma sep_impl_q_alt:
  "(P -*q Q) = (\<lambda>h. INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
  unfolding sep_impl_q_def apply(rule ext)
  apply (rule arg_cong[where f=Inf]) by auto



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


 




lemma star_comm: "(X **q Y) = (Y **q X)"
  unfolding sep_conj_q_SUP
  apply(rule ext)
  apply(rule Sup_cong)
  apply auto
  subgoal
    apply (auto simp add: mult.commute sep_disj_commute sep_add_commute)
    done
  subgoal for a b
    apply(rule Set.image_eqI[where x="(b,a)"])
    apply auto
      apply (simp add: mult.commute)
    using local.sep_add_commute apply auto[1]
    apply (simp add: sep_disj_commute)
    done
  done

lemma star_comm_nice: "(X **q Y) = (Y **q X)"
  unfolding sep_conj_q_SUP
  apply(rule ext)
  apply(rule Sup_cong)
  apply (auto simp add: mult.commute sep_disj_commute sep_add_commute)
  done


lemma emp_neutral1:
  "(X **q sep_empty_q) = X"
  unfolding sep_conj_q_def sep_empty_q_def emb_def
  apply(rule ext)
  apply(rule antisym)
  subgoal
    by (auto intro: Sup_least)
  subgoal
    by (auto intro: Sup_upper)
  done
 

lemma emp_neutral2 : 
  "(sep_empty_q **q X) = X"
  apply(simp only: star_comm)
  apply(rule emp_neutral1) done

lemmas emp_neutral = emp_neutral1 emp_neutral2


thm emp_neutral


lemma sep_conj_q_left_commute: "(P **q Q **q R) = (Q **q P **q R)"
  apply(subst  star_assoc)
  apply(subst  star_comm)
  apply(subst  star_assoc) by simp


lemmas sep_conj_q_c = star_comm sep_conj_q_left_commute


subsubsection \<open>(Sub)distributivity Laws\<close>
 
term "Q * (R::_\<Rightarrow>ennreal)"

lemma theorem_3_6:
  "(P **q (sup Q R)) = sup (P **q Q) (P **q R)"
  "(P **q (Q + R)) \<le> (P **q Q) + (P **q R)"
  "( (emb \<phi>) **q (Q * R)) \<le> ((emb \<phi>) **q Q) * ((emb \<phi>) **q R)"
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
  proof -

    have brr: "\<And>S. \<And>f g::_\<Rightarrow>ennreal. (SUP x:S. f x + g x) \<le> (SUP x:S. f x) + (SUP x:S. g x)"
      by (simp add: SUP_least SUP_upper add_mono)

    have "\<And>a b c :: ennreal. a * (b + c) = a * b + a * c"
      by (simp add: algebra_simps) 
    have fff: "\<And>a b c d :: ennreal. a=c \<Longrightarrow> b=d \<Longrightarrow> a + b = c + d"
      by (simp add: algebra_simps) 
    { fix h
      have "(P **q (Q + R)) h = Sup {P x * (Q + R) y |x y. h = x + y \<and> x ## y}"

        unfolding sep_conj_q_def by simp
      also have "\<dots> = Sup { (P x * Q y) + (P x * R y) |x y. h = x + y \<and> x ## y}"
        unfolding plus_fun_def by(simp add: algebra_simps) 
      also have "\<dots> = (SUP (x,y):{(x,y)|x y. h = x + y \<and> x ## y}. (P x * Q y) + (P x * R y) )"
        apply(rule arg_cong[where f=Sup]) by auto  
      also have "\<dots> = (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. (P (fst x) * Q (snd x)) + (P (fst x) * R (snd x)) )"
        apply(rule arg_cong[where f=Sup]) by force    
      also have "\<dots> \<le> (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x) * Q (snd x) )
                    + (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x) * R (snd x) )" 
        by (rule brr)
          (*
  also have "\<dots> = Sup { (P x * Q y) |x y. h = x + y \<and> x ## y} + Sup { P x * R y |x y. h = x + y \<and> x ## y}"
    apply(rule fff)
    subgoal apply(rule arg_cong[where f=Sup]) by force 
    subgoal apply(rule arg_cong[where f=Sup]) by force    
    done *)
      also have "\<dots> = ((P **q Q) + (P **q R)) h"
        unfolding sep_conj_q_alt apply simp     
        by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
      finally have "(P **q (Q + R)) h \<le> ((P **q Q) + (P **q R)) h " .
    }

    then show ?thesis by (rule le_funI)
  qed
next
  show "( (emb \<phi>) **q (Q * R)) \<le> ((emb \<phi>) **q Q) * ((emb \<phi>) **q R)"
    sorry
qed




subsubsection \<open>monotonicity of @{term "( **q)"}\<close>

text \<open>theorem 3.7\<close>

lemma sep_conj_q_mono:
   "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (X **q Y) \<le> (X' **q Y')"  
    by (force intro: le_funI SUP_mono simp add: sep_conj_q_alt mult_mono le_funD)  

subsubsection \<open>adjointness of star and magicwand\<close>

text \<open>theorem 3.9\<close>

lemma adjoint: "(X **q (emb P)) \<le> Y \<longleftrightarrow> X \<le> (P -*q Y)"
proof
  assume "(X **q emb P) \<le> Y"
  with star_comm have "(emb P **q X) \<le> Y"
    by auto
  then have "\<And>h'. (SUP (x, y):{(x, y) |x y. h' = x + y \<and> x ## y}. emb P x * X y)  \<le> Y h'"    
    by (auto simp: le_fun_def sep_conj_q_SUP)
  then have eq99: "\<And>h' h1' h2'. h' = h1' + h2' \<and> h1' ## h2' \<Longrightarrow> emb P h1' * X h2' \<le> Y h'"
    by(auto simp add: Sup_le_iff)
  have eq99': "\<And>h' h1' h2'. h' = h1' + h2' \<and> h1' ## h2' \<and> P h1' \<Longrightarrow>  X h2' \<le> Y h'"
    using eq99 unfolding emb_def by force

  show "X \<le> (P -*q Y)"
  proof (rule le_funI)
    fix h
    show "X h \<le> (P -*q Y) h"
    proof (cases "(\<exists>h'.  P h' \<and> h ## h')")
      case no_h': False
      have " (P -*q Y) h = (INF h':{h'. h ## h' \<and> P h'}. Y (h + h'))"
        unfolding sep_impl_q_alt by simp
      also have "\<dots> = Inf {}" 
        using no_h' by force
      also have "\<dots> = \<infinity>"
        by auto
      finally show ?thesis by auto
    next
      case True
      then have "X h = (INF h':{h'. P h' \<and> h ## h'}. X h)"
        by(auto simp add: INF_constant)
      also have "\<dots> \<le> (INF h':{h'. h ## h' \<and> P h'}. Y (h + h'))"
        apply(rule INF_mono)  
        using eq99' sep_disj_commute sep_add_commute by auto 
      also have "\<dots> = (P -*q Y) h"
        unfolding sep_impl_q_alt by simp
      finally show ?thesis .
    qed
  qed 
next
  assume "X \<le> (P -*q Y)"
  show "(X **q emb P) \<le> Y"
    sorry
qed

subsubsection \<open>quantitative modus ponens\<close>

text \<open>theorem 3.8\<close>

lemma quant_modus_ponens:
  "( (emb P) **q (P -*q X)) \<le> X"
proof -
  have " (P -*q X) \<le> (P -*q X)" by simp
  then have "(((P -*q X) **q emb P) \<le> X)"
    using adjoint[symmetric, where X="(P -*q X)" and Y=X] by auto
  then show ?thesis using star_comm by auto
qed


subsection \<open>Intuitionistic Expectations\<close>

text \<open>In SL, a predicate @{term \<phi>} is called @{term intuitionistic}, iff for all @{term h} and 
 @{term h'} with @{term "h \<preceq> h'"} , @{term "\<phi> h"} implies @{term "\<phi> h'"}.\<close>

term "intuitionistic"

term "sep_true"

definition "intuitionistic_q P = (\<forall>h h'. h \<preceq> h' \<longrightarrow> P h \<le> P h')"

lemma "intuitionistic P \<Longrightarrow> intuitionistic_q (emb P)"
  unfolding intuitionistic_q_def intuitionistic_def emb_def by auto


lemma intuitionistic_qI:
  "(\<And>h h'. h \<preceq> h' \<Longrightarrow> P h \<le> P h') \<Longrightarrow> intuitionistic_q P"
  by (unfold intuitionistic_q_def, fast)

lemma intuitionistic_qI2:
  "(\<And>h h'. h ## h' \<Longrightarrow> P h \<le> P (h + h')) \<Longrightarrow> intuitionistic_q P"
  apply (unfold intuitionistic_q_def sep_substate_def)
  by auto

 

lemma intuitionistic_qD:
  "intuitionistic_q X \<Longrightarrow>  h ## z \<Longrightarrow> h' = h + z \<Longrightarrow> X h \<le> X h' "
  by (unfold intuitionistic_q_def sep_substate_def, auto)


lemma intuitionistic_q_is_attained_at_h: 
  fixes
    X :: "_ \<Rightarrow> ennreal"
  assumes "intuitionistic_q X"
  shows "(SUP (h1, h2):{(x, y) |x y. h = x + y \<and> x ## y}. X h1) = X h"
  apply(rule antisym)
  subgoal 
    apply(rule SUP_least) using assms by(auto dest: intuitionistic_qD)
  subgoal 
      apply(rule SUP_upper2[where i="(h,0)"]) by auto
  done
 
text \<open>Tightest intuitionistic expectations\<close>

abbreviation sep_true_q ("\<^bold>1")  where "\<^bold>1 \<equiv> (emb sep_true)"

theorem tightest_intuitionistic_expectations_star:
    "intuitionistic_q (X **q \<^bold>1)"
    "X \<le> (X **q \<^bold>1)"
    "\<And>X'. intuitionistic_q X' \<Longrightarrow> X \<le> X' \<Longrightarrow> (X **q \<^bold>1) \<le> X'"
proof -
  show "intuitionistic_q (X **q \<^bold>1)" 
  proof (rule intuitionistic_qI2)
    fix h h'
    assume a: "h ## h'" 
    have "(X **q \<^bold>1) h = (SUP (h1, h2):{(x, y). h = x + y \<and> x ## y}. X h1 * \<^bold>1 h2)" 
      unfolding sep_conj_q_alt by simp
    also have "\<dots> = (SUP (h1, h2):{(x, y). h = x + y \<and> x ## y}. X h1 * \<^bold>1 (h2+h'))"
      by (auto simp: emb_def)
    also have "\<dots> \<le> (SUP (h1, h2):{(x, y). h + h' = x + y \<and> x ## y}. X h1 * \<^bold>1 h2)"
      apply(rule SUP_mono) apply auto
      subgoal for h1 h2 apply(rule exI[where x=h1]) apply(rule exI[where x="h2 + h'"])  
        using a by (force simp: sep_add_assoc dest: sep_add_disjD intro: sep_disj_addI3) 
      done
  also have "\<dots> = (X **q \<^bold>1) (h + h')" 
      unfolding sep_conj_q_alt by simp
    finally show "(X **q \<^bold>1) h \<le> (X **q \<^bold>1) (h + h')" .
  qed
next
  show "X \<le> (X **q \<^bold>1)"
  proof (rule le_funI)
    fix h
    have "X h \<le> (SUP (x, y):{(x, y) |x y. h = x + y \<and> x ## y}. X x * emb (\<lambda>s. True) y)"
      apply(rule Sup_upper) apply auto 
      apply(rule Set.image_eqI[where x="(h,0)"]) by (auto simp: emb_def)   
    also have "\<dots> = (X **q \<^bold>1) h"
      unfolding sep_conj_q_SUP by simp
    finally show "X h \<le> (X **q \<^bold>1) h" .
  qed
next
  fix X'
  assume "intuitionistic_q X'" and Xmono: "X \<le> X'"
  {
    (* for arbitrary but fixed h *)
    fix h
    have "(X **q \<^bold>1) h \<le> (X' **q \<^bold>1) h"
      using sep_conj_q_mono[OF Xmono] by(auto dest: le_funD)
    also have "\<dots> = (SUP (x, y):{(x, y) |x y. h = x + y \<and> x ## y}. X' x *  \<^bold>1 y)"
      unfolding sep_conj_q_SUP by simp
    also have "\<dots> = (SUP (x, y):{(x, y) |x y. h = x + y \<and> x ## y}. X' x)"
      by (auto simp add: emb_def)
    also have "\<dots> = X' h" 
      apply(rule intuitionistic_q_is_attained_at_h) by fact
    finally have "(X **q \<^bold>1) h \<le> X' h" .
  }
  then show "(X **q \<^bold>1) \<le> X'" by (auto simp: le_fun_def)
qed



lemma
    "intuitionistic_q (sep_true -*q X)" 
    "(sep_true -*q X) \<le> X"
    "\<And>X'. intuitionistic_q X' \<Longrightarrow> X' \<le> X \<Longrightarrow>  X' \<le> (sep_true -*q X)"
proof -
  {  
    fix h h'
    assume a: "h ## h'"
    have "(sep_true -*q X) h \<le> (sep_true -*q X) (h + h')" 
      sorry
  } note * = this (* gives the lemma in the brackets a name *) 

  show 1: "intuitionistic_q (sep_true -*q X)"
    apply(rule intuitionistic_qI2)
    by(rule *)
next
  show "(sep_true -*q X) \<le> X"
    sorry
next
  fix X'
  assume "intuitionistic_q X'" and Xmono: "X' \<le> X"
  show "X' \<le> ((\<lambda>s. True) -*q X)"
    sorry
qed



qed




end