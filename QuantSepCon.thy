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

instance "fun" :: (type,zero) zero
  by standard  

instantiation "fun" :: (type,times) times
begin
definition [simp]: "(f1 * f2) x = f1 x * f2 x"
instance by standard
end 


definition emb :: "('b \<Rightarrow> bool) \<Rightarrow> 'b  \<Rightarrow> ennreal" where
  "emb P x = (if P x then 1 else 0)"

lemma emb_range: "emb P x \<in> {0,1}" unfolding emb_def by auto

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






lemma sep_conj_q_SUP: "(P **q Q) = (\<lambda>h. (SUP i:{(x,y)| x y. h=x+y \<and> x ## y}. (\<lambda>(x,y). P x * Q y) i))"
  unfolding sep_conj_q_def apply auto  apply (rule ext)
  apply(rule Sup_cong) by auto 



subsection \<open>Quantitative Separating Implication - Magic Wand\<close>

definition
  sep_impl_qq :: "('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal)" (infixr "-*qq" 35)
  where
  "P -*qq Q \<equiv> \<lambda>h. INF h': { h'. h ## h' \<and> P(h') > 0 \<and> (P h' < \<infinity> \<or> Q (h+h') < \<infinity>)}. Q (h + h') / P(h')"

(*definition
  sep_impl_q :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal)" (infixr "-*q" 35)
  where
  "P -*q Q \<equiv> \<lambda>h. Inf {  Q (h + h') | h'. h ## h' \<and> P h'}"
*)

abbreviation sep_impl_q (infixr "-*q" 35) where   "(P -*q Q) \<equiv> (emb P -*qq Q)" 

 
lemma ennreal_div_one: "x / 1 = (x::ennreal)"
by (metis ennreal_top_neq_one mult.right_neutral mult_divide_eq_ennreal one_neq_zero)

lemma sep_impl_q_alt:
  "(P -*q Q) = (\<lambda>h. INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
  apply (rule ext)
  unfolding sep_impl_qq_def emb_def
  apply (rule INF_cong)
   apply (auto simp:ennreal_div_one)
  done

subsection \<open>Embedding of SL into QSL\<close>


lemma Sup_zeroone: " P \<subseteq> {0,1} \<Longrightarrow> Sup P \<in> {0,1::ennreal}"
(*  sledgehammer *)
  by (smt Set.set_insert Sup_bot_conv(1) Sup_empty Sup_insert Sup_subset_mono Sup_upper bot_ennreal ccpo_Sup_singleton insertCI insert_commute insert_subset linorder_not_less order_le_less subset_insert)


lemma Inf_zeroone: "P \<noteq> {} \<Longrightarrow> P \<subseteq> {0,1} \<Longrightarrow> Inf P \<in> {0,1::ennreal}"
 (*  sledgehammer *)
  by (smt Inf_le_Sup Inf_lower Inf_superset_mono Sup_empty Sup_subset_mono bot_ennreal cInf_singleton insertCI le_zero_eq linorder_not_less order_le_less subset_insert)
 


lemma "(0::ennreal) \<le> 1"  by auto

lemma emb_1: "emb P h = 1 \<longleftrightarrow> P h"
  by(auto simp: emb_def)

subsubsection \<open>Conservativity of QSL as an assertion language\<close>



lemma sep_conj_q_range: "((emb P) **q (emb Q)) h \<in> {0,1}"
  unfolding sep_conj_q_def  
  apply(rule Sup_zeroone) 
    by (auto simp: emb_def)
   


lemma sep_conj_q_leq1: "((emb P) **q (emb Q)) h \<le>1"
  using sep_conj_q_range[of P Q h] by auto 

lemma sep_impl_q_range: "(P -*q (emb Q)) h \<in> {0,1}"  
  unfolding sep_impl_qq_def
  apply(rule Inf_zeroone)
  subgoal apply simp oops (* only holds for {0..1} instead of ennreal *)


lemma "(P  \<longrightarrow>* Q) h \<longleftrightarrow> (P -*q (emb Q)) h = 1"
  sorry



lemma "(P ** Q) h \<longleftrightarrow> ((emb P) **q (emb Q)) h = 1" 
proof -
  have "(P ** Q) h = (\<exists>xa y. xa ## y \<and> h = xa + y \<and> emb P xa = 1 \<and> emb Q y = 1)"
    unfolding sep_conj_def emb_1 by auto
  also have "\<dots> = (Sup { emb P x * emb Q y | x y. h=x+y \<and> x ## y} = 1)"
    apply rule
    subgoal  
      apply(rule antisym)
      subgoal using sep_conj_q_leq1[unfolded sep_conj_q_def] by simp
      subgoal apply(rule Sup_upper) by force 
      done
    subgoal  
      sorry
    done
  also have "\<dots> = (((emb P) **q (emb Q)) h = 1)" unfolding sep_conj_q_def by simp
  finally show ?thesis .
qed

 


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



subsubsection \<open>Or\<close>

lemma "emb (X or Y) = (max (emb X) (emb Y))" 
  sorry


lemma "((emb X) **q (emb Y)) = 0 \<Longrightarrow> emb (X or Y) = (emb X) + (emb Y)" 
  sorry



subsubsection \<open>monotonicity of @{term "( **q)"}\<close>

text \<open>theorem 3.7\<close>

lemma sep_conj_q_mono:
   "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (X **q Y) \<le> (X' **q Y')"  
    by (force intro: le_funI SUP_mono simp add: sep_conj_q_alt mult_mono le_funD)  


lemma sep_conj_q_impl1:
  assumes P: "\<And>h. P h \<le> I h"
  shows "(P **q R) h \<le> (I **q R) h" 
  by (metis (no_types, lifting) assms le_funD le_fun_def star_comm_nice sup.absorb_iff2 theorem_3_6(1))  
   (* crazy sledgehammer proof *)



lemma sep_conj_q_impl :
  assumes P: "\<And>h. P h \<le> P' h"
  assumes Q: "\<And>h. Q h \<le> Q' h"
  shows "(P **q Q) h \<le> (P' **q Q') h"
  using sep_conj_q_mono  
  by (simp add: P Q le_funD le_funI)  


subsubsection \<open>is @{term "(-*qq)"} monotonic\<close>


lemma nn: "(\<not> x < (top::ennreal)) = (x = top)" 
  using top.not_eq_extremum by blast

lemma sep_impl_q_monoR: 
  shows "Y \<le> Y' \<Longrightarrow> (P -*qq Y) \<le> (P -*qq Y')"  
  unfolding sep_impl_qq_def
  apply(rule le_funI)
  apply(rule Inf_mono)
  apply auto
  subgoal for h h' apply(rule exI[where x=h']) 
    apply auto  
    by (simp add: divide_right_mono_ennreal le_funD)
  subgoal for h h' apply(rule exI[where x=h']) 
    apply auto  
     apply (auto simp add: nn divide_right_mono_ennreal le_funD)   
    
    by (metis le_funD not_less) 
  done


lemma "(a::ennreal) div b = a / b" by auto
  
lemma ennreal_inverse_antimono:
  "(a::ennreal) \<le> b \<Longrightarrow> inverse b \<le> inverse a"
  apply(cases a; cases b; cases "a=0"; cases "b=0") 
     apply simp_all
   apply(simp add: inverse_ennreal)   
  using ennreal_neq_top top.extremum_uniqueI by blast   

lemma sep_impl_q_monoL: 
  shows "P' \<le> P \<Longrightarrow> (P -*qq Y) \<le> (P' -*qq Y)"  
(*  unfolding sep_impl_qq_def
  apply(rule le_funI)
  apply(rule Inf_mono)
  apply auto
  subgoal for h h' apply(rule exI[where x=h']) 
    apply (auto) apply(drule le_funD[where x=h']) apply simp
    apply(cases "P h'<\<infinity>")
    subgoal apply auto apply(drule le_funD[where x=h']) 
      apply(drule ennreal_inverse_antimono) 
      unfolding divide_ennreal_def 
      using mult_left_mono by fastforce 
    subgoal by (auto simp: nn)
    done
  done
*) oops

lemma sep_impl_q_mono: 
  shows "P' \<le> P \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (P -*qq Y) \<le> (P' -*qq Y')"  
  apply(rule order.trans)
  apply(rule sep_impl_q_monoL) apply simp
  apply(rule sep_impl_q_monoR) apply simp
  oops

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


thm ereal_mult_divide

lemma ennreal_mult_divide: "b > 0 \<Longrightarrow> b < (\<infinity>::ennreal) \<Longrightarrow> b * (a / b) = a" 
  apply(cases a; cases b) apply (auto simp: divide_ennreal ennreal_mult[symmetric])
   by (simp add: ennreal_divide_eq_top_iff ennreal_mult_eq_top_iff)    

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


lemma adjoint_general:
  shows "(X **q P) \<le> Y \<longleftrightarrow> X \<le> (P -*qq Y)"
proof - 
  have eq79: "\<And>h h'. h ## h' \<Longrightarrow> 0 < P h'  \<Longrightarrow> (P h' < \<infinity> \<or> Y (h+h') < \<infinity>) \<Longrightarrow> ( X h \<le> Y (h + h') / P h') \<longleftrightarrow> X h * P h' \<le> Y(h+h') "
    subgoal for h h'
      apply rule
      subgoal using mult_left_mono[where a="X h" and b="Y (h + h') / P h'" and c="P h'"]
        apply(cases "P h'<\<infinity>")
        subgoal    
          by (simp add: ennreal_mult_divide mult.commute)  
        subgoal  
          by (auto simp: nn ) 
        done
      subgoal
        apply(cases "P h'<\<infinity>")
        subgoal  
          by (smt divide_less_ennreal ennreal_mult_divide infinity_ennreal_def less_le mult_left_mono not_less)
        subgoal 
          apply auto
          apply(simp only: nn)
          apply simp  (* oopsie \<forall>x. x/\<infinity> = 0 *)           
          using  nn 
          by (metis ennreal_mult_eq_top_iff linorder_not_less)      
        done
      done 
    done
  thm eq79[where h'=0]
  have "X \<le> (P -*qq Y) \<longleftrightarrow> (\<forall> h. X h \<le> (P -*qq Y) h)"
    by (simp add: le_fun_def)
  also have "... \<longleftrightarrow> (\<forall>h. X h \<le> (INF h':{h'. h ## h' \<and> 0 < P h'\<and> (P h' < \<infinity> \<or> Y (h+h') < \<infinity>) }. Y (h + h') / P h'))" 
    unfolding sep_impl_qq_def
    by simp  
  also have "... \<longleftrightarrow> (\<forall>h h'. h ## h' \<and> 0 < P h' \<and> (P h' < \<infinity> \<or> Y (h+h') < \<infinity>)  \<longrightarrow> X h \<le> Y (h + h') / P h')" 
    by (simp add: le_INF_iff)
  also have "... \<longleftrightarrow>  (\<forall>h h'. h ## h' \<and> 0 < P h' \<and> (P h' < \<infinity> \<or> Y (h+h') < \<infinity>)  \<longrightarrow> X h * P h' \<le> Y (h + h'))"
    using eq79 by auto
  also have "... \<longleftrightarrow> (\<forall>a b. a ## b \<longrightarrow> X a * P b \<le> Y (a + b))" 
    apply auto
    subgoal for a b
      apply (cases "0 < P b")
      subgoal
        apply( cases "P b < \<infinity>"; cases "Y (a+b) < \<infinity>")
           apply (auto simp: nn) by force
        subgoal
        apply( cases "P b < \<infinity>"; cases "Y (a+b) < \<infinity>")
           by (auto simp: nn)
         done
       done
  also have "... \<longleftrightarrow> ((\<lambda>h. SUP (x, y):{(x, y). h = x + y \<and> x ## y}. X x * P y) \<le> Y)" 
    thm SUP_le_iff
    by (simp add: le_fun_def SUP_le_iff)
  also have "... \<longleftrightarrow> (X **q P) \<le> Y"
    unfolding sep_conj_q_alt
    by simp
  finally show ?thesis by simp
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

lemma quant_modus_ponens_general:
  assumes "(\<And>h. P h < \<infinity>)"
  shows "( P **q (P -*qq X)) \<le> X"
proof -
  have " (P -*qq X) \<le> (P -*qq X)" by simp
  then have "(((P -*qq X) **q  P) \<le> X)"
    using adjoint_general[symmetric, where X="(P -*qq X)" and Y=X] assms by auto
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



lemma tightest_intuitionistic_expectations_wand:
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


lemma tightest_intuitionistic_expectations_wand_general:
    "intuitionistic_q (\<^bold>1 -*qq X)" 
    "(\<^bold>1 -*qq X) \<le> X"
    "\<And>X'. intuitionistic_q X' \<Longrightarrow> X' \<le> X \<Longrightarrow>  X' \<le> (\<^bold>1 -*qq X)"
  sorry



abbreviation (input)
  pred_ex_q :: "('b \<Rightarrow> 'a \<Rightarrow> ennreal) \<Rightarrow> 'a \<Rightarrow> ennreal" (binder "EXSq " 10) where
  "EXSq x. P x \<equiv> \<lambda>h. SUP x. P x h"




end


end