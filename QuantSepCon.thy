(*
  Author: Maximilian P. L. Haslbeck
  Author: Christoph Matheja
  Author: Kevin Batz
*)
theory QuantSepCon
  imports
  "Sep_Algebra_Add"
 "Separation_Algebra.Separation_Algebra" "HOL-Library.Extended_Nat"
  "HOL-Library.Extended_Nonnegative_Real" 
begin

section \<open>Misc\<close>

subsection \<open>Stuff about ennreal\<close>


lemma ennreal_div_one: "x / 1 = (x::ennreal)"
by (metis ennreal_top_neq_one mult.right_neutral mult_divide_eq_ennreal one_neq_zero)


subsection \<open>Stuff about SUP and various operations\<close>


lemma Sup_cong: "\<And>S S'. S=S' \<Longrightarrow> Sup S = Sup S'"
  by simp

lemma SUP_plus_subdistrib: "\<And>S. \<And>f g::_\<Rightarrow>'b::{complete_lattice,ordered_ab_semigroup_add }. (SUP x:S. f x + g x) \<le> (SUP x:S. f x) + (SUP x:S. g x)"
  by (simp add: SUP_least SUP_upper add_mono)


lemma SUP_plus_subdistrib_ennreal: "\<And>S. \<And>f g::_\<Rightarrow>ennreal. (SUP x:S. f x + g x) \<le> (SUP x:S. f x) + (SUP x:S. g x)"
      by (simp add: SUP_least SUP_upper add_mono)

lemma SUP_plus_subdistrib2:
  "(SUP (h1,h2):A.  f h1 h2 + g h1 h2 :: ennreal) \<le> (SUP (h1,h2):A.  f h1 h2) + (SUP (h1,h2):A.  g h1 h2)"
  apply(rule Sup_least) apply auto 
  apply(rule add_mono) by(auto intro: SUP_upper2)  

term sup_continuous
thm mult_mono

class nogoodname = bot + top + times +
  assumes bot_squared: "bot * bot = bot"     
    and  top_squared: "top * top = top"


class nonnegative = zero + order +
  assumes zero_smallest: "\<And>x::'a. 0 \<le> x"

instance ennreal :: nonnegative
  apply(standard) by auto


lemma SUP_times_distrib: "(SUP x:A. f x * g x::ennreal) \<le> (SUP x:A. f x) * (SUP x:A. g x)"
      by (simp add: SUP_least SUP_upper mult_mono)

lemma SUP_times_distrib2: "(SUP (x,y):A. f x y * g x y::ennreal) \<le> (SUP (x, y):A. f x y) * (SUP (x, y):A. g x y)" 
  apply(rule Sup_least) apply auto 
  apply(rule mult_mono) by(auto intro: SUP_upper2)  


lemma SUP_times_distrib2_general:
  fixes g :: "_\<Rightarrow>_\<Rightarrow>'b::{complete_lattice,ordered_semiring, nonnegative}"
  shows "(SUP (x,y):A. f x y * g x y) \<le> (SUP (x, y):A. f x y) * (SUP (x, y):A. g x y)" 
  apply(rule SUP_least)
  apply auto apply(rule mult_mono)
      by (auto intro: SUP_upper2 simp: zero_smallest)


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

lemma emb_squared: "emb P x = emb P x * emb P x"
  apply (cases "emb P x = 0") using emb_range apply auto by fastforce


definition embc :: "('b \<Rightarrow> bool) \<Rightarrow> 'b  \<Rightarrow> 'c::{complete_lattice}" where
  "embc P x = (if P x then top else bot)"

lemma embc_range: "embc P x \<in> {bot, top}" unfolding embc_def by auto

lemma embc_squared: 
  shows "embc P x = (embc P x :: 'c::{complete_lattice,times,nogoodname}) * embc P x"
  apply (cases "embc P x = bot") using embc_range apply auto
  unfolding embc_def by (auto simp: top_squared bot_squared) 
 
section \<open>Quantitative Separating Connectives\<close>


class divide_right_mono = inverse + order + 
  assumes divide_right_mono_general: "\<And>a b c::'a. a \<le> b \<Longrightarrow> a / c \<le> b / c" 

class SUP_mult_left = complete_lattice + times +
  assumes SUP_mult_left: "c * (SUP i:I. f i) = (SUP i:I. c * f i :: 'a)"
begin

lemma   SUP_mult_right: "(SUP i:I. f i) * c = (SUP i:I. f i * c :: 'a)"
  sorry

end

instance ennreal :: SUP_mult_left
  apply standard apply(rule SUP_mult_left_ennreal) .

thm SUP_mult_left_ennreal


datatype ennreal_inv = E (thee: ennreal)


lemma INF_mult_left_ennreal: "(INF xa:I. x * f xa :: ennreal ) = x * (INF x:I. f x)"
   
  sorry
 
(*
lemma INF_ennreal_add_const':
  fixes f g :: "_ \<Rightarrow> ennreal" 
  shows "(INF i:I. f i + c) = (INF i:I. f i) + c"
proof (cases "I \<noteq> {}")
  case True
  then show ?thesis
    apply(subst ennreal_approx_INF[symmetric, of _ "(INF i:I. f i) + c"])
    apply(rule add_mono) apply(rule INF_lower) apply simp_all 
  proof -
    fix e
    from True obtain i where "f i \<le> (INF x:I. f x)" and iI: "i\<in>I" 
       
      sorry
    then have "\<And>c. f i \<le> (INF x:I. f x) + ennreal c"  
      by (metis add.right_neutral add_mono zero_le)  
    with iI show "\<exists>i\<in>I. c = top \<or> f i \<le> (INF x:I. f x) + ennreal e"
      apply(intro bexI[where x=i]) by auto  
  qed
next
  case False
  then show ?thesis by auto
qed 
  *)

thm INF_ennreal_add_const


lemma INF_ereal_add_left:
  assumes "I \<noteq> {}" "c \<noteq> -\<infinity>" "\<And>x. x \<in> I \<Longrightarrow> 0 \<le> f x"
  shows "(INF i:I. f i + c :: ereal) = (INF i:I. f i) + c"
proof -
  have "(INF i:I. f i) \<noteq> -\<infinity>"
    unfolding INF_eq_minf using assms by (intro exI[of _ 0]) auto
  then show ?thesis
    apply (subst continuous_at_Inf_mono[where f="\<lambda>x. x + c"])
        apply     (auto simp: mono_def ereal_add_mono \<open>I \<noteq> {}\<close> \<open>c \<noteq> -\<infinity>\<close> )
    apply(subst continuous_at_imp_continuous_at_within )
    apply(subst continuous_at)  apply (auto simp:     \<open>I \<noteq> {}\<close> \<open>c \<noteq> -\<infinity>\<close> ) sorry
qed
lemma INF_ennreal_add_const'':
  fixes f g :: "_ \<Rightarrow> ennreal" 
  shows "(INF i:I. f i + c) = (INF i:I. f i) + c"
proof (cases "I \<noteq> {}")
  case True 
  then  show ?thesis 
  apply(subst   continuous_at_Inf_mono[of "\<lambda>x. x + c" ])
        apply (auto simp: mono_def   \<open>I \<noteq> {}\<close>    ) 
    apply(subst continuous_at_imp_continuous_at_within) 
     apply(subst continuous_at)
     apply auto
    unfolding filterlim_def   sorry 
qed auto

lemma INF_ennreal_add_const':
  fixes f g :: "_ \<Rightarrow> ennreal" 
  shows "(INF i:I. f i + c) = (INF i:I. f i) + c"
  using INF_ereal_add_right
proof (cases "I \<noteq> {}")
  case True
  then show ?thesis
    apply(subst ennreal_approx_INF[symmetric, of _ "(INF i:I. f i) + c"])
    apply(rule add_mono) apply(rule INF_lower) apply simp_all 
  proof -
    fix e
    from True obtain i where "f i \<le> (INF x:I. f x)" and iI: "i\<in>I" 
       
      sorry
    then have "\<And>c. f i \<le> (INF x:I. f x) + ennreal c"  
      by (metis add.right_neutral add_mono zero_le)  
    with iI show "\<exists>i\<in>I. c = top \<or> f i \<le> (INF x:I. f x) + ennreal e"
      apply(intro bexI[where x=i]) by auto  
  qed
next
  case False
  then show ?thesis by auto
qed 



lemma INF_ennreal_const_add':
  fixes f g :: "_ \<Rightarrow> ennreal" 
  shows "(INF i:I. c + f i) = c + (INF i:I. f i)" 
    using   INF_ennreal_add_const'[of f c I ] by (simp add: ac_simps) 

instantiation ennreal_inv :: SUP_mult_left
begin

fun times_ennreal_inv where "times_ennreal_inv (E x1) (E x2) = E (x1 + x2)"
fun Inf_ennreal_inv where "Inf_ennreal_inv A = E (Sup (thee ` A))"
fun Sup_ennreal_inv where "Sup_ennreal_inv A = E (Inf (thee ` A))"
definition bot_ennreal_inv where [simp]: "bot_ennreal_inv = E top"
fun  sup_ennreal_inv where "sup_ennreal_inv (E a) (E b) = E (inf a b)"
definition top_ennreal_inv where  [simp]: "top_ennreal_inv = E bot"
fun  inf_ennreal_inv where "inf_ennreal_inv (E a) (E b) = E (sup a b)"
fun  less_eq_ennreal_inv where "less_eq_ennreal_inv (E a) (E b) = (a \<ge> b)"
fun  less_ennreal_inv where "less_ennreal_inv (E a) (E b) = (a > b)"
                               
lemma thee_times: "thee (a * b) = thee a + thee b"
  apply(cases a; cases b) by auto

instance apply(standard)
  subgoal for x y apply(cases x; cases y) by auto
  subgoal for x  apply(cases x ) by auto
  subgoal for x y z apply(cases x; cases y; cases z) by auto
  subgoal for x y apply(cases x; cases y) by auto
  subgoal for x y apply(cases x; cases y) by auto
  subgoal for x y apply(cases x; cases y) by auto
  subgoal for x y z apply(cases x; cases y; cases z) by auto
  subgoal for x y apply(cases x; cases y) by auto
  subgoal for x y apply(cases x; cases y) by auto
  subgoal for x y z apply(cases x; cases y; cases z) by auto
  subgoal for x A apply(cases x) apply simp   
    by (simp add: Sup_upper rev_image_eqI)   
  subgoal for A z apply(cases z) apply simp 
    by (metis SUP_least ennreal_inv.exhaust_sel less_eq_ennreal_inv.simps)
  subgoal for x A apply(cases x) apply simp
    by (metis INF_lower ennreal_inv.sel) 
  subgoal for A z apply(cases z) apply simp 
    by (metis INF_greatest ennreal_inv.collapse less_eq_ennreal_inv.simps) 
  subgoal   by auto
  subgoal   by auto
  subgoal for c f I apply(cases c) by (simp add: thee_times INF_ennreal_const_add')   
  done
end
 

instance ennreal_inv :: ab_semigroup_mult
  apply(standard) 
  subgoal for a b c apply(cases a; cases b; cases c) by (auto simp: mult.assoc)
  subgoal for a b   apply(cases a; cases b ) by (auto simp: mult.commute)
  done 



context sep_algebra
begin


definition
  sep_empty_q :: "'a \<Rightarrow> ennreal"  where
  "sep_empty_q \<equiv> emb (\<lambda>h. h = 0)"

subsection \<open>Quantitative Separating Conjunction\<close>

definition
  sep_conj_q :: "('a \<Rightarrow> 'b::{complete_lattice,times,SUP_mult_left}) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" (infixr "**q" 35)
  where
  "P **q Q \<equiv> \<lambda>h. Sup { P x * Q y | x y. h=x+y \<and> x ## y}" (* why not Sup ? *)

lemma sep_conj_q_alt : "(P **q Q) = (\<lambda>h. (SUP (x,y): {(x,y). h=x+y \<and> x ## y}. P x * Q y))"
  unfolding  sep_conj_q_def
  apply auto apply(rule ext)
  apply(rule arg_cong[where f=Sup]) by auto

lemma sep_conj_q_SUP: "(P **q Q) = (\<lambda>h. (SUP i:{(x,y)| x y. h=x+y \<and> x ## y}. (\<lambda>(x,y). P x * Q y) i))"
  unfolding sep_conj_q_def apply auto  apply (rule ext)
  apply(rule Sup_cong) by auto 



subsection \<open>Quantitative Separating Implication - Magic Wand\<close>

definition
  sep_impl_qq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{ord, SUP_mult_left, inverse})" (infixr "-*qq" 35)
  where
  "P -*qq Q \<equiv> \<lambda>h. INF h': { h'. h ## h' \<and> (bot < P h' \<or> bot < Q (h+h') ) \<and> (P h' < top \<or> Q (h+h') < top)}. Q (h + h') / P(h')"

subsection \<open>Embedding of SL into QSL\<close>


print_classes

abbreviation sep_impl_q (infixr "-*q" 35) where   "(P -*q Q) \<equiv> (embc P -*qq Q)" 

lemma "x/ (\<infinity>::ennreal) = g" apply simp oops

 

lemma 
  assumes "P = (\<lambda>_. True)"
  shows
  "(P -*q Q) = (\<lambda>h. INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
  apply (rule ext)
  unfolding sep_impl_qq_def embc_def
  using assms apply simp

lemma sep_impl_q_alt:
  "(P -*q Q) = (\<lambda>h. INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
  apply (rule ext)
  unfolding sep_impl_qq_def embc_def
  apply(rule antisym)
  subgoal for h
  apply(rule Inf_greatest) apply auto
  apply(rule Inf_lower2)  subgoal for m apply(rule exI[where x=m]) apply auto
  apply (rule INF_cong)
  subgoal
    apply (auto simp:ennreal_div_one  bot_ennreal) sorry
  subgoal
   apply (auto simp:ennreal_div_one  bot_ennreal) 
  done  



lemma Sup_zeroone: " P \<subseteq> {0,1} \<Longrightarrow> Sup P \<in> {0,1::ennreal}"
(*  sledgehammer *)
  by (smt Set.set_insert Sup_bot_conv(1) Sup_empty Sup_insert Sup_subset_mono Sup_upper bot_ennreal ccpo_Sup_singleton insertCI insert_commute insert_subset linorder_not_less order_le_less subset_insert)


lemma Inf_zeroone: "P \<noteq> {} \<Longrightarrow> P \<subseteq> {0,1} \<Longrightarrow> Inf P \<in> {0,1::ennreal}"
 (*  sledgehammer *)
  by (smt Inf_le_Sup Inf_lower Inf_superset_mono Sup_empty Sup_subset_mono bot_ennreal cInf_singleton insertCI le_zero_eq linorder_not_less order_le_less subset_insert)
 

lemma emb_1: "emb P h = 1 \<longleftrightarrow> P h"
  by(auto simp: emb_def)

subsubsection \<open>Conservativity of QSL as an assertion language\<close>



lemma sep_conj_q_range: "((emb P) **q (emb Q)) h \<in> {0,1}"
  unfolding sep_conj_q_def  
  apply(rule Sup_zeroone) 
    by (auto simp: emb_def)
   


lemma sep_conj_q_leq1: "((emb P) **q (emb Q)) h \<le>1"
  using sep_conj_q_range[of P Q h] by auto 

lemma sep_impl_q_rangezeroonetop: "((P -*q (emb Q)) h) \<in> {0,1,top}"  
  unfolding sep_impl_qq_def 
  apply(cases "{h'. h ## h' \<and> 0 < emb P h' \<and> (emb P h' < \<infinity> \<or> emb Q (h + h') < \<infinity>)} = {}")
  subgoal
    by auto
  subgoal apply(rule subsetD[where A="{0,1}"])
    apply simp
    apply(rule Inf_zeroone)
    subgoal by (auto simp: emb_def bot_ennreal)  
    by(auto simp: emb_def split: if_splits)
  done

lemma inf_1_cuts: "a \<in> {0, 1, top} \<Longrightarrow> inf 1 a \<in> {0, 1::ennreal}"
proof -
  assume "a \<in> {0, 1, top}"
  then have "a \<in> {bot, 1, top}"
    using bot_ennreal by presburger
  then have "inf 1 a \<in> {1, bot}"
    using inf_bot_right inf_idem inf_top_right by blast
  then show ?thesis
    using bot_ennreal by auto
qed

lemma sep_impl_q_range: "inf 1 ((P -*q (emb Q)) h) \<in> {0,1}"  
  apply(rule inf_1_cuts) by(rule sep_impl_q_rangezeroonetop)   

lemma quant_wand_conservative: "(P  \<longrightarrow>* Q) h  \<longleftrightarrow> inf 1 (((emb P) -*qq (emb Q)) h)  = 1"
proof - 
  (* rather ugly proof, DB's fault ;) *)
  fix h
  have " inf 1 ((P -*q (emb Q)) h) = 1 \<longleftrightarrow> inf 1 ((INF h':{h'. h ## h' \<and> P h'}. emb Q (h + h'))) = 1"
    unfolding sep_impl_q_alt by simp 
  also have "\<dots> \<longleftrightarrow> (\<forall>h'. h ## h' \<and> P h' \<longrightarrow> Q (h + h'))"
    apply(rule antisym)
    subgoal apply auto
      apply(cases "{h'. h ## h' \<and> P h'} = {}")
      subgoal by simp
      subgoal for h' apply auto proof (rule ccontr, goal_cases)
        case (1 x)
        from 1(2-6) have "inf 1 (INF h':{h'. h ## h' \<and> P h'}. emb Q (h + h')) \<le> 0" 
          apply(intro le_infI2)
          apply(intro INF_lower2[where i=h']) apply simp by (simp add: emb_def)
        then show ?case using 1(1) by auto
      qed 
      done
    subgoal   by (auto simp: emb_def INF_constant) 
    done
  also have "\<dots> \<longleftrightarrow> (P  \<longrightarrow>* Q) h" unfolding sep_impl_def by auto
  finally show "(P  \<longrightarrow>* Q) h \<longleftrightarrow> inf 1 ((P -*q (emb Q)) h) = 1" by simp
qed 

lemma quant_star_conservative: "(P ** Q) h \<longleftrightarrow> ((emb P) **q (emb Q)) h = 1" 
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
    proof (rule ccontr, goal_cases)
      case 1
      from 1(2) have "\<And>x y. (x,y) \<in> {(x,y) | x y. h = x + y \<and> x ## y} \<Longrightarrow> emb P x * emb Q y = 0 "
        apply auto  unfolding emb_def by(auto split: if_splits)  
      then have "Sup {emb P x * emb Q y |x y. h = x + y \<and> x ## y} \<le> 0"
        apply(intro Sup_least) by auto
      with 1(1) show "False" by simp 
    qed 
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
    apply(simp add: SUP_mult_left prod.case_distrib mult.assoc) 
    using SUP_mult_left   sorry
  also have "\<dots> = (SUP xa:{(x, y). h = x + y \<and> x ## y}. SUP i:{((fst xa),x, y)| x y . snd xa = x + y \<and> x ## y}. (case i of (b, h21, h22) \<Rightarrow> x b * y h21 * z h22))"
    apply(rule SUP_cong) apply simp
    apply safe apply(rule Sup_cong) by force 
  also have "\<dots> = (SUP xa:{(h1, h2, h3). h = h1 + h2 + h3 \<and> h1 ## h2 + h3 \<and> h1 ## h2 \<and> h1 ## h3 \<and> h3 ## h2 }. case xa of (h1, h2, h3) \<Rightarrow> x h1 * y h2 * z h3)"
    apply(subst SUP_UNION[symmetric]) 
    apply(rule SUP_cong)
    subgoal
      apply (auto simp: sep_add_ac dest: sep_disj_addD  ) 
      by (metis sep_add_assoc sep_disj_addD1 sep_disj_addD2)  
    by auto
  also have "\<dots> = (SUP xa:{(x, y). h = x + y \<and> x ## y}. SUP i:{(h1,h2, snd xa)| h1 h2 . fst xa = h1 + h2 \<and> h1 ## h2}. (case i of (h1, h2, h3) \<Rightarrow> x h1 * y h2 * z h3))"
    apply(subst SUP_UNION[symmetric]) 
    apply(rule SUP_cong)
    subgoal
      apply (auto simp: sep_add_ac dest: sep_disj_addD )
      subgoal   
        using  sep_disj_addI1  sep_disj_commuteI by blast   
      subgoal   
        using sep_disj_addI3 sep_disj_commuteI by blast   
      done
    by auto 
  also have "\<dots> = (SUP xa:{(h12, h3). h = h12 + h3 \<and> h12 ## h3}. case xa of (h12, h3) \<Rightarrow> SUP h12:{(x, y). h12 = x + y \<and> x ## y}. (case h12 of (h1, h2) \<Rightarrow> (x h1 * y h2 * z h3)))"
    apply(rule SUP_cong) apply simp
    apply safe
    apply(rule Sup_cong) by force
  also have "\<dots> = ((x **q y) **q z) h"
    unfolding sep_conj_q_SUP apply  (auto simp:  SUP_mult_right) 
    apply(rule SUP_cong) apply simp
    apply safe apply(rule SUP_cong) by (auto simp: mult.assoc) 
  finally show "(x **q (y **q z)) h  = ((x **q y) **q z) h " .
qed


 




lemma star_comm:
  fixes X Y :: "_ \<Rightarrow> 'c::{SUP_mult_left, ab_semigroup_mult}"
  shows  "(X **q Y) = (Y **q X)"
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

lemma star_comm_nice:
  fixes X Y :: "_ \<Rightarrow> 'c::{SUP_mult_left, ab_semigroup_mult}"
  shows  "(X **q Y) = (Y **q X)"
  unfolding sep_conj_q_SUP
  apply(rule ext)
  apply(rule Sup_cong)
  apply (auto simp add: mult.commute sep_add_ac)
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

lemma sep_conj_q_left_commute:
  fixes P Q R :: "_ \<Rightarrow> 'c::{SUP_mult_left, ab_semigroup_mult}"
  shows  "(P **q Q **q R) = (Q **q P **q R)"
  apply(subst  star_assoc)
  apply(subst  star_comm)
  apply(subst  star_assoc) by simp


lemmas sep_conj_q_c = star_comm sep_conj_q_left_commute


subsubsection \<open>(Sub)distributivity Laws\<close>


lemma theorem_3_6_general1: 
  fixes
      P :: "_ \<Rightarrow> 'c::{SUP_mult_left,ordered_semiring,nonnegative, linorder}"  
  shows
  "(P **q (sup Q R)) = sup (P **q Q) (P **q R)"
proof -
  have "\<And>f q x. sup f q x = sup (f x) (q x)" by simp
  have A: "\<And>a b :: ennreal. sup a b = Sup ({a} \<union> {b})"  
    apply(subst Sup_union_distrib) by simp

  have supmax: "\<And>x y::'c::{SUP_mult_left,ordered_semiring,nonnegative, linorder}. sup x y = max x y" 
    apply (rule antisym) by (auto simp add: max_def)

  have *: "\<And> a b c. (a::'c::{SUP_mult_left,ordered_semiring,nonnegative, linorder}) * max b c = max (a*b) (a*c)"  
    apply (auto simp add: max_def mult_left_mono) 
    apply(rule antisym) 
    by (simp_all add: antisym mult_left_mono zero_smallest) 

  have sup_times_distrib: "\<And> a b c. (a::'c::{SUP_mult_left,ordered_semiring,nonnegative, linorder}) * sup b c = sup (a*b) (a*c)" 
    unfolding supmax by (fact *)


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
      by auto
    also have "\<dots> = sup (P **q Q) (P **q R) h"
      unfolding sep_conj_q_alt apply simp
      by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
    finally have "(P **q sup Q R) h = sup (P **q Q) (P **q R) h ".
  }
  then show "(P **q (sup Q R)) = sup (P **q Q) (P **q R)" by auto
qed
 
lemma theorem_3_6_general2: 
  fixes
      P :: "_ \<Rightarrow> 'c::{SUP_mult_left,ordered_semiring,nonnegative, linorder }"  
  shows
  "(P **q (Q + R)) \<le> (P **q Q) + (P **q R)"
proof (rule le_funI)
  fix h
  have "(P **q (Q + R)) h = (SUP (x,y):{(x,y)|x y. h = x + y \<and> x ## y}. (P x * Q y) + (P x * R y) )"
    unfolding sep_conj_q_alt  by(simp add: algebra_simps) 
  also have "\<dots> = (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. (P (fst x) * Q (snd x)) + (P (fst x) * R (snd x)) )"
    apply(rule Sup_cong) by force    
  also have "\<dots> \<le> (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x) * Q (snd x) )
                  + (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x) * R (snd x) )" 
    by (rule SUP_plus_subdistrib)
  also have "\<dots> = ((P **q Q) + (P **q R)) h"
    unfolding sep_conj_q_alt apply simp     
    by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
  finally show "(P **q (Q + R)) h \<le> ((P **q Q) + (P **q R)) h " .
qed

lemma theorem_3_6_general3: 
  fixes 
      Q :: "_ \<Rightarrow> 'c::{ab_semigroup_mult,linorder,SUP_mult_left,nogoodname,nonnegative,ordered_semiring}"  
  shows 
  "( (embc \<phi>) **q (Q * R)) \<le> ((embc \<phi>) **q Q) * ((embc \<phi>) **q R)"
  proof (rule le_funI)
    fix h
    have "( (embc \<phi>) **q (Q * R)) h  =  (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. embc \<phi> h1 * (Q * R) h2)"
      unfolding sep_conj_q_alt by simp
    also have "... = (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. embc \<phi> h1 * Q h2 * R h2)" apply (rule SUP_cong) 
       apply simp
      by (auto simp: mult.assoc)    
    also have "... =   (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. (embc \<phi> h1 * Q h2) * ( embc \<phi> h1  * R h2))"
      apply (subst (1) embc_squared)
      by (simp add: mult_ac)
    also have "... \<le> (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. (embc \<phi> h1 * Q h2)) * (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}.  ( embc \<phi> h1  * R h2))"
      by (rule SUP_times_distrib2_general)
    also have "... = (((embc \<phi>) **q Q) * ((embc \<phi>) **q R)) h"  by (simp add: local.sep_conj_q_alt)
    finally show "( (embc \<phi>) **q (Q * R)) h \<le> (((embc \<phi>) **q Q) * ((embc \<phi>) **q R)) h".
  qed

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

  have *: "\<And> a b c. (a::ennreal) * max b c = max (a*b) (a*c)"  
    apply (auto simp add: max_def mult_left_mono) 
    apply(rule antisym) 
    by (simp_all add: mult_left_mono) 

  have sup_times_distrib: "\<And> a b c. (a::ennreal) * sup b c = sup (a*b) (a*c)" 
    unfolding supmax by (fact *)


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
      by auto
    also have "\<dots> = sup (P **q Q) (P **q R) h"
      unfolding sep_conj_q_alt apply simp
      by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
    finally have "(P **q sup Q R) h = sup (P **q Q) (P **q R) h ".
  }
  then show "(P **q (sup Q R)) = sup (P **q Q) (P **q R)" by auto

next
  show "(P **q Q + R) \<le> (P **q Q) + (P **q R)" 
  proof (rule le_funI)
    fix h
    have "(P **q (Q + R)) h = (SUP (x,y):{(x,y)|x y. h = x + y \<and> x ## y}. (P x * Q y) + (P x * R y) )"
      unfolding sep_conj_q_alt  by(simp add: algebra_simps) 
    also have "\<dots> = (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. (P (fst x) * Q (snd x)) + (P (fst x) * R (snd x)) )"
      apply(rule Sup_cong) by force    
    also have "\<dots> \<le> (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x) * Q (snd x) )
                    + (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x) * R (snd x) )" 
      by (rule SUP_plus_subdistrib)
    also have "\<dots> = ((P **q Q) + (P **q R)) h"
      unfolding sep_conj_q_alt apply simp     
      by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
    finally show "(P **q (Q + R)) h \<le> ((P **q Q) + (P **q R)) h " .
  qed
next
  show "( (emb \<phi>) **q (Q * R)) \<le> ((emb \<phi>) **q Q) * ((emb \<phi>) **q R)"
  proof (rule le_funI)
    fix h
    have "( (emb \<phi>) **q (Q * R)) h  =  (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. emb \<phi> h1 * (Q * R) h2)" unfolding sep_conj_q_alt by simp
    also have "... = (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. emb \<phi> h1 * Q h2 * R h2)" apply (rule SUP_cong) 
       apply simp
      by (auto simp: mult.assoc)
    also have "... =   (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. (emb \<phi> h1 * Q h2) * ( emb \<phi> h1  * R h2))"
      apply (subst (1) emb_squared)
      by (simp add: mult_ac)
    also have "... \<le> (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. (emb \<phi> h1 * Q h2)) * (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}.  ( emb \<phi> h1  * R h2))"
      by (rule SUP_times_distrib2)
    also have "... = (((emb \<phi>) **q Q) * ((emb \<phi>) **q R)) h"  by (simp add: local.sep_conj_q_alt)
    finally show "( (emb \<phi>) **q (Q * R)) h \<le> (((emb \<phi>) **q Q) * ((emb \<phi>) **q R)) h".
  qed
qed



subsubsection \<open>Or\<close>
lemma ennreal_supmax: "\<And>x y::ennreal. sup x y = max x y" 
  apply (rule antisym) by auto   


lemma emb_or: "emb (X or Y) = (sup (emb X) (emb Y))" 
  unfolding emb_def apply(rule ext) unfolding  sup_fun_def apply auto
  by(auto simp add: ennreal_supmax max_def) 


subsubsection \<open>monotonicity of @{term "( **q)"}\<close>

text \<open>theorem 3.7\<close>
 

lemma sep_conj_q_mono:
  fixes X X' :: "_ \<Rightarrow> 'c::{SUP_mult_left, ab_semigroup_mult, ordered_semiring, nonnegative}"
  shows 
   "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (X **q Y) \<le> (X' **q Y')"  
  apply (auto intro: le_funI SUP_mono simp add: sep_conj_q_alt mult_mono le_funD)  
  apply(rule le_funI)
  apply(rule SUP_mono) apply auto
  subgoal for h1 h2
  apply(rule exI[where x=h1])
    apply(rule exI[where x=h2]) apply safe
    apply(rule mult_mono) by (auto simp: zero_smallest le_funD)
  done

lemma sep_conj_q_mono_ennreal:
  fixes X X' :: "_ \<Rightarrow> ennreal"
  shows 
   "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (X **q Y) \<le> (X' **q Y')"  
  by (force intro: le_funI SUP_mono simp add: sep_conj_q_alt mult_mono le_funD)  



lemma sep_conj_q_impl1_ennreal:
  fixes P :: "_ \<Rightarrow> ennreal"
  assumes P: "\<And>h. P h \<le> I h"
  shows "(P **q R) h \<le> (I **q R) h" 
  by (metis (no_types, lifting) assms le_funD le_fun_def star_comm_nice sup.absorb_iff2 theorem_3_6(1)) 
   (* crazy sledgehammer proof *) 

lemma sep_conj_q_impl1:
  fixes P :: "_ \<Rightarrow> 'c::{ab_semigroup_mult,linorder,SUP_mult_left,nogoodname,nonnegative,ordered_semiring}"
  assumes P: "\<And>h. P h \<le> I h"
  shows "(P **q R) h \<le> (I **q R) h" 
  by (metis (no_types, lifting) assms le_funD le_fun_def star_comm_nice sup.absorb_iff2 theorem_3_6_general1)  
   (* crazy sledgehammer proof *)



lemma sep_conj_q_impl_ennreal :
  fixes P Q :: "_ \<Rightarrow> ennreal"
  assumes P: "\<And>h. P h \<le> P' h"
  assumes Q: "\<And>h. Q h \<le> Q' h"
  shows "(P **q Q) h \<le> (P' **q Q') h"
  using sep_conj_q_mono_ennreal  
  by (simp add: P Q le_funD le_funI)  


subsubsection \<open>is @{term "(-*qq)"} monotonic\<close>


lemma nn: "(\<not> x < (top::'b::{complete_lattice})) = (x = top)" 
  using top.not_eq_extremum by blast
lemma nn_bot: "(\<not> x > (bot::'b::{complete_lattice})) = (x = bot)" 
  using bot.not_eq_extremum by blast





lemma sep_impl_q_monoR: 
  fixes P :: "_\<Rightarrow>'b::{divide_right_mono,inverse,SUP_mult_left,linorder}"
  shows "Y \<le> Y' \<Longrightarrow> (P -*qq Y) \<le> (P -*qq Y')"  
  unfolding sep_impl_qq_def
  apply(rule le_funI)
  apply(rule Inf_mono)
  apply auto
  subgoal for h h' apply(rule exI[where x=h']) 
    apply auto  
    by (simp add: divide_right_mono_general le_funD)
  subgoal for h h' apply(rule exI[where x=h']) 
    apply auto  
     apply (auto simp add: nn divide_right_mono_general le_funD)    
    by (metis le_funD not_less) 
  done                   


lemma sep_impl_q_monoR': 
  fixes P :: "_\<Rightarrow>'b::{divide_right_mono,inverse,SUP_mult_left,linorder}"
  shows "Y \<le> Y' \<Longrightarrow> (P -*qq Y) h \<le> (P -*qq Y') h"  
  using sep_impl_q_monoR le_fun_def by fast

lemma "(a::ennreal) div b = a / b" by auto
  
lemma ennreal_inverse_antimono:
  "(a::ennreal) \<le> b \<Longrightarrow> inverse b \<le> inverse a"
  apply(cases a; cases b; cases "a=0"; cases "b=0") 
     apply simp_all
   apply(simp add: inverse_ennreal)   
  using ennreal_neq_top top.extremum_uniqueI by blast   

lemma NOTsep_impl_q_monoL: 
  shows "~(\<forall>P' P Y. P' \<le> P \<longrightarrow> (P -*qq Y) \<le> (P' -*qq Y))"  
proof -
  let ?half = "(\<lambda>_. 1::ennreal)"
  let ?one = "(\<lambda>_. \<infinity>::ennreal)"
  have "?half \<le> ?one" by (auto simp: le_fun_def)  
  have "  (?one -*qq ?one) <= (?half -*qq ?one)"
    unfolding sep_impl_qq_def apply (auto simp add: le_fun_def INF_constant)
    oops 
    

lemma sep_impl_q_monoL: 
  shows "P' \<le> P \<Longrightarrow> (P -*qq Y) \<le> (P' -*qq Y)"  
  unfolding sep_impl_qq_def
  apply(rule le_funI)
  apply(rule INF_mono) apply auto oops
(*
lemma sep_impl_q_monoL: 
  shows "P' \<le> P \<Longrightarrow> (P -*qq Y) \<le> (P' -*qq Y)"  
proof -
  assume "P' \<le> P"
  then have "\<And>x. {h'. x ## h' \<and> 0 < P' h' \<and> (P' h' < \<infinity> \<or> Y (x + h') < \<infinity>)}
          \<subseteq> {h'. x ## h' \<and> 0 < P h' \<and> (P h' < \<infinity> \<or> Y (x + h') < \<infinity>)}"
    apply auto 
    subgoal for h h' apply(drule le_funD[where x=h']) by auto
    subgoal for h h' apply(drule le_funD[where x=h'])  
  oops

lemma sep_impl_q_antimonoL: 
  shows "P' \<le> P \<Longrightarrow> (P -*qq Y) \<le> (P' -*qq Y)"  
  unfolding sep_impl_qq_def
  apply(rule le_funI)

  apply(rule INF_mono)   (* TODO: I think one looses here already ! *)
  
  subgoal for  h h'  
    apply(rule bexI[where x=h']) 
    subgoal    
      apply(drule le_funD[where x=h']) apply auto
      subgoal apply(drule ennreal_inverse_antimono) unfolding divide_ennreal_def 
        using mult_left_mono by fa st force
      subgoal apply(drule ennreal_inverse_antimono) unfolding divide_ennreal_def 
        using mult_left_mono by fas tforce   
      done
    subgoal   apply(drule le_funD[where x=h'])  apply auto  apply (auto simp: nn)
      oops 


lemma sep_impl_q_mono: 
  shows "P' \<le> P \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (P -*qq Y) \<le> (P' -*qq Y')"  
  apply(rule order.trans)
  apply(rule sep_impl_q_monoR) apply simp oops
 (* apply(rule sep_impl_q_monoL) apply simp *)
  *)

subsubsection \<open>adjointness of star and magicwand\<close>

text \<open>theorem 3.9\<close>

lemma adjoint_ltor: "(X **q (emb P)) \<le> Y \<Longrightarrow> X \<le> (P -*q Y)"
proof -
  assume "(X **q emb P) \<le> Y"
  with star_comm have "(emb P **q X) \<le> Y"
    apply(subst star_comm) .
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
        using eq99' by (auto simp: sep_add_ac) 
      also have "\<dots> = (P -*q Y) h"
        unfolding sep_impl_q_alt by simp
      finally show ?thesis .
    qed
  qed 
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
  have eq79: "\<And>h h'. h ## h' \<Longrightarrow> (bot < P h' \<or> bot < Y (h+h') )  \<Longrightarrow> (P h' < top \<or> Y (h+h') < top) \<Longrightarrow> ( X h \<le> Y (h + h') / P h') \<longleftrightarrow> X h * P h' \<le> Y(h+h') "
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
  also have "... \<longleftrightarrow> (\<forall>h. X h \<le> (INF h':{h'. h ## h' \<and> (bot < P h' \<or> bot < Y (h+h') ) \<and> (P h' < top \<or> Y (h+h') < top) }. Y (h + h') / P h'))" 
    unfolding sep_impl_qq_def
    by simp  
  also have "... \<longleftrightarrow> (\<forall>h h'. h ## h' \<and> (bot < P h' \<or> bot < Y (h+h') ) \<and> (P h' < top \<or> Y (h+h') < top)  \<longrightarrow> X h \<le> Y (h + h') / P h')" 
    by (simp add: le_INF_iff)
  also have "... \<longleftrightarrow>  (\<forall>h h'. h ## h' \<and> (bot < P h' \<or> bot < Y (h+h') ) \<and> (P h' < top \<or> Y (h+h') < top)  \<longrightarrow> X h * P h' \<le> Y (h + h'))"
    using eq79 by auto 
  also have "... \<longleftrightarrow> (\<forall>a b. a ## b \<longrightarrow> X a * P b \<le> Y (a + b))" 
    apply auto
    subgoal for a b
      apply (cases "bot < P b")
      subgoal
        apply( cases "P b < top"; cases "Y (a+b) < top")
           apply (auto simp: nn) by force
        subgoal
        apply( cases "P b < top"; cases "Y (a+b) < top")
             apply (auto simp: nn nn_bot)
          subgoal  
            by (metis SUP_least SUP_mult_left empty_iff not_less_bot order_less_le)   
          subgoal  
            by (metis bot.extremum_strict)   
done
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

  
lemma adjoint: "(X **q (emb P)) \<le> Y \<longleftrightarrow> X \<le> (P -*q Y)"
  using adjoint_general by simp

subsubsection \<open>quantitative modus ponens\<close>

text \<open>theorem 3.8\<close>

lemma quant_modus_ponens:
  "( (emb P) **q (P -*q X)) \<le> X"
proof -
  have " (P -*q X) \<le> (P -*q X)" by simp
  then have "(((P -*q X) **q emb P) \<le> X)"
    using adjoint[symmetric, where X="(P -*q X)" and Y=X] by auto
  then show ?thesis apply(subst star_comm) .
qed

lemma quant_modus_ponens_general:
  shows "( P **q (P -*qq X)) \<le> X"
proof -
  have " (P -*qq X) \<le> (P -*qq X)" by simp
  then have "(((P -*qq X) **q  P) \<le> X)"
    using adjoint_general[symmetric, where X="(P -*qq X)" and Y=X]  by auto
  then show ?thesis apply(subst star_comm) .
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
      using sep_conj_q_mono [OF Xmono] by(auto dest: le_funD)
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



lemma intuitionistic_q_is_attained_at_h_wand: 
  fixes
    X :: "_ \<Rightarrow> ennreal"
  assumes "intuitionistic_q X"
  shows "X h = (INF h':{h'. h ## h' }. X (h + h') )"
  apply(rule antisym)
  subgoal 
    apply(rule Inf_greatest) using assms by(auto dest: intuitionistic_qD)
  subgoal 
      apply(rule INF_lower2[where i=0])  by auto
  done


lemma tightest_intuitionistic_expectations_wand_general:
    "intuitionistic_q (\<^bold>1 -*qq X)" 
    "(\<^bold>1 -*qq X) \<le> X"
    "\<And>X'. intuitionistic_q X' \<Longrightarrow> X' \<le> X \<Longrightarrow>  X' \<le> (\<^bold>1 -*qq X)"
proof -
  {  
    fix h h'
    assume a: "h ## h'"
    have "(\<^bold>1 -*qq X) h = (INF h':{h'. h ## h' \<and> 0 < emb (\<lambda>s. True) h' \<and> (emb (\<lambda>s. True) h' < \<infinity> \<or> X (h + h') < \<infinity>)}.
        X (h + h') / emb (\<lambda>s. True) h')" 
      unfolding sep_impl_qq_def  by simp
    also have "\<dots> \<le> (INF h'a:{h'a. h + h' ## h'a \<and> 0 < emb (\<lambda>s. True) h'a \<and> (emb (\<lambda>s. True) h'a < \<infinity> \<or> X (h + h' + h'a) < \<infinity>)}.
        X (h + h' + h'a) / emb (\<lambda>s. True) h'a)" 
      apply(rule INF_mono)
      subgoal for h'' apply(rule bexI[where x="h' + h''"])
        using a by (auto simp: sep_disj_addI3 emb_def sep_add_assoc dest: sep_add_disjD)
      done
    also have "\<dots> = (\<^bold>1 -*qq X) (h + h')" 
      unfolding sep_impl_qq_def  by simp
    finally have "(\<^bold>1 -*qq X) h \<le> (\<^bold>1 -*qq X) (h + h')" .
  } note * = this (* gives the lemma in the brackets a name *) 

  show 1: "intuitionistic_q (\<^bold>1 -*qq X)"
    apply(rule intuitionistic_qI2)
    by(rule *)
next
  show "(\<^bold>1 -*qq X) \<le> X"
  proof (rule le_funI)
    fix h
    have "(\<^bold>1 -*qq X) h = (INF h':{h'. h ## h' \<and> 0 < emb (\<lambda>s. True) h' \<and> (emb (\<lambda>s. True) h' < \<infinity> \<or> X (h + h') < \<infinity>)}.
        X (h + h') / emb (\<lambda>s. True) h')"
      unfolding sep_impl_qq_def by simp   
    also have "\<dots> \<le> X h"
      apply(rule INF_lower2[where i=0]) by (auto simp: emb_def ennreal_div_one)  
    finally show "(\<^bold>1 -*qq X) h \<le> X h" .
  qed
next
  fix X'
  assume "intuitionistic_q X'" and Xmono: "X' \<le> X"
  {    
    fix h (* for arbitrary but fixed h *)
    have "X' h = (INF h':{h'. h ## h' }. X' (h + h') )"
      apply(rule intuitionistic_q_is_attained_at_h_wand) by fact
    also have "\<dots> = (INF h':{h'. h ## h' \<and> 0 < emb (\<lambda>s. True) h' \<and> (emb (\<lambda>s. True) h' < \<infinity> \<or> X' (h + h') < \<infinity>)}.
        X' (h + h') / emb (\<lambda>s. True) h')"
      by (auto simp: emb_def ennreal_div_one)  
    also have "\<dots> = (\<^bold>1 -*qq X') h"
      unfolding sep_impl_qq_def by simp
    also have "\<dots> \<le> (\<^bold>1 -*qq X) h" 
      apply(rule sep_impl_q_monoR') by fact
    finally have "X' h \<le> (\<^bold>1 -*qq X) h" .
  }
  then show "X' \<le> (\<^bold>1 -*qq X)" by(auto intro: le_funI)
qed




lemma tightest_intuitionistic_expectations_wand:
    "intuitionistic_q (sep_true -*q X)" 
    "(sep_true -*q X) \<le> X"
    "\<And>X'. intuitionistic_q X' \<Longrightarrow> X' \<le> X \<Longrightarrow>  X' \<le> (sep_true -*q X)"
  using tightest_intuitionistic_expectations_wand_general by auto

abbreviation (input)
  pred_ex_q :: "('b \<Rightarrow> 'a \<Rightarrow> ennreal) \<Rightarrow> 'a \<Rightarrow> ennreal" (binder "EXSq " 10) where
  "EXSq x. P x \<equiv> \<lambda>h. SUP x. P x h"


end


subsection \<open>Introduce sized separation algebras\<close>

print_classes
term size
term Size
class sized = 
  fixes Size :: "'a \<Rightarrow> ennreal"


class normed_sep_algebra = sep_algebra  + sized  +
  assumes size0: "Size 0 = 0" 
    and sizeadd_triangle: "Size (h1+h2) \<le> Size h1 + Size h2"
    and sizeadd: "h1 ## h2 \<Longrightarrow> Size (h1+h2) = Size h1 + Size h2"
begin
 
text \<open>Heap Size Law #3:\<close>

lemma heap_size_law_3: "(X **q Y) * Size \<le> ((X * Size) **q Y) + ((Y * Size) **q X) "
proof (rule le_funI)
  fix h 
  have "((X **q Y) * Size) h = (SUP x:{(x, y). h = x + y \<and> x ## y}. case x of (x, y) \<Rightarrow> X x * Y y) * Size h"
    unfolding sep_conj_q_alt by simp
  also have "\<dots> = (SUP x:{(x, y). h = x + y \<and> x ## y}. (case x of (x, y) \<Rightarrow> X x * Y y) *  Size h)" 
    by (simp add: SUP_mult_right_ennreal) 
  also have "\<dots> = (SUP (h1,h2):{(x, y). h = x + y \<and> x ## y}.  (X h1 * Y h2 * Size h1) + X h1 * Y h2 *  Size h2)" 
    apply(rule SUP_cong) by(auto simp: sizeadd distrib_left) 
  also have "\<dots> \<le> (SUP (h1, h2):{(x, y). h = x + y \<and> x ## y}. X h1 * Y h2 * Size h1) +
    (SUP (h1, h2):{(x, y). h = x + y \<and> x ## y}. X h1 * Y h2 * Size h2)" (is "_ \<le> ?L + ?R")
    by (rule SUP_plus_subdistrib2)
  also 
  have L: "?L = (SUP (x, y):{(x, y). h = x + y \<and> x ## y}. X x * Size x * Y y)"
    apply (rule SUP_cong) by (auto simp: mult_ac) 
  have R: "?R = (SUP (x, y):{(x, y). h = x + y \<and> x ## y}. Y x * Size x * X y)"
    apply (rule Sup_cong) by (auto simp: sep_add_ac mult_ac)  
  have "?L + ?R = (SUP (x, y):{(x, y). h = x + y \<and> x ## y}. X x * Size x * Y y) 
                      + (SUP (x, y):{(x, y). h = x + y \<and> x ## y}. Y x * Size x * X y)"  
    by(simp only: L R) 
  also have "\<dots> = (((X * Size) **q Y) + ((Y * Size) **q X)) h"
    unfolding sep_conj_q_alt plus_fun_def times_fun_def by auto 
  finally show "((X **q Y) * Size) h \<le> ((X * Size **q Y) + (Y * Size **q X)) h " .
qed

end

term dom
 

datatype ('a, 'b) heap = Heap (theheap: "'a \<Rightarrow> 'b option")

instantiation "heap"  :: (type, type) sized
begin

fun Size_heap where 
  "Size_heap (Heap x) = (if finite (dom x) then ennreal (card (dom x)) else \<infinity>)"

instance apply standard done


end


instantiation "heap" :: (type,type) sep_algebra
begin

  fun plus_heap :: "('a, 'b) heap \<Rightarrow> ('a, 'b) heap \<Rightarrow> ('a, 'b) heap" where
    "plus_heap f g = Heap (\<lambda>x.  (if x \<in> dom (theheap f) then theheap f x 
                                    else theheap g x))"

  fun sep_disj_heap :: "('a, 'b) heap \<Rightarrow> ('a, 'b) heap \<Rightarrow> bool" where
    "sep_disj_heap f g \<longleftrightarrow> dom (theheap f) \<inter> dom (theheap g) = {}"


lemma [simp]: "\<And>x. theheap (Heap x) = x" by auto

lemma exx: "theheap x = theheap y \<Longrightarrow> x = y" using heap.expand by auto

definition zero_heap where [simp]: "zero_heap =  Heap (\<lambda>_. None)"

instance apply standard apply auto
  subgoal apply(rule heap.expand) apply simp apply (rule ext)
    apply auto  
    by (metis option.exhaust)  
  subgoal apply(rule ext) by(auto)
  subgoal apply(rule ext) by (auto split: if_splits)
  subgoal by fastforce  
  subgoal by (smt disjoint_iff_not_equal domIff option.simps(3))  
  done

end

thm heap.case heap.split

lemma dom_Heap_union:
  "dom (theheap (Heap x + Heap xa)) = dom x \<union> dom xa"
  by (auto split: if_splits)

lemma **:  "Size x = 
    (if finite (dom (theheap x)) then ennreal (card (dom (theheap x))) else \<infinity>)"
  apply(cases x) by auto

instance "heap" :: (type,type) normed_sep_algebra
  apply standard 
  subgoal by auto
  subgoal for h1 h2
    apply(cases h1; cases h2) 
    apply (auto simp: dom_Heap_union ** split: if_splits simp del: plus_heap.simps)
    apply(subst ennreal_plus[symmetric]) apply simp apply simp
    apply(rule ennreal_leI) 
    using card_Un_le of_nat_mono by fastforce  
  subgoal for h1 h2
    apply(cases h1; cases h2) 
    apply (auto simp: dom_Heap_union ** split: if_splits simp del: plus_heap.simps)
    apply(subst ennreal_plus[symmetric]) apply simp apply simp 
    apply(rule ennreal_cong) 
    by (simp add: card_Un_disjoint)  
  done


instantiation nat :: sized
begin

fun Size_nat :: "nat\<Rightarrow>ennreal" where "Size_nat n = (ennreal n)"

instance by standard
end



text  \<open>nat is a separation algebra\<close>
 

instantiation nat :: sep_algebra
begin
  fun sep_disj_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
   "sep_disj_nat n1 n2 \<longleftrightarrow> True" 
  
  fun sep_plus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
   "sep_plus_nat n1 n2 = n1 + n2" 

  instance
    apply standard by auto
end


instance nat :: normed_sep_algebra
  apply(standard)  by auto

instantiation prod :: (sized,sized) sized
begin
definition Size_prod :: "'a \<times> 'b \<Rightarrow> ennreal"  where [simp]:
  "Size_prod  = (\<lambda>(a,b). Size a + Size b)"

instance by standard

end
 
instance prod :: (normed_sep_algebra, normed_sep_algebra) normed_sep_algebra
  apply standard
    apply (auto simp: zero_prod_def size0 plus_prod_def)
  subgoal 
    by (simp add: sizeadd_triangle add_mono_thms_linordered_semiring(1) semiring_normalization_rules(20))
  subgoal by(simp add: sep_disj_prod_def sizeadd)
  done






lemma fixes
  a b :: "(string \<Rightarrow> int tsa_opt) \<Rightarrow> ennreal_inv"
shows "(a **q b) = c"
  oops
  





end