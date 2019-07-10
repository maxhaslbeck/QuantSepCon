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

"Median_Of_Medians_Selection.Median_Of_Medians_Selection"

begin 

section \<open>Misc\<close>


subsection \<open>stuff about complete lattices:\<close>


lemma nn: "(\<not> x < (top::'b::{complete_lattice})) = (x = top)" 
  using top.not_eq_extremum by blast
lemma nn_bot: "(\<not> x > (bot::'b::{complete_lattice})) = (x = bot)" 
  using bot.not_eq_extremum by blast

(* I think this rule is actually stronger than Inf_mono *)
lemma Inf_mono_my:
  assumes "\<And>b::'c::{complete_lattice}. b \<in> B \<Longrightarrow> b < top \<Longrightarrow> \<exists>a\<in>A. a \<le> b"
  shows "Inf A \<le> Inf B"
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

lemma INF_mono_my: "(\<And>m. m \<in> B \<Longrightarrow> g m < top \<Longrightarrow> \<exists>n\<in>A. f n \<le> g m) \<Longrightarrow> (INF n:A. (f n) ::'c::{complete_lattice}) \<le> (INF n:B. g n)"
  using Inf_mono_my [of "g ` B" "f ` A"] by auto

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

(*
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
 
*)

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


thm complete_lattice_axioms
term complete_lattice

term "\<infinity> - \<infinity>"
lemma "\<infinity> - \<infinity> = (\<infinity>::ennreal)" by simp

(* ordered_ab_semigroup_add *)
 
print_classes  
          
term "(div)"
                
thm algebra_simps
thm add_mono[no_vars]
locale quant_sep_con =  comm_monoid oper neutr
  for  
      oper :: "'b::{complete_lattice} \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>*" 70)
    and neutr :: "'b" ("\<^bold>1") +
  fixes
      divide :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>div" 70)
  assumes 
         AA: "\<And>x::'b. x \<^bold>div \<^bold>1 = x"   (* gilt für domain    top  *    /  1
                                                    [0,1]     1    *   /   1
                                                   ennreal    0    +   -   0  *)  
  and BB: "\<And>x::'b. x > bot \<Longrightarrow> x \<^bold>div bot = top"    
  and DD: "\<And>x. x \<^bold>* bot = bot"   
  and FF: "bot < \<^bold>1" 
(*  and GG: "\<And>x::'b. x < top \<Longrightarrow> x \<^bold>div top = bot"    *)

  and SUP_mult_left': "\<And>c A. c \<^bold>* Sup A = Sup (((\<^bold>*) c) ` A)"
(*  and ff: "\<And>A. (SUP (x,y):A. x \<^bold>* y) \<le> (SUP (x,y):A. x ) \<^bold>* (SUP (x,y):A. y)" *)
  and oper_mono: "\<And>a b c d. a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a \<^bold>* c \<le> b \<^bold>* d"
  and  divide_right_mono_general: "\<And>a b c. a \<le> b \<Longrightarrow> a \<^bold>div c \<le> b \<^bold>div c" 
  and  divide_right_antimono_general: "\<And>a b c. c \<le> b \<Longrightarrow> a \<^bold>div b \<le> a \<^bold>div c" 
  and JJ:  "\<And>x. x < top \<Longrightarrow>  top \<^bold>div x = top"

  and div_mult_adjoint: \<comment> \<open>The essence of equation 79\<close>
     "\<And>A B C :: 'b. (bot < C \<or> bot < B ) \<Longrightarrow> (C < top \<or> B < top) \<Longrightarrow> (A \<le> B \<^bold>div C) \<longleftrightarrow> A \<^bold>* C \<le> B"
   

begin 
 (*
lemma SUP_times_distrib2_general:
  fixes g :: "_\<Rightarrow>_\<Rightarrow>'b"
  shows "(SUP (x,y):A. f x y \<^bold>* g x y) \<le> (SUP (x, y):A. f x y) \<^bold>* (SUP (x, y):A. g x y)"   
  using ff[where A="(\<lambda>(x,y). (f x y, g x y)) ` A"]  
  by (auto simp: split_beta)  *)

thm mult_left_mono[no_vars] 
lemma oper_left_mono: "\<And>a b c d. a \<le> b   \<Longrightarrow> c \<^bold>* a \<le> c \<^bold>* b"
  apply(rule oper_mono) by auto

lemma SUP_times_distrib2_general:
  fixes g :: "_\<Rightarrow>_\<Rightarrow>'b"
  shows "(SUP (x,y):A. f x y \<^bold>* g x y) \<le> (SUP (x, y):A. f x y) \<^bold>* (SUP (x, y):A. g x y)"  
  apply(rule SUP_least)
  apply auto apply(rule oper_mono)
      by (auto intro: SUP_upper2)


lemma SUP_mult_left: "\<And>c f. c \<^bold>* (SUP i:I. f i) = (SUP i:I. c \<^bold>* f i)"
  apply(subst SUP_mult_left') by simp


lemma SUP_mult_right: "(SUP i:I. f i) \<^bold>* c = (SUP i:I. f i \<^bold>* c)"
  by (simp add: commute SUP_mult_left) 



lemma sup_times_distrib: "(a::'b) \<^bold>* sup b c = sup (a\<^bold>*b) (a\<^bold>*c)" 
proof -
  have f: "\<And>a b :: 'b. sup a b = Sup {a,b}"  
    by simp   
  show ?thesis
    apply(simp only: f)
    apply(subst SUP_mult_left') by simp
qed


context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin


term "INF x:A. (f x::'b)"
  
end
end


locale quant_sep_con_oper2 =  quant_sep_con oper neutr divide
  for  
      oper :: "'b::{complete_lattice} \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>*" 70)
    and neutr :: "'b" ("\<^bold>1") 
    and  divide :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>div" 70) +
  fixes
      oper2 :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<^bold>+" 65)
    assumes
      plusmal_distrib[algebra_simps]: "\<And>a b c. a \<^bold>* (b \<^bold>+ c) = a \<^bold>* b \<^bold>+ a \<^bold>* c"
      and oper2_mono: "\<And>a b c d. a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a \<^bold>+ c \<le> b \<^bold>+ d"
begin


lemma SUP_plus_subdistrib: "\<And>S. \<And>f g::_\<Rightarrow>'b. (SUP x:S. f x \<^bold>+ g x) \<le> (SUP x:S. f x) \<^bold>+ (SUP x:S. g x)"
  by (simp add: SUP_least SUP_upper oper2_mono)

end


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
  
lemma ennreal_mult_divide: "b > 0 \<Longrightarrow> b < (\<infinity>::ennreal) \<Longrightarrow> b * (a / b) = a" 
  apply(cases a; cases b) apply (auto simp: divide_ennreal ennreal_mult[symmetric])
   by (simp add: ennreal_divide_eq_top_iff ennreal_mult_eq_top_iff)    

lemma eq79_ennreal: fixes A B C :: ennreal
  shows "(bot < C \<or> bot < B )  \<Longrightarrow> (C < top \<or> B < top) \<Longrightarrow> ( A \<le> B / C) \<longleftrightarrow> A * C \<le> B "
  apply(cases "C<bot")
  subgoal by auto
  apply(cases "C < top")
  subgoal   
    by (metis bot.extremum bot_ennreal  
            divide_le_posI_ennreal divide_less_ennreal dual_order.irrefl 
              ennreal_divide_eq_0_iff ennreal_divide_eq_top_iff ennreal_mult_less_top ennreal_times_divide 
                eq_iff eq_refl leD le_less_linear linear mult.commute mult_eq_0_iff order.not_eq_order_implies_strict
                  order.strict_trans1 order_trans top_greatest)   
  subgoal  
    by (metis bot.extremum_strict bot_ennreal ennreal_divide_top ennreal_mult_eq_top_iff mult_eq_0_iff nn nn_bot not_le)  
  done

lemma "\<not> c < (b::ereal) \<longleftrightarrow> b \<le> c" using not_less by blast
definition "divv a (b::ereal) = min 1 (a / b)"
lemma fixes a b c :: ereal
  assumes A: "0 \<le> a" "a \<le> 1"   "0 \<le> b" "b \<le> 1"   "0 \<le> c" "c \<le> 1"
    and B1: "(0 < b \<or> 0 < c )" and B2: "(b< 1 \<or> c < 1)"
  shows "(a \<le>divv b c) \<longleftrightarrow> a * c \<le> b"
proof(cases "b>c")
  case True
  then have *: "divv b c = 1" using A apply(auto simp: divv_def min_def) 
    by (metis abs_ereal_ge0 divide_ereal_def ereal_divide_one ereal_divide_same ereal_infty_less(1) ereal_inverse_antimono_strict ereal_mult_left_mono leD less_imp_le)
  have "a \<le> divv b c \<longleftrightarrow> a \<le> 1" unfolding * by simp
  also have "\<dots> \<longleftrightarrow> a * c \<le> b" using True  
    by (metis assms(2) assms(5) ereal_mult_left_mono  less_imp_triv mult.comm_neutral mult.commute not_less order_trans)   
  finally show ?thesis .
next
  case False
  then show ?thesis 
    using A apply(auto  simp: divv_def)
    subgoal  
      by (metis antisym ereal_divide_Infty(1) ereal_le_divide_pos ereal_zero_times less_eq_ereal_def mult.commute)  
    subgoal 
      apply(cases "c<0")  
      subgoal by auto
      subgoal  (* HERE I NEED THE EXTRA ASSUMPTIONS *)
        apply(cases "c=0") 
        subgoal using  B1 by simp
        subgoal using B2   
          by (metis ereal_divide_Infty(1) ereal_divide_one ereal_infty_less(1) ereal_le_divide_pos leD linorder_cases mult.commute)  
        done
      done
    done
  qed 


(*
  subgoal by auto 
    subgoal
      apply rule
      subgoal using mult_left_mono[where a="A" and b="B / C" and c="C"]
        apply(cases "C<\<infinity>")
        subgoal    
          apply (simp add:  mult.commute)  
          apply(subst (asm) ennreal_mult_divide) apply (auto simp add: bot_ennreal)  
        subgoal  
          by (auto simp: nn ) 
        done
      subgoal
        apply(cases "C<\<infinity>")
        subgoal  
          by (s mt divide_less_ennreal ennreal_mult_divide infinity_ennreal_def less_le mult_left_mono not_less)
        subgoal 
          apply auto
          apply(simp only: nn)
          apply simp  (* oopsie \<forall>x. x/\<infinity> = 0 *)           
          using  nn 
          by (m etis ennreal_mult_eq_top_iff linorder_not_less)      
        done
      done 
done *)


interpretation FULL: quant_sep_con   "( * )" "1::ennreal"  "(/)"   
  apply standard subgoal  
    by (simp add: ennreal_div_one)  
  subgoal  
    by (simp add: bot_ennreal)  
  subgoal 
    by (simp add: bot_ennreal)  
  subgoal 
    by (simp add: bot_ennreal)  
  subgoal     
    using SUP_mult_left_ennreal[where f=id] by simp 
  subgoal 
    by (auto simp: mult_mono)  
  subgoal
    by (simp add: divide_right_mono_ennreal)
      
  subgoal for a b c
    using ennreal_div_antimono by simp
  subgoal using ennreal_top_divide by simp
  subgoal apply(rule eq79_ennreal) by auto
  done

 (*
datatype UnitInterval = ZOI ennreal 

interpretation PROB: quant_sep_con  "( * )"  "(/)"   "1::UnitInterval" 
  apply standard  .
 *)


instantiation "bool" :: one
begin
definition "one_bool == True"
instance by standard
end 



interpretation BOOL: quant_sep_con   "(\<and>)" "True" "\<lambda>x y. y \<longrightarrow> x"  
  apply standard 
  by auto

instantiation "dual_ord" :: (Inf) Sup
begin
lift_definition Sup_dual_ord :: "('a dual_ord) set \<Rightarrow> 'a dual_ord" is
  "\<lambda>A :: 'a set. Inf A" .
instance ..
end

instantiation "dual_ord" :: (Sup) Inf
begin
lift_definition Inf_dual_ord :: "('a dual_ord) set \<Rightarrow> 'a dual_ord" is
  "\<lambda>A :: 'a set. Sup A" .
instance ..
end


instantiation "dual_ord" :: (sup) inf
begin
lift_definition inf_dual_ord :: "('a dual_ord)   \<Rightarrow> 'a dual_ord \<Rightarrow> 'a dual_ord" is
  "\<lambda>a b :: 'a  . sup a b" .
instance ..
end

instantiation "dual_ord" :: (inf) sup
begin
lift_definition sup_dual_ord :: "('a dual_ord)   \<Rightarrow> 'a dual_ord \<Rightarrow> 'a dual_ord" is
  "\<lambda>a b :: 'a  . inf a b" .
instance ..
end


thm dual_semilattice
thm dual_lattice
thm dual_complete_lattice

(*
instance "dual_ord" :: (complete_lattice) complete_lattice
  oops

 
  term "a::'b::{complete_lattice}"
 



interpretation ERT: quant_sep_con "(+)" "\<lambda>_. undefined"  "0::ennreal dual_ord"
  apply standard by (auto intro: Sup_least Sup_upper Inf_lower Inf_greatest)
*)

context quant_sep_con 
begin          
context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin

definition emb  where "emb P = (\<lambda>h. if P h then \<^bold>1 else bot)"

lemma emb_range: "emb P x \<in> {bot,\<^bold>1}" unfolding emb_def by auto

lemma emb_squared: "emb P x = emb P x \<^bold>* emb P x"
  apply (cases "emb P x = bot") using emb_range apply (auto simp: DD) by fastforce

lemma emb_1: "emb P h = \<^bold>1 \<longleftrightarrow> P h"
  apply (auto simp: emb_def) using FF by blast  

definition sep_empty_q :: "'a \<Rightarrow> 'b"  where
  "sep_empty_q \<equiv> emb (\<lambda>h. h = 0)"

subsection \<open>Quantitative Separating Conjunction\<close>

definition
  sep_conj_q  (infixr "**q" 35)
  where
  "P **q Q \<equiv> \<lambda>h. Sup { P x \<^bold>* Q y | x y. h=x+y \<and> x ## y}" (* why not Sup ? *)

lemma sep_conj_q_alt : "(P **q Q) = (\<lambda>h. (SUP (x,y): {(x,y). h=x+y \<and> x ## y}. P x \<^bold>* Q y))"
  unfolding  sep_conj_q_def
  apply auto apply(rule ext)
  apply(rule arg_cong[where f=Sup]) by auto

lemma sep_conj_q_SUP: "(P **q Q) = (\<lambda>h. (SUP i:{(x,y)| x y. h=x+y \<and> x ## y}. (\<lambda>(x,y). P x \<^bold>* Q y) i))"
  unfolding sep_conj_q_def apply auto  apply (rule ext)
  apply(rule Sup_cong) by auto 

 

subsection \<open>Quantitative Separating Implication - Magic Wand\<close>

 

definition
  sep_impl_qq  :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a  \<Rightarrow> 'b ) \<Rightarrow> 'a \<Rightarrow> 'b"   (infixr "-*qq" 35)
  where 
  "P -*qq Q \<equiv> \<lambda>h. INF h': { h'. h ## h' \<and> (bot < P h' \<or> bot < Q (h+h') ) \<and> (P h' < top \<or> Q (h+h') < top)}. (Q (h + h')) \<^bold>div (P h')"

lemma 
  "(P -*qq Q) = (\<lambda>h. INF h': { h'. h ## h' \<and> (bot < P h' \<or> bot < Q (h+h') ) \<and> (P h' = top \<longrightarrow> Q (h+h') < top)}. (Q (h + h')) \<^bold>div (P h'))"
  oops

subsection \<open>Embedding of SL into QSL\<close>
 
abbreviation sep_impl_q (infixr "-*q" 35) where   "(P -*q Q) \<equiv> (emb P -*qq Q)" 
 
  

end
end

locale quant_sep_con_one = quant_sep_con oper  neutr divide for  
      oper :: "'b::{complete_lattice} \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>*" 64)
    and divide :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>div" 64)
    and neutr :: "'b" ("\<^bold>1")
  + assumes neutral_is_top: "\<^bold>1 = top"
  and CC: "bot < (top::'b)"  

begin 
context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin


lemma sep_impl_q_alt_general:
  fixes  Q :: "'a \<Rightarrow> 'b"
 
  shows 
  "(P -*q Q) = (\<lambda>h. INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
proof  (rule ext)
  fix h
  have T: "{h'. h ## h' \<and> ((bot::'b) < emb P h' \<or> (bot::'b) < Q (h + h')) \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}
      = {h'. h ## h' \<and>  (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < top)}
       \<union>  {h'. h ## h' \<and>(bot::'b) = emb P h' \<and> (bot::'b) < Q (h + h') \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}" 
    using bot.not_eq_extremum by fastforce    

  let ?A ="{h'. h ## h' \<and> (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}"
  let ?B ="{h'.  h ## h'   \<and> Q (h + h') < top \<and> P h'}"

  have 1: "(INF h':?A. Q (h + h') \<^bold>div emb P h') = (INF x:?B. Q (h + x))"
    apply(rule INF_cong)
    subgoal
      apply rule 
        subgoal (* ?A \<subseteq> ?B *) apply (auto simp: AA emb_def CC FF) using neutral_is_top by auto
        subgoal (* ?B \<subseteq> ?A *) by (auto simp: AA emb_def CC FF)
        done
    subgoal by (simp add: AA emb_def)  
    done

  have "(\<exists>h'. h ## h' \<and> (bot::'b) < top \<and> Q (h + h') < top  \<and> P h') \<Longrightarrow> (INF h': { h'. h ## h' \<and> P h'}. Q (h + h')) < top"
    apply safe subgoal for h' 
      apply(rule order.strict_trans1)
       apply(rule INF_lower[where i=h']) by auto
    done
  
  have "~(\<exists>h'. h ## h' \<and> (bot::'b) < top \<and> Q (h + h') < top  \<and> P h') \<Longrightarrow> (INF h': { h'. h ## h' \<and> P h'}. Q (h + h')) = top"
    apply auto  
    by (metis Inf_UNIV Inf_top_conv(2) UNIV_I top.not_eq_extremum)  
 
  have 2: "(INF h':{h'. h ## h' \<and> (bot::'b) = emb P h' \<and> (bot::'b) < Q (h + h')  \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}. Q (h + h') \<^bold>div emb P h')
      = top" 
    unfolding emb_def apply auto
    using BB by simp_all 
  

  have F: "{ h'. h ## h' \<and> P h'} = { h'. h ## h' \<and> P h' \<and> Q (h + h') = top} \<union> { h'. h ## h' \<and> P h' \<and> Q (h + h') < top}"
    using top.not_eq_extremum by blast


  have 3: "(INF h':{h'. h ## h' \<and> P h' \<and> Q (h + h') = top}. Q (h + h')) = top"
    by auto
 
  have "(P -*q Q) h = inf (INF h':{h'. h ## h' \<and> (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}. Q (h + h') \<^bold>div emb P h')
     (INF h':{h'. h ## h' \<and> (bot::'b) = emb P h'\<and> (bot::'b) < Q (h + h') \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}. Q (h + h') \<^bold>div emb P h')"
    unfolding sep_impl_qq_def  
    unfolding T
    unfolding INF_union by simp
  also have "\<dots>  = (INF x:{h'.  h ## h'  \<and> Q (h + h') < top \<and> P h'}. Q (h + x))"
    unfolding 1 2 by simp
  also have "\<dots> = ( INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
      unfolding F 
    unfolding INF_union unfolding 3 apply simp
    apply(rule INF_cong) by auto
  finally show "(P -*q Q) h = (INF h':{h'. h ## h' \<and> P h'}. Q (h + h'))" .
qed

end
end
 

 
context quant_sep_con 
begin 
context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin


lemma sep_impl_q_alt_general:
  fixes  Q :: "'a \<Rightarrow> 'b" 
  shows 
  "inf \<^bold>1 ((P -*q Q) h) = inf \<^bold>1 (INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
proof -
  have T: "{h'. h ## h' \<and> ((bot::'b) < emb P h' \<or> (bot::'b) < Q (h + h')) \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}
      = {h'. h ## h' \<and>  (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < top)}
       \<union>  {h'. h ## h' \<and>(bot::'b) = emb P h' \<and> (bot::'b) < Q (h + h') \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}" 
    using bot.not_eq_extremum by fastforce    

  let ?A = "{h'.  h ## h'   \<and> Q (h + h') < top \<and> P h'}"
  let ?B = "{h'. h ## h' \<and> (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}"
  have AB: "?A \<subseteq> ?B"  by (auto simp: emb_def FF)

  have KK: "(INF h':?B-?A. Q (h + h') \<^bold>div emb P h') \<ge> \<^bold>1"
    unfolding le_Inf_iff apply auto
      apply(auto simp: emb_def AA split: if_splits) 
    using top.not_eq_extremum by fastforce 


    have 1: "inf \<^bold>1 (INF h':?B. Q (h + h') \<^bold>div emb P h')
      = inf \<^bold>1 (INF x:?A. Q (h + x))"
    proof -
      have B_decompose: "?B = (?B - ?A) \<union> (?A)"  using AB by blast
      thm INF_union
      have i: "(INF h':?A. Q (h + h') \<^bold>div emb P h') = (INF h':?A.  Q (h + h'))"
        apply(rule INF_cong) apply simp by (auto simp: emb_def AA)

      have ii: "inf \<^bold>1 (INF h':?B-?A. Q (h + h') \<^bold>div emb P h') = \<^bold>1" 
        using KK  
        by (simp add: antisym) 

      have "(INF h':?B. Q (h + h') \<^bold>div emb P h')  = inf (INF h':?B - ?A. Q (h + h') \<^bold>div emb P h') (INF h':?A. Q (h + h') \<^bold>div emb P h')"
        apply(subst B_decompose) by(rule INF_union)
      also have "\<dots> = inf (INF h':?B - ?A. Q (h + h') \<^bold>div emb P h') (INF h':?A.  Q (h + h'))"
        unfolding i by simp
      finally have iii: "(INF h':?B. Q (h + h') \<^bold>div emb P h') = inf (INF h':?B - ?A. Q (h + h') \<^bold>div emb P h') (INF h':?A.  Q (h + h'))" .

      have "inf \<^bold>1 (INF h':?B. Q (h + h') \<^bold>div emb P h') 
              = inf \<^bold>1 (inf (INF h':?B - ?A. Q (h + h') \<^bold>div emb P h') (INF h':?A.  Q (h + h')))" unfolding iii by simp
      also have "\<dots> = inf (inf \<^bold>1 (INF h':?B - ?A. Q (h + h') \<^bold>div emb P h')) (INF h':?A.  Q (h + h'))"
        by(simp add: inf.assoc)
      also have "\<dots> = inf \<^bold>1 (INF h':?A.  Q (h + h'))"
        unfolding ii apply simp done
      finally show ?thesis .
    qed 


  have "(\<exists>h'. h ## h' \<and> (bot::'b) < top \<and> Q (h + h') < top  \<and> P h') \<Longrightarrow> (INF h': { h'. h ## h' \<and> P h'}. Q (h + h')) < top"
    apply safe subgoal for h' 
      apply(rule order.strict_trans1)
       apply(rule INF_lower[where i=h']) by auto
    done
  
  have "~(\<exists>h'. h ## h' \<and> (bot::'b) < top \<and> Q (h + h') < top  \<and> P h') \<Longrightarrow> (INF h': { h'. h ## h' \<and> P h'}. Q (h + h')) = top"
    apply auto  
    by (metis Inf_UNIV Inf_top_conv(2) UNIV_I top.not_eq_extremum)  
 
  have 2: "(INF h':{h'. h ## h' \<and> (bot::'b) = emb P h' \<and> (bot::'b) < Q (h + h')  \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}. Q (h + h') \<^bold>div emb P h')
      = top" 
    unfolding emb_def apply auto
    using BB by simp_all 
  

  have F: "{ h'. h ## h' \<and> P h'} = { h'. h ## h' \<and> P h' \<and> Q (h + h') = top} \<union> { h'. h ## h' \<and> P h' \<and> Q (h + h') < top}"
    using top.not_eq_extremum by blast


  have 3: "(INF h':{h'. h ## h' \<and> P h' \<and> Q (h + h') = top}. Q (h + h')) = top"
    by auto
 
  have "inf \<^bold>1 ((P -*q Q) h) = inf \<^bold>1 (inf (INF h':{h'. h ## h' \<and> (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}. Q (h + h') \<^bold>div emb P h')
     (INF h':{h'. h ## h' \<and> (bot::'b) = emb P h'\<and> (bot::'b) < Q (h + h') \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}. Q (h + h') \<^bold>div emb P h'))"
    unfolding sep_impl_qq_def  
    unfolding T
    unfolding INF_union by simp
  also have "\<dots> =  inf \<^bold>1 (inf (INF h':{h'. h ## h' \<and> (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}. Q (h + h') \<^bold>div emb P h')
     top)"
    unfolding 2 by simp
  also have "\<dots> = inf \<^bold>1 (INF h':{h'. h ## h' \<and> (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}. Q (h + h') \<^bold>div emb P h')"
    by simp
  also have "\<dots>  = inf \<^bold>1 (INF x:{h'.  h ## h'  \<and> Q (h + h') < top \<and> P h'}. Q (h + x))"
    unfolding 1 by simp
  also have "\<dots> = inf \<^bold>1 ( INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
      unfolding F 
    unfolding INF_union unfolding 3 apply simp  
    apply(rule arg_cong[where f="\<lambda>x. inf \<^bold>1 x"])
    apply(rule INF_cong) by auto
  finally show "inf \<^bold>1 ((P -*q Q) h) =  inf \<^bold>1 (INF h':{h'. h ## h' \<and> P h'}. Q (h + h'))" .
qed



lemma sep_impl_q_alt_general':
  fixes  Q :: "'a \<Rightarrow> 'b" 
  assumes "\<^bold>1 = top"
  shows 
  "((P -*q Q) h) = (INF h': { h'. h ## h' \<and> P h'}. Q (h + h'))"
  using assms sep_impl_q_alt_general by simp

subsubsection \<open>Conservativity of QSL as an assertion language\<close>


lemma Sup_zeroone: " P \<subseteq> {bot,\<^bold>1} \<Longrightarrow> Sup P \<in> {bot,\<^bold>1}"
  by (metis (no_types, lifting) Sup_insert ccpo_Sup_singleton insertCI insert_Diff subset_insert_iff subset_singletonD sup_bot.left_neutral)

lemma sep_conj_q_range: "((emb P) **q (emb Q)) h \<in> {bot,\<^bold>1}"
  unfolding sep_conj_q_def  
  apply(rule Sup_zeroone) 
  apply (auto simp: emb_def) using   AA BB DD      by auto  
   

lemma Inf_zeroone: "P \<noteq> {} \<Longrightarrow> P \<subseteq> {bot,\<^bold>1} \<Longrightarrow> Inf P \<in> {bot,\<^bold>1}" 
  by (metis Inf_lower bot.extremum_uniqueI cInf_singleton insertCI subset_insert subset_singletonD)  

lemma Inf_zeroonetop: " P \<subseteq> {bot,\<^bold>1,top} \<Longrightarrow> Inf P \<in> {bot,\<^bold>1,top}"  
  by (smt Inf_empty Inf_insert Inf_lower bot.extremum_uniqueI cInf_singleton insertCI insert_Diff subset_insert_iff)

lemma sep_conj_q_leq1: "((emb P) **q (emb Q)) h \<le> \<^bold>1"
  using sep_conj_q_range[of P Q h] by auto 

lemma emb_not_bot: "bot < emb P h \<longleftrightarrow> emb P h = \<^bold>1"
  using FF by (auto simp: emb_def) 
lemma emb_not_bot2: "bot \<noteq> emb P h \<longleftrightarrow> emb P h = \<^bold>1"
    "emb P h \<noteq> bot \<longleftrightarrow> emb P h = \<^bold>1"
  using FF by (auto simp: emb_def) 
 

lemma "\<^bold>1 \<^bold>div emb P h' \<noteq> bot \<Longrightarrow> \<^bold>1 < top \<Longrightarrow>  \<^bold>1 \<^bold>div emb P h' = \<^bold>1" 
  unfolding emb_def apply(cases "P h'")
  subgoal 
    by (auto simp: AA BB FF)
    subgoal 
      apply (auto simp: AA BB FF)
  oops

lemma sep_impl_q_rangezeroonetop: "((P -*q (emb Q)) h) \<in> {bot,\<^bold>1,top}"  
  unfolding sep_impl_qq_def  
    apply(rule Inf_zeroonetop)  
  subgoal apply (auto simp: emb_not_bot emb_not_bot2 AA  )
    apply(auto simp: emb_def AA BB FF)
    done
  done

lemma inf_1_cuts: "a \<in> {bot, \<^bold>1, top} \<Longrightarrow> inf \<^bold>1 a \<in> {bot, \<^bold>1}"
proof -
  assume "a \<in> {bot, \<^bold>1, top}" 
  then have "inf \<^bold>1 a \<in> { \<^bold>1, bot}"
    using inf_bot_right inf_idem inf_top_right by blast
  then show ?thesis
    using bot_ennreal by auto
qed

lemma sep_impl_q_range: "inf \<^bold>1 ((P -*q (emb Q)) h) \<in> {bot, \<^bold>1}"  
  apply(rule inf_1_cuts) by(rule sep_impl_q_rangezeroonetop)   

lemma quant_wand_conservative: 
  fixes P :: "'a \<Rightarrow> bool"
  shows "(P  \<longrightarrow>* Q) h  \<longleftrightarrow> inf \<^bold>1 (((emb P) -*qq (emb Q)) h)  = \<^bold>1"
proof - 
  (* rather ugly proof, DB's fault ;) *)
  fix h
  have " inf \<^bold>1 ((P -*q (emb Q)) h) = \<^bold>1 \<longleftrightarrow> inf \<^bold>1 ((INF h':{h'. h ## h' \<and> P h'}. emb Q (h + h'))) = \<^bold>1" 
    unfolding sep_impl_q_alt_general by simp 
  also have "\<dots> \<longleftrightarrow> (\<forall>h'. h ## h' \<and> P h' \<longrightarrow> Q (h + h'))"
    apply(rule antisym)
    subgoal apply auto
      apply(cases "{h'. h ## h' \<and> P h'} = {}")
      subgoal by simp
      subgoal for h' apply auto proof (rule ccontr, goal_cases)
        case (1 x)
        from 1(2-6) have "inf \<^bold>1 (INF h':{h'. h ## h' \<and> P h'}. emb Q (h + h')) \<le> bot" 
          apply(intro le_infI2)
          apply(intro INF_lower2[where i=h']) apply simp by (simp add: emb_def)
        then show ?case using 1(1) FF by auto
      qed 
      done
    subgoal   by (auto simp: emb_def INF_constant) 
    done
  also have "\<dots> \<longleftrightarrow> (P  \<longrightarrow>* Q) h" unfolding sep_impl_def by auto
  finally show "(P  \<longrightarrow>* Q) h \<longleftrightarrow> inf \<^bold>1 ((P -*q (emb Q)) h) = \<^bold>1" by simp
qed 

lemma quant_star_conservative:
  fixes P :: "'a \<Rightarrow> bool"
  shows "(P ** Q) h \<longleftrightarrow> ((emb P) **q (emb Q)) h = \<^bold>1" 
proof -
  have "(P ** Q) h = (\<exists>xa y. xa ## y \<and> h = xa + y \<and> emb P xa = \<^bold>1 \<and> emb Q y = \<^bold>1)"
    unfolding sep_conj_def emb_1 by auto
  also have "\<dots> = (Sup { emb P x \<^bold>* emb Q y | x y. h=x+y \<and> x ## y} = \<^bold>1)"
    apply rule
    subgoal  
      apply(rule antisym)
      subgoal apply(subst sep_conj_q_leq1[unfolded sep_conj_q_def] ) by simp
      subgoal apply(rule Sup_upper) by force 
      done
    subgoal
    proof (rule ccontr, goal_cases)
      case 1
      from 1(2) have "\<And>x y. (x,y) \<in> {(x,y) | x y. h = x + y \<and> x ## y} \<Longrightarrow> emb P x \<^bold>* emb Q y = bot "
        apply auto  unfolding emb_def by (auto split: if_splits simp: DD)  
      then have "Sup {emb P x \<^bold>* emb Q y |x y. h = x + y \<and> x ## y} \<le>  bot"
        apply(intro Sup_least) by auto
      with 1(1) show "False" using FF by simp 
    qed 
    done
  also have "\<dots> = (((emb P) **q (emb Q)) h = \<^bold>1)" unfolding sep_conj_q_def by simp
  finally show ?thesis .
qed

 


subsection \<open>Properties of Quantitative Separating Connectives\<close> 

subsubsection \<open>Commutative monoid\<close>

lemma star_assoc:
  fixes x y z :: "'a \<Rightarrow> 'b"
  shows  "(x **q (y **q z))  = ((x **q y) **q z) "
proof (rule ext)
  fix h 

  have "(x **q (y **q z)) h    = (SUP (xa, ya):{(x, y) |x y. h = x + y \<and> x ## y}. x xa \<^bold>* (SUP (x, ya):{(x, y) |x y. ya = x + y \<and> x ## y}. y x \<^bold>* z ya))" 
    unfolding sep_conj_q_SUP by auto 
  also have "\<dots> = (SUP xa:{(x, y). h = x + y \<and> x ## y}. case xa of (xa, ya) \<Rightarrow> SUP i:{(x, y). ya = x + y \<and> x ## y}. (case i of (h21, h22) \<Rightarrow> x xa \<^bold>* y h21 \<^bold>* z h22))"
    by(simp add: SUP_mult_left prod.case_distrib assoc)  
  also have "\<dots> = (SUP xa:{(x, y). h = x + y \<and> x ## y}. SUP i:{((fst xa),x, y)| x y . snd xa = x + y \<and> x ## y}. (case i of (b, h21, h22) \<Rightarrow> x b \<^bold>* y h21 \<^bold>* z h22))"
    apply(rule SUP_cong) apply simp
    apply safe apply(rule Sup_cong) by force 
  also have "\<dots> = (SUP xa:{(h1, h2, h3). h = h1 + h2 + h3 \<and> h1 ## h2 + h3 \<and> h1 ## h2 \<and> h1 ## h3 \<and> h3 ## h2 }. case xa of (h1, h2, h3) \<Rightarrow> x h1 \<^bold>* y h2 \<^bold>* z h3)"
    apply(subst SUP_UNION[symmetric]) 
    apply(rule SUP_cong)
    subgoal
      apply (auto simp: sep_add_ac dest: sep_disj_addD  ) 
      by (metis sep_add_assoc sep_disj_addD1 sep_disj_addD2)  
    by auto
  also have "\<dots> = (SUP xa:{(x, y). h = x + y \<and> x ## y}. SUP i:{(h1,h2, snd xa)| h1 h2 . fst xa = h1 + h2 \<and> h1 ## h2}. (case i of (h1, h2, h3) \<Rightarrow> x h1 \<^bold>* y h2 \<^bold>* z h3))"
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
  also have "\<dots> = (SUP xa:{(h12, h3). h = h12 + h3 \<and> h12 ## h3}. case xa of (h12, h3) \<Rightarrow> SUP h12:{(x, y). h12 = x + y \<and> x ## y}. (case h12 of (h1, h2) \<Rightarrow> (x h1 \<^bold>* y h2 \<^bold>* z h3)))"
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
  fixes X Y :: "_ \<Rightarrow> 'b"
  shows  "(X **q Y) = (Y **q X)"
  unfolding sep_conj_q_SUP
  apply(rule ext)
  apply(rule Sup_cong)
  apply auto
  subgoal
    apply (auto simp add: commute sep_disj_commute sep_add_commute)
    done
  subgoal for a b
    apply(rule Set.image_eqI[where x="(b,a)"])
    apply auto
      apply (simp add:  commute)
    using sep_add_commute apply auto[1]
    apply (simp add: sep_disj_commute)
    done
  done

lemma star_comm_nice:
  fixes X Y :: "_ \<Rightarrow> 'b"
  shows  "(X **q Y) = (Y **q X)"
  unfolding sep_conj_q_SUP
  apply(rule ext)
  apply(rule Sup_cong)
  apply (auto simp add: commute sep_add_ac)
  done


lemma emp_neutral1:
  "(X **q sep_empty_q) = X"
  unfolding sep_conj_q_def sep_empty_q_def emb_def
  apply(rule ext)
  apply(rule antisym)
  subgoal
    by (auto intro!: Sup_least simp: DD)
  subgoal
    by (auto intro: Sup_upper)
  done

lemma emp_neutral2 : 
  "(sep_empty_q **q X) = X"
  apply(simp only: star_comm)
  apply(rule emp_neutral1) done

lemmas emp_neutral = emp_neutral1 emp_neutral2

lemma sep_conj_q_left_commute:
  fixes P Q R :: "'a \<Rightarrow> 'b"
  shows  "(P **q Q **q R) = (Q **q P **q R)"
  apply(subst  star_assoc)
  apply(subst  star_comm)
  apply(subst  star_assoc) by simp


lemmas sep_conj_q_c = star_comm sep_conj_q_left_commute


subsubsection \<open>(Sub)distributivity Laws\<close>


lemma theorem_3_6_general1: 
  fixes
      P :: "'a \<Rightarrow> 'b"  
  shows
  "(P **q (sup Q R)) = sup (P **q Q) (P **q R)"
proof 
  fix h
  have "(P **q (sup Q R)) h = Sup {P x \<^bold>* sup Q R y |x y. h = x + y \<and> x ## y}"
    unfolding sep_conj_q_def by simp
  also have "\<dots> = Sup {P x \<^bold>* sup (Q y) (R y) |x y. h = x + y \<and> x ## y}"
    by simp
  also have "\<dots> = Sup { sup (P x \<^bold>* Q y) (P x \<^bold>* R y) |x y. h = x + y \<and> x ## y}"
    apply(subst  sup_times_distrib)  by simp
  also have "\<dots> = (SUP x:{(x, y). h = x + y \<and> x ## y}. case x of (x,y) \<Rightarrow> sup (P x \<^bold>* Q y) (P x \<^bold>* R y))" 
    apply (rule arg_cong[where f=Sup]) by auto
  also have "\<dots> = (SUP x:{(x, y). h = x + y \<and> x ## y}. sup (P (fst x) \<^bold>* Q (snd x)) (P (fst x) \<^bold>* R (snd x)))"
    apply (rule arg_cong[where f=Sup])  
    by (meson prod.case_eq_if)    
  also have "\<dots> = sup (SUP x:{(x, y). h = x + y \<and> x ## y}. P (fst x) \<^bold>* Q (snd x))
   (SUP x:{(x, y). h = x + y \<and> x ## y}. P (fst x) \<^bold>* R (snd x))"
    apply(subst SUP_sup_distrib[symmetric]) 
    subgoal apply auto apply(rule exI[where x=h])  apply(rule exI[where x=0]) by auto
    by auto
  also have "\<dots> = sup (P **q Q) (P **q R) h"
    unfolding sep_conj_q_alt apply simp
    by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
  finally show "(P **q sup Q R) h = sup (P **q Q) (P **q R) h ". 
qed

end
end

context  quant_sep_con_oper2
begin
context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin

lemma theorem_3_6_general2: 
  fixes
      P :: "_ \<Rightarrow> 'b"  
  shows
  "((P **q (\<lambda>h. Q h \<^bold>+ R h)) h) \<le> ((P **q Q) h) \<^bold>+ ((P **q R) h)"
proof -
  have "(P **q (\<lambda>h. Q h \<^bold>+ R h)) h = (SUP (x,y):{(x,y)|x y. h = x + y \<and> x ## y}. (P x \<^bold>* Q y) \<^bold>+ (P x \<^bold>* R y) )"
    unfolding sep_conj_q_alt  by (simp add: plusmal_distrib) 
  also have "\<dots> = (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. (P (fst x) \<^bold>* Q (snd x))  \<^bold>+ (P (fst x) \<^bold>* R (snd x)) )"
    apply(rule Sup_cong) by force    
  also have "\<dots> \<le> (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x)  \<^bold>* Q (snd x) )
                   \<^bold>+ (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x)  \<^bold>* R (snd x) )" 
    by (rule SUP_plus_subdistrib)
  also have "\<dots> = ((P **q Q) h)  \<^bold>+ ((P **q R) h)"
    unfolding sep_conj_q_alt apply simp     
    by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
  finally show "((P **q (\<lambda>h. Q h \<^bold>+ R h)) h) \<le> ((P **q Q) h) \<^bold>+ ((P **q R) h)" .
qed

end
end

context  quant_sep_con
begin
context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin

lemma theorem_3_6_general3: 
  fixes 
      Q :: "_ \<Rightarrow> 'b"  
  shows 
  "( (emb \<phi>) **q (\<lambda>h. Q h \<^bold>* R h)) h \<le> ((emb \<phi>) **q Q) h \<^bold>* ((emb \<phi>) **q R) h"
  proof -
    have "( (emb \<phi>) **q (\<lambda>h. Q h \<^bold>* R h)) h  =  (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. emb \<phi> h1 \<^bold>* (\<lambda>h. Q h \<^bold>* R h) h2)"
      unfolding sep_conj_q_alt by simp
    also have "... = (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. emb \<phi> h1 \<^bold>* Q h2 \<^bold>* R h2)" apply (rule SUP_cong) 
       apply simp
      by (auto simp: assoc)    
    also have "... =   (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. (emb \<phi> h1 \<^bold>* Q h2) \<^bold>* ( emb \<phi> h1  \<^bold>* R h2))"
      apply (subst (1) emb_squared)
      by (simp add: ac_simps)
    also have "... \<le> (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}. (emb \<phi> h1  \<^bold>* Q h2)) \<^bold>* (SUP (h1, h2):{(h1, h2). h = h1 + h2 \<and> h1 ## h2}.  ( emb \<phi> h1  \<^bold>* R h2))"
      by (rule SUP_times_distrib2_general)
    also have "... = ((emb \<phi>) **q Q) h \<^bold>* ((emb \<phi>) **q R) h"  by (simp add: local.sep_conj_q_alt)
    finally show "( (emb \<phi>) **q (\<lambda>h. Q h \<^bold>* R h)) h \<le> ((emb \<phi>) **q Q) h \<^bold>* ((emb \<phi>) **q R) h".
  qed

(*
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
    unfolding supmax by (fact * )


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
qed *)



subsubsection \<open>Or\<close>
lemma ennreal_supmax: "\<And>x y::ennreal. sup x y = max x y" 
  apply (rule antisym) by auto   


lemma emb_or: "emb (X or Y) = (sup (emb X) (emb Y))" 
  unfolding emb_def apply(rule ext) unfolding  sup_fun_def apply auto
  by(auto simp add: ennreal_supmax max_def) 


subsubsection \<open>monotonicity of @{term "( **q)"}\<close>

text \<open>theorem 3.7\<close>
 

lemma sep_conj_q_mono:
  fixes X X' :: "_ \<Rightarrow> 'b"
  shows 
   "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (X **q Y) \<le> (X' **q Y')"  
  apply (auto intro: le_funI SUP_mono simp add: sep_conj_q_alt le_funD)  
  apply(rule le_funI)
  apply(rule SUP_mono) apply auto
  subgoal for h1 h2
  apply(rule exI[where x=h1])
    apply(rule exI[where x=h2]) apply safe
    apply(rule oper_mono) by (auto simp: le_funD)
  done

lemma sep_conj_q_mono_ennreal:
  fixes X X' :: "_ \<Rightarrow> 'b"
  shows 
   "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (X **q Y) \<le> (X' **q Y')"  
  by (force intro: le_funI SUP_mono simp add: sep_conj_q_alt oper_mono le_funD)  



lemma sep_conj_q_impl1:
  fixes P :: "_ \<Rightarrow> 'b"
  assumes P: "\<And>h. P h \<le> I h"
  shows "(P **q R) h \<le> (I **q R) h" 
  using sep_conj_q_mono_ennreal 
  by (metis assms dual_order.refl le_funD le_fun_def) 



lemma sep_conj_q_impl_ennreal :
  fixes P Q :: "_ \<Rightarrow> 'b"
  assumes P: "\<And>h. P h \<le> P' h"
  assumes Q: "\<And>h. Q h \<le> Q' h"
  shows "(P **q Q) h \<le> (P' **q Q') h"
  using   P Q 
  by (auto intro: le_funI intro!: sep_conj_q_mono_ennreal[THEN le_funD])  


subsubsection \<open>is @{term "(-*qq)"} monotonic\<close>





lemma "\<not> bot < (x::'b) \<longleftrightarrow> x = bot" 
  by (simp add: nn_bot)  

thm Inf_mono[no_vars]

lemma "Inf A \<le> Inf B \<Longrightarrow> (\<And>b::'c::{complete_lattice}. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<le> b)"
  oops 
 
  thm INF_mono

 

lemma sep_impl_q_monoR: 
  fixes P :: "_\<Rightarrow>'b"
  shows "Y \<le> Y' \<Longrightarrow> (P -*qq Y) \<le> (P -*qq Y')"  
  unfolding sep_impl_qq_def
  apply(rule le_funI)
  apply(rule Inf_mono_my) 
  apply auto
  subgoal for h h' apply(rule exI[where x=h']) 
    apply auto  
    by (simp add: divide_right_mono_general le_funD)
  subgoal for h h' apply(rule exI[where x=h']) 
    apply auto  
     apply (auto simp add: nn divide_right_mono_general le_funD)         
    by (metis le_funD less_le_not_le) 
  subgoal for h h' apply(rule exI[where x=h'])  
    apply (auto simp add: nn divide_right_mono_general le_funD)
      apply(auto simp: nn_bot)
  proof (rule classical, goal_cases)
    case 1
    then have Pbot: "P h' = bot" by (auto simp: nn_bot)
    from 1(4) Pbot BB have "Y' (h + h') \<^bold>div P h' = top" by simp
      with 1(2) have "False" by simp     
    then show ?case by simp
  qed
   
  subgoal for h h' apply(rule exI[where x=h']) 
    apply auto 
      apply (auto simp add: nn divide_right_mono_general le_funD nn_bot)
    subgoal 
  proof (rule classical, goal_cases)
    case 1
    then have Pbot: "P h' = bot" by (auto simp: nn_bot)
    from 1(4) Pbot BB have "Y' (h + h') \<^bold>div P h' = top" by simp
      with 1(2) have "False" by simp     
    then show ?case by simp
  qed
  subgoal apply(drule le_funD[where x="h+h'"])
    by auto
  done     
  done


lemma sep_impl_q_monoR': 
  fixes P :: "_\<Rightarrow>'b"
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
  apply(rule Inf_mono_my) apply auto oops
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
  oops *)
 
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

lemma sep_impl_q_antimonoL: 
  shows "P' \<le> P \<Longrightarrow> (P -*qq Y) \<le> (P' -*qq Y)"  
  unfolding sep_impl_qq_def
  apply(rule le_funI)

  apply(rule INF_mono_my)   (* TODO: I think one looses here already ! *)

  subgoal for  h h'  
    apply(rule bexI[where x=h'])  apply simp
    subgoal   
      apply(drule le_funD[where x=h']) apply auto
      subgoal apply(rule divide_right_antimono_general) by simp
      subgoal apply(rule divide_right_antimono_general)  by simp
      subgoal apply(rule divide_right_antimono_general)  by simp
      subgoal apply(rule divide_right_antimono_general)  by simp
      done
    subgoal   apply(drule le_funD[where x=h'])  apply auto  apply (auto simp: nn)
      subgoal 
      proof (rule classical, goal_cases)
        case 1 
        from 1(5)  JJ   have "top \<^bold>div P' h' = top" by simp
        with 1(1) have "False" by simp     
        then show ?case by simp
      qed
      subgoal 
      proof (rule classical, goal_cases)
        case 1 
        from 1(5)  JJ   have "top \<^bold>div P' h' = top" by simp
        with 1(1) have "False" by simp     
        then show ?case by simp
      qed
      done
    done
  done

lemma sep_impl_q_mono: 
  shows "P' \<le> P \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (P -*qq Y) \<le> (P' -*qq Y')"  
  apply(rule order.trans)
  apply(rule sep_impl_q_monoR) apply simp oops
 (* apply(rule sep_impl_q_monoL) apply simp *)
   

subsubsection \<open>adjointness of star and magicwand\<close>

text \<open>theorem 3.9\<close>
(*
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
qed*)


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
lemma general_mult_divide: "\<And>a b. b > bot \<Longrightarrow> b < (top::'b) \<Longrightarrow> b \<^bold>* (a \<^bold>div b) = a" 
  sorry

thm mult_left_mono


(* for bool
    "(bot < A \<or> bot < B )" and 2: "(A < top \<or> B < top)"
  is 
    A \<or> B and ~A \<or> ~B
  equiv with
    (A\<and>~B) or (~A\<and>B)
*)



lemma adjoint_general:
  shows "(X **q P) \<le> Y \<longleftrightarrow> X \<le> (P -*qq Y)"
proof -   
  have "X \<le> (P -*qq Y) \<longleftrightarrow> (\<forall> h. X h \<le> (P -*qq Y) h)"
    by (simp add: le_fun_def)
  also have "... \<longleftrightarrow> (\<forall>h. X h \<le> (INF h':{h'. h ## h' \<and> (bot < P h' \<or> bot < Y (h+h') ) \<and> (P h' < top \<or> Y (h+h') < top) }. Y (h + h') \<^bold>div P h'))" 
    unfolding sep_impl_qq_def
    by simp  
  also have "... \<longleftrightarrow> (\<forall>h h'. h ## h' \<and> (bot < P h' \<or> bot < Y (h+h') ) \<and> (P h' < top \<or> Y (h+h') < top)  \<longrightarrow> X h \<le> Y (h + h') \<^bold>div P h')" 
    by (simp add: le_INF_iff)
  also have "... \<longleftrightarrow>  (\<forall>h h'. h ## h' \<and> (bot < P h' \<or> bot < Y (h+h') ) \<and> (P h' < top \<or> Y (h+h') < top)  \<longrightarrow> X h \<^bold>* P h' \<le> Y (h + h'))"
    using div_mult_adjoint by auto 
  also have "... \<longleftrightarrow> (\<forall>a b. a ## b \<longrightarrow> X a \<^bold>* P b \<le> Y (a + b))" 
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
  also have "... \<longleftrightarrow> ((\<lambda>h. SUP (x, y):{(x, y). h = x + y \<and> x ## y}. X x \<^bold>* P y) \<le> Y)" 
    thm SUP_le_iff
    by (simp add: le_fun_def SUP_le_iff)
  also have "... \<longleftrightarrow> (X **q P) \<le> Y"
    unfolding sep_conj_q_alt
    by simp
  finally show ?thesis by simp
qed

  
lemma adjoint: "(X **q (emb P)) \<le> Y \<longleftrightarrow> X \<le> (P -*q Y)"
  using adjoint_general by blast

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
    X :: "_ \<Rightarrow> 'b"
  assumes "intuitionistic_q X"
  shows "(SUP (h1, h2):{(x, y) |x y. h = x + y \<and> x ## y}. X h1) = X h"
  apply(rule antisym)
  subgoal 
    apply(rule SUP_least) using assms by(auto dest: intuitionistic_qD)
  subgoal 
      apply(rule SUP_upper2[where i="(h,0)"]) by auto
  done
 
text \<open>Tightest intuitionistic expectations\<close>

abbreviation sep_true_q ("1\<^sub>q")  where "1\<^sub>q \<equiv> (emb sep_true)"

theorem tightest_intuitionistic_expectations_star:
  fixes X :: "'a \<Rightarrow> 'b"
  shows
    "intuitionistic_q (X **q 1\<^sub>q)"
    "X \<le> (X **q 1\<^sub>q)"
    "\<And>X'. intuitionistic_q X' \<Longrightarrow> X \<le> X' \<Longrightarrow> (X **q 1\<^sub>q) \<le> X'"
proof -
  show "intuitionistic_q (X **q 1\<^sub>q)" 
  proof (rule intuitionistic_qI2)
    fix h h' :: 'a
    assume a: "h ## h'" 
    have "(X **q 1\<^sub>q) h = (SUP (h1, h2):{(x, y). h = x + y \<and> x ## y}. X h1 \<^bold>* 1\<^sub>q h2)" 
      unfolding sep_conj_q_alt by simp
    also have "\<dots> = (SUP (h1, h2):{(x, y). h = x + y \<and> x ## y}. X h1 \<^bold>* 1\<^sub>q (h2+h'))"
      by (auto simp: emb_def)
    also have "\<dots> \<le> (SUP (h1, h2):{(x, y). h + h' = x + y \<and> x ## y}. X h1 \<^bold>* 1\<^sub>q h2)"
      apply(rule SUP_mono) apply auto
      subgoal for h1 h2 apply(rule exI[where x=h1]) apply(rule exI[where x="h2 + h'"])  
        using a by (force simp: sep_add_assoc dest: sep_add_disjD intro: sep_disj_addI3) 
      done
  also have "\<dots> = (X **q 1\<^sub>q) (h + h')" 
      unfolding sep_conj_q_alt by simp
    finally show "(X **q 1\<^sub>q) h \<le> (X **q 1\<^sub>q) (h + h')" .
  qed
next
  show "X \<le> (X **q 1\<^sub>q)"
  proof (rule le_funI)
    fix h
    have "X h \<le> (SUP (x, y):{(x, y) |x y. h = x + y \<and> x ## y}. X x \<^bold>* emb (\<lambda>s. True) y)"
      apply(rule Sup_upper) apply auto 
      apply(rule Set.image_eqI[where x="(h,0)"]) by (auto simp: emb_def)   
    also have "\<dots> = (X **q 1\<^sub>q) h"
      unfolding sep_conj_q_SUP by simp
    finally show "X h \<le> (X **q 1\<^sub>q) h" .
  qed
next
  fix X'
  assume "intuitionistic_q X'" and Xmono: "X \<le> X'"
  {
    (* for arbitrary but fixed h *)
    fix h
    have "(X **q 1\<^sub>q) h \<le> (X' **q 1\<^sub>q) h"
      using sep_conj_q_mono [OF Xmono] by(auto dest: le_funD)
    also have "\<dots> = (SUP (x, y):{(x, y) |x y. h = x + y \<and> x ## y}. X' x \<^bold>*  1\<^sub>q y)"
      unfolding sep_conj_q_SUP by simp
    also have "\<dots> = (SUP (x, y):{(x, y) |x y. h = x + y \<and> x ## y}. X' x)"
      by (auto simp add: emb_def)
    also have "\<dots> = X' h" 
      apply(rule intuitionistic_q_is_attained_at_h) by fact
    finally have "(X **q 1\<^sub>q) h \<le> X' h" .
  }
  then show "(X **q 1\<^sub>q) \<le> X'" by (auto simp: le_fun_def)
qed



lemma intuitionistic_q_is_attained_at_h_wand: 
  fixes
    X :: "_ \<Rightarrow> 'b"
  assumes "intuitionistic_q X"
  shows "X h = (INF h':{h'. h ## h' \<and> (\<^bold>1 < top \<or> X (h + h') < top) }. X (h + h') )"
  apply(rule antisym)
  subgoal 
    apply(rule Inf_greatest) using assms by(auto dest: intuitionistic_qD)
  subgoal 
    apply(cases "X h<top")
    subgoal apply(rule INF_lower2[where i=0])  by auto
    subgoal by(auto simp: nn)
    done
  done


lemma tightest_intuitionistic_expectations_wand_general:
  fixes X :: "'a \<Rightarrow> 'b"
  shows
    "intuitionistic_q (1\<^sub>q -*qq X)" 
    "(1\<^sub>q -*qq X) \<le> X"
    "\<And>X'. intuitionistic_q X' \<Longrightarrow> X' \<le> X \<Longrightarrow>  X' \<le> (1\<^sub>q -*qq X)"
proof -
  {  
    fix h h' :: 'a
    assume a: "h ## h'"
    have "(1\<^sub>q -*qq X) h = (INF h':{h'. h ## h' \<and> (bot < emb (\<lambda>s. True) h' \<or> bot < X (h + h')) \<and> (emb (\<lambda>s. True) h' < top \<or> X (h + h') < top)}.
        X (h + h') \<^bold>div emb (\<lambda>s. True) h')" 
      unfolding sep_impl_qq_def  by simp
    also have "\<dots> \<le> (INF h'a:{h'a. h + h' ## h'a \<and> (bot < emb (\<lambda>s. True) h'a \<or> bot < X (h + h'+ h'a)) \<and> (emb (\<lambda>s. True) h'a < top \<or> X (h + h' + h'a) < top)}.
        X (h + h' + h'a) \<^bold>div emb (\<lambda>s. True) h'a)" 
      apply(rule INF_mono)
      subgoal for h'' apply(rule bexI[where x="h' + h''"])
        using a FF by (auto simp: sep_disj_addI3 emb_def sep_add_assoc dest: sep_add_disjD)
      done
    also have "\<dots> = (1\<^sub>q -*qq X) (h + h')" 
      unfolding sep_impl_qq_def  by simp
    finally have "(1\<^sub>q -*qq X) h \<le> (1\<^sub>q -*qq X) (h + h')" .
  } note * = this (* gives the lemma in the brackets a name *) 

  show 1: "intuitionistic_q (1\<^sub>q -*qq X)"
    apply(rule intuitionistic_qI2)
    by(rule *)
next
  show "(1\<^sub>q -*qq X) \<le> X"
  proof (rule le_funI)
    fix h
    have "(1\<^sub>q -*qq X) h = (INF h':{h'. h ## h' \<and> (bot < emb (\<lambda>s. True) h' \<or> bot < X (h + h')) \<and> (emb (\<lambda>s. True) h' < top \<or> X (h + h') < top)}.
        X (h + h') \<^bold>div emb (\<lambda>s. True) h')"
      unfolding sep_impl_qq_def by simp   
    also have "\<dots> \<le> X h"
      apply(cases "X h<top")
      subgoal apply(rule INF_lower2[where i=0]) using FF  by (auto simp: emb_def AA)
      subgoal by (auto simp: nn)
      done
    finally show "(1\<^sub>q -*qq X) h \<le> X h" .
  qed
next
  fix X'
  assume "intuitionistic_q X'" and Xmono: "X' \<le> X"
  {    
    fix h (* for arbitrary but fixed h *)
    have "X' h = (INF h':{h'. h ## h' \<and> (\<^bold>1 < top \<or> X' (h + h') < top) }. X' (h + h') )"
      apply(rule intuitionistic_q_is_attained_at_h_wand) by fact
    also have "\<dots> = (INF h':{h'. h ## h' \<and> (bot < emb (\<lambda>s. True) h' \<or> bot < X' (h + h')) \<and> (emb (\<lambda>s. True) h' < top \<or> X' (h + h') < top)}.
        X' (h + h') \<^bold>div emb (\<lambda>s. True) h')"
      using FF by (auto simp: emb_def AA ) 
    also have "\<dots> = (1\<^sub>q -*qq X') h"
      unfolding sep_impl_qq_def by simp
    also have "\<dots> \<le> (1\<^sub>q -*qq X) h" 
      apply(rule sep_impl_q_monoR') by fact
    finally have "X' h \<le> (1\<^sub>q -*qq X) h" .
  }
  then show "X' \<le> (1\<^sub>q -*qq X)" by(auto intro: le_funI)
qed




lemma tightest_intuitionistic_expectations_wand:
  fixes X :: "'a \<Rightarrow> 'b"
  shows
    "intuitionistic_q (sep_true -*q X)" 
    "(sep_true -*q X) \<le> X"
    "\<And>X'. intuitionistic_q X' \<Longrightarrow> X' \<le> X \<Longrightarrow>  X' \<le> (sep_true -*q X)"
  using tightest_intuitionistic_expectations_wand_general by auto

abbreviation (input)
  pred_ex_q :: "('b \<Rightarrow> 'a \<Rightarrow> ennreal) \<Rightarrow> 'a \<Rightarrow> ennreal" (binder "EXSq " 10) where
  "EXSq x. P x \<equiv> \<lambda>h. SUP x. P x h"


end
end



subsection \<open>Showing that quantitative separating connectives
   instantiated for bool yield the boolean separating connectives\<close>

lemma "BOOL.sep_conj_q = sep_conj"
  apply(rule ext) apply (rule ext)
  unfolding sep_conj_def BOOL.sep_conj_q_def
  by auto

lemma "BOOL.sep_impl_qq = sep_impl"
  apply(rule ext) apply (rule ext)
  unfolding sep_impl_def BOOL.sep_impl_qq_def
  by auto





section \<open>Introduce sized separation algebras\<close>

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