theory PotentialMethod
imports QuantSepCon
begin




section \<open>The dual order type\<close>

text \<open>
  The following type is a copy of a given ordered base type, but with the ordering reversed.
  This will be useful later because we can do some of our reasoning simply by symmetry.
\<close>
typedef 'a dual_ord = "UNIV :: 'a set" morphisms of_dual_ord to_dual_ord
  by auto

setup_lifting type_definition_dual_ord

instantiation dual_ord :: (ord) ord
begin

lift_definition less_eq_dual_ord :: "'a dual_ord \<Rightarrow> 'a dual_ord \<Rightarrow> bool" is
  "\<lambda>a b :: 'a. a \<ge> b" .

lift_definition less_dual_ord :: "'a dual_ord \<Rightarrow> 'a dual_ord \<Rightarrow> bool" is
  "\<lambda>a b :: 'a. a > b" .

instance ..
end


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

(*
instance dual_ord :: (preorder) preorder
  by standard (transfer; force simp: less_le_not_le intro: order_trans)+

instance dual_ord :: (linorder) linorder
  by standard (transfer; force simp: not_le)+ *)

instantiation "dual_ord" :: (complete_lattice) complete_lattice
begin

lift_definition bot_dual_ord :: "('a dual_ord)" is top .
lift_definition top_dual_ord :: "('a dual_ord)" is bot .

instance
  by (standard) (transfer; auto intro: Sup_upper Sup_least Inf_lower Inf_greatest)+
end


instantiation "dual_ord" :: (plus) plus
begin

lift_definition plus_dual_ord :: "('a dual_ord) \<Rightarrow> ('a dual_ord) \<Rightarrow> ('a dual_ord)" is plus . 

instance .. 
end

instantiation "dual_ord" :: (minus) minus
begin

lift_definition minus_dual_ord :: "('a dual_ord) \<Rightarrow> ('a dual_ord) \<Rightarrow> ('a dual_ord)" is minus . 

instance .. 
end

instantiation "dual_ord" :: (zero) zero
begin

lift_definition zero_dual_ord :: "('a dual_ord)" is 0 .  

instance .. 
end



typ "ennreal dual_ord"







section "showing quantitative separation connectives for ennreal with plus"



                    
thm INF_ennreal_add_const

lemma INF_ennreal_add_const_local2:
  fixes f g :: "_ \<Rightarrow> ennreal"
  shows "(INF i:A. f i + c) = (INF i:A. f i) + c"
  apply(cases  "A={}")
  subgoal by simp
  subgoal 
    using continuous_at_Inf_mono[of "\<lambda>x. x + c" "f`A"]
    using continuous_add[of "at_right (Inf (f ` A))", of "\<lambda>x. x" "\<lambda>x. c"]
    by (auto simp: mono_def) 
  done


lemma INF_ennreal_const_add':
  fixes f g :: "_ \<Rightarrow> ennreal" 
  shows "(INF i:I. c + f i) = c + (INF i:I. f i)" 
    using   INF_ennreal_add_const_local2[of f c I ] by (simp add: ac_simps) 
 



typ "ennreal dual_ord"



interpretation ENNREAL_PLUS: quant_sep_con "(+)" "0::ennreal dual_ord" "(-)"  
  apply (standard ; transfer)
  subgoal by (auto simp add: bot_ennreal minus_top_ennreal) 
  subgoal by (auto simp add: bot_ennreal minus_top_ennreal)
  subgoal by (auto simp add: bot_ennreal minus_top_ennreal)
  subgoal by (auto simp add: bot_ennreal minus_top_ennreal)
  subgoal by (auto simp add: bot_ennreal minus_top_ennreal)
  subgoal by (auto simp add: bot_ennreal minus_top_ennreal)
  subgoal by (simp add: ennreal_minus_mono)
  subgoal by (simp add: ennreal_mono_minus) 
  subgoal by (auto simp add: bot_ennreal minus_top_ennreal)
  subgoal for c A 
    using INF_ennreal_add_const_local2[where f=id and c=c] 
    by (simp add: algebra_simps)    
  subgoal  by (simp add: add_mono)
  subgoal by (metis add.commute ennreal_minus_le_iff not_le top_greatest)
  subgoal by (auto simp add: bot_ennreal minus_top_ennreal) 
  done



abbreviation star_pot_method (infixl "**\<^sub>p" 60) where
  "star_pot_method == ENNREAL_PLUS.sep_conj_q"

abbreviation wand_pot_method (infixl "-*\<^sub>p" 60) where
  "wand_pot_method == ENNREAL_PLUS.sep_impl_qq"


thm ENNREAL_PLUS.adjoint_general


(* TODO: maybe transfer back *)







subsection \<open>Experiments for an inverted order on ennreal\<close>



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


subsection  "more experiments with type classes"



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





       


end