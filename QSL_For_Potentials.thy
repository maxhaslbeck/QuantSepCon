\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
theory QSL_For_Potentials
imports Assertions_With_State
begin


paragraph \<open>Summary\<close>

text \<open>This theory instantiates the Quantitative Separation Logic language with the
        quantale for potentials (ennreal,>=,+,-).

    \<close>


section "showing quantitative separating connectives for ennreal with plus"

lemma INF_ennreal_add_const_local2:
  fixes f g :: "_ \<Rightarrow> ennreal"
  shows "(INF i\<in>A. f i + c) = (INF i\<in>A. f i) + c"
  apply(cases  "A={}")
  subgoal by simp
  subgoal 
    using continuous_at_Inf_mono[of "\<lambda>x. x + c" "f`A"]
    using continuous_add[of "at_right (Inf (f ` A))", of "\<lambda>x. x" "\<lambda>x. c"]
    by (auto simp: image_comp mono_def) 
  done


lemma INF_ennreal_const_add':
  fixes f g :: "_ \<Rightarrow> ennreal" 
  shows "(INF i\<in>I. c + f i) = c + (INF i\<in>I. f i)" 
    using   INF_ennreal_add_const_local2[of f c I ] by (simp add: ac_simps) 
 

interpretation ENNREAL_PLUS: quant_sep_con_one Sup Inf sup "(\<ge>)" "(>)" inf bot top "(+)" "(-)" "0::ennreal" 
  unfolding quant_sep_con_def quant_sep_con_one_def comm_quantale_def apply safe
  subgoal using dual_complete_lattice .
  subgoal by standard    
  subgoal apply standard
    apply(subst INF_ennreal_const_add') by simp
  subgoal apply standard
    subgoal by auto
    subgoal by (simp add: ennreal_minus_mono)  
    subgoal by (simp add: ennreal_mono_minus)  
    subgoal by (metis add.commute ennreal_minus_le_iff top.not_eq_extremum)  
    subgoal by simp  
    done
  subgoal apply standard by (auto simp: bot_ennreal)
  done 

definition star_pot_method (infixr "\<star>\<^sub>p" 35) where 
  "star_pot_method = ENNREAL_PLUS.sep_conj_s_q" 
 
lemma star_pot_method_alt':
  "star_pot_method = 
    (\<lambda>P Q a. case a of (s, h) \<Rightarrow> Inf {P (s, x) + Q (s, y) |x y. h = x + y \<and> x ## y})"
  unfolding star_pot_method_def ENNREAL_PLUS.sep_conj_s_q_def ENNREAL_PLUS.sep_conj_q_def  
  by (auto )


lemma star_pot_method_alt:
  "(P \<star>\<^sub>p Q) = (\<lambda>(s,h). Inf { P(s,x) + Q(s,y) | x y. h=x+y \<and> x ## y})"
  unfolding star_pot_method_alt' by simp

lemma star_pot_method_alt'':
  "(P \<star>\<^sub>p Q) = (\<lambda>(s,h). INF (x,y)\<in> { (x, y). h=x+y \<and> x ## y}. P(s,x) + Q(s,y) )"
  unfolding star_pot_method_alt'  
  by (metis (no_types) ENNREAL_PLUS.sep_conj_q_alt ENNREAL_PLUS.sep_conj_q_def)  

 
definition wand_pot_method (infixr "-\<star>\<^sub>p" 35) where
  "wand_pot_method = ENNREAL_PLUS.sep_impl_s_q" 
  

lemma wand_pot_method_alt': 
  "(-\<star>\<^sub>p) = (\<lambda>P Q a. case a of (s, h) \<Rightarrow> SUP h'\<in>{h'. h ## h' \<and> (P (s, h') < top \<or> Q (s, h + h') < top) \<and> (bot < P (s, h') \<or> bot < Q (s, h + h'))}. Q (s, h + h') - P (s, h'))"
  unfolding wand_pot_method_def ENNREAL_PLUS.sep_impl_s_q_def ENNREAL_PLUS.sep_impl_qq_def
  by auto    

lemma wand_pot_method_alt:
  "(P -\<star>\<^sub>p Q) = (\<lambda>(s,h). SUP h'\<in> { h'. h ## h' \<and> (bot < P(s,h') \<or> bot < Q(s,h+h') )
                                \<and> ( P(s,h') < top \<or> Q(s,h+h') < top)}. 
                                    (Q (s,h + h')) - P (s,h') )"
  unfolding wand_pot_method_alt'    by(force intro: SUP_cong)





definition "emb\<^sub>p \<equiv> (ENNREAL_PLUS.emb)" 

lemma emb\<^sub>p_alt:"emb\<^sub>p = (\<lambda>P h. if P h then 0 else top)" 
  by (force simp: emb\<^sub>p_def ENNREAL_PLUS.emb_def  )
   
lemma emb\<^sub>p_alt2: "emb\<^sub>p = (\<lambda>P sh. (if P sh then 0 else \<infinity>))"
  unfolding emb\<^sub>p_def ENNREAL_PLUS.emb_def apply transfer 
  unfolding infinity_ennreal_def
  by (auto  )  

lemma grr: "(\<lambda>h. emb\<^sub>p P (s, h)) = emb\<^sub>p (\<lambda>h. P (s, h))" 
  unfolding emb\<^sub>p_alt by auto

lemma wand_pot_method_emb_alt:
  "((emb\<^sub>p P) -\<star>\<^sub>p Q) = (\<lambda>(s, h). SUP h'\<in>{h'. h ## h' \<and> P (s, h')}. Q (s, h + h'))"
  unfolding wand_pot_method_def 
  unfolding ENNREAL_PLUS.sep_impl_s_q_def
  unfolding grr 
  unfolding emb\<^sub>p_def 
  apply(subst ENNREAL_PLUS.sep_impl_q_alt_general'') .. 

definition "sep_empty\<^sub>p \<equiv> ENNREAL_PLUS.sep_empty_s_q"


lemma sep_empty\<^sub>p_alt: "sep_empty\<^sub>p = (\<lambda>(s, h). emb\<^sub>p (\<lambda>h. h = 0) h)"
  by (auto simp: sep_empty\<^sub>p_def emb\<^sub>p_def ENNREAL_PLUS.sep_empty_s_q_def
                    ENNREAL_PLUS.sep_empty_q_def  )




definition "pure\<^sub>p \<equiv> ENNREAL_PLUS.pure_q"

lemma wrap: "\<forall>s h1 h2. to_dual_ord (X (s, h1)) = to_dual_ord (X (s, h2))
    \<Longrightarrow> \<forall>s h1 h2. of_dual_ord (to_dual_ord (X (s, h1))) = of_dual_ord (to_dual_ord (X (s, h2)))"
  by metis

lemma pure\<^sub>e_alt: "pure\<^sub>p X \<longleftrightarrow> (\<forall>s h1 h2. X (s,h1) = X (s,h2))"
  unfolding pure\<^sub>p_def ENNREAL_PLUS.pure_q_def by auto 
     
 
 

lemmas star_pot_method_commute = ENNREAL_PLUS.sep_conj_s_q_commute[folded star_pot_method_def] 
lemmas star_pot_method_neutral =  ENNREAL_PLUS.sep_conj_s_q_neutral [folded star_pot_method_def sep_empty\<^sub>p_def] 
  
lemmas star_pot_method_assoc = ENNREAL_PLUS.sep_conj_s_q_assoc[folded star_pot_method_def]  
lemmas star_pot_method_commute_c = ENNREAL_PLUS.sep_conj_q_left_commute_s[folded star_pot_method_def]  


lemma fixes P :: "_ * ('a:: sep_algebra) \<Rightarrow> ennreal"
  shows  theorem_3_6_s_1: "(P \<star>\<^sub>p inf Q R) = inf (P \<star>\<^sub>p Q) (P \<star>\<^sub>p R)" 
  unfolding inf_fun_def 
  using ENNREAL_PLUS.theorem_3_6_s(1)[folded star_pot_method_def, where P=P and Q=Q and R=R  ]
  by simp
    
 
lemmas star_pot_method_mono = ENNREAL_PLUS.sep_conj_s_q_mono[folded star_pot_method_def]
lemmas star_pot_method_mono_more = ENNREAL_PLUS.sep_conj_s_q_mono_more[folded star_pot_method_def]

lemmas theorem_3_6_s_2 = ENNREAL_PLUS.theorem_3_6_s(2)[folded star_pot_method_def emb\<^sub>p_def]  

 
 
lemmas wand_pot_method_mono = ENNREAL_PLUS.sep_impl_s_q_mono[folded wand_pot_method_def sep_empty\<^sub>p_def] 

lemmas wand_pot_method_Rmono = ENNREAL_PLUS.sep_impl_s_q_Rmono[folded wand_pot_method_def sep_empty\<^sub>p_def] 



lemmas adjoint_general_s = ENNREAL_PLUS.adjoint_general_s[folded wand_pot_method_def star_pot_method_def]
lemmas adjoint_general_s_liberal = ENNREAL_PLUS.adjoint_general_s_liberal[folded wand_pot_method_def star_pot_method_def] 
lemma adjoint_general_s':
  "Y \<le> (X \<star>\<^sub>p P) \<longleftrightarrow> (P -\<star>\<^sub>p Y)  \<le> X"
  using adjoint_general_s[of Y X P] unfolding le_fun_def by auto


lemmas quant_modus_ponens_general_s = ENNREAL_PLUS.quant_modus_ponens_general_s[folded wand_pot_method_def star_pot_method_def]  



lemma plus_fun': "f + g = (\<lambda>h. f h + g h)"
  apply(rule ext) by simp

lemmas theorem_3_11_1 = ENNREAL_PLUS.theorem_3_11_1[folded pure\<^sub>p_def  star_pot_method_def] 

lemmas theorem_3_11_3 = ENNREAL_PLUS.theorem_3_11_3[folded pure\<^sub>p_def star_pot_method_def] 
 


subsection \<open>Experiments for an inverted order on ennreal\<close>



class divide_right_mono = inverse + order + 
  assumes divide_right_mono_general: "\<And>a b c::'a. a \<le> b \<Longrightarrow> a / c \<le> b / c" 

class SUP_mult_left = complete_lattice + times +
  assumes SUP_mult_left: "c * (SUP i\<in>I. f i) = (SUP i\<in>I. c * f i :: 'a)"
begin

lemma   SUP_mult_right: "(SUP i\<in>I. f i) * c = (SUP i\<in>I. f i * c :: 'a)"
  oops

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
  subgoal for c f I apply(cases c) by (simp add: image_comp thee_times INF_ennreal_const_add')   
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


lemma SUP_times_distrib: "(SUP xA. f x * g x::ennreal) \<le> (SUP xA. f x) * (SUP xA. g x)"
      by (simp add: SUP_least SUP_upper mult_mono)

lemma SUP_times_distrib2: "(SUP (x,y)A. f x y * g x y::ennreal) \<le> (SUP (x, y)A. f x y) * (SUP (x, y)A. g x y)" 
  apply(rule Sup_least) apply auto 
  apply(rule mult_mono) apply(auto simp: image_image SUP_image intro:  SUP_upper)
  subgoal by (metis ENNREAL_PLUS.INF_lower UNIV_I old.prod.case)
  subgoal
    by (metis ENNREAL_PLUS.INF_lower UNIV_I old.prod.case) 
  done

lemma SUP_times_distrib2_general:
  fixes g :: "_\<Rightarrow>_\<Rightarrow>'b::{complete_lattice,ordered_semiring, nonnegative}"
  shows "(SUP (x,y)A. f x y * g x y) \<le> (SUP (x, y)A. f x y) * (SUP (x, y)A. g x y)" 
  apply(rule SUP_least)
  apply auto apply(rule mult_mono)
     apply (auto intro: SUP_upper2 simp: SUP_image zero_smallest) 
  subgoal by (metis SUP_upper UNIV_I prod.simps(2))
  subgoal by (metis SUP_le_iff UNIV_I case_prod_conv order_refl) 
  done




       


end