theory Probabilities
imports QuantSepConState
begin



section "Unit interval"

typedef unitinterval = "{x :: ereal. 0 \<le> x \<and> x \<le> 1}"
  morphisms UI2real real2UI'
  by auto


definition "real2UI x = real2UI' (max 0 (min x 1))"
                           
lemma unitinterval_range: "real2UI ` {0..1} = UNIV"
proof -
  have "\<exists>y\<in>{0..1}. x = real2UI y" for x
    by (cases x)  (auto simp: real2UI_def max_absorb2 min_absorb1)
  then show ?thesis
    by (auto simp: image_iff Bex_def)
qed

lemma type_definition_unitinterval': "type_definition UI2real real2UI {x. 0 \<le> x \<and> x \<le> 1}"
  using type_definition_unitinterval
  by (auto simp: type_definition_def real2UI_def max_absorb2 min_absorb1)

setup_lifting type_definition_unitinterval'

declare [[coercion real2UI]]

instantiation unitinterval :: complete_linorder
begin

lift_definition top_unitinterval :: unitinterval is 1 by simp
lift_definition bot_unitinterval :: unitinterval is 0 by simp
lift_definition sup_unitinterval :: "unitinterval \<Rightarrow> unitinterval \<Rightarrow> unitinterval" is sup by (auto simp: max_def)
lift_definition inf_unitinterval :: "unitinterval \<Rightarrow> unitinterval \<Rightarrow> unitinterval" is inf by (auto simp: min_def)

lift_definition Inf_unitinterval :: "unitinterval set \<Rightarrow> unitinterval" is "inf 1 \<circ> Inf"
  by (auto intro: Inf_greatest)  

lift_definition Sup_unitinterval :: "unitinterval set \<Rightarrow> unitinterval" is "sup 0 \<circ> Sup"
  by (auto intro: Sup_least) 

lift_definition less_eq_unitinterval :: "unitinterval \<Rightarrow> unitinterval \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_unitinterval :: "unitinterval \<Rightarrow> unitinterval \<Rightarrow> bool" is "(<)" .

instance
  apply ( standard ; transfer)
  by ( auto simp: le_Inf_iff min_def Inf_lower Inf_greatest Sup_upper Sup_least le_max_iff_disj max.absorb1)+
 
end
 
lift_definition one_unitinterval :: unitinterval is 1 by simp
lift_definition zero_unitinterval :: unitinterval is 0 by simp 


instantiation unitinterval :: times
begin
lift_definition times_unitinterval :: "unitinterval \<Rightarrow> unitinterval \<Rightarrow> unitinterval"   is "(*)"
    apply auto  
  by (metis ereal_mult_left_mono mult.right_neutral order_trans) 

instance ..
end
 
lift_definition divide_unitinterval :: "unitinterval \<Rightarrow> unitinterval \<Rightarrow> unitinterval" (infixl "'/\<^sub>u" 70) is "\<lambda>a b. min (a / b) (1)"
  by auto    

lemma mm: "c \<ge> 0 \<Longrightarrow> c \<le> 1 \<Longrightarrow> c * max a b = max (c*a) (c*(b::ereal))"
  unfolding max_def apply auto 
  subgoal  
    by (simp add: ereal_mult_left_mono) 
  subgoal  
    by (simp add: antisym ereal_mult_left_mono) 
  done


lemma "\<not> c < (b::ereal) \<longleftrightarrow> b \<le> c" using not_less by blast
definition "divv a (b::ereal) = min 1 (a / b)"
lemma divv_alt: "divv a b = min  (a / b) 1"
  apply(simp add: divv_def min_def) by auto
lemma fixes a b c :: ereal
  assumes A: "0 \<le> a" "a \<le> 1"   "0 \<le> b" "b \<le> 1"   "0 \<le> c" "c \<le> 1"
    and B1: "(0 < b \<or> 0 < c )" and B2: "(b< 1 \<or> c < 1)"
  shows unitinterval_adjoint: "(a \<le>divv b c) \<longleftrightarrow> a * c \<le> b"
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






section "Use the unit interval to model probabilities"


interpretation PROB: quant_sep_con  Inf Sup inf "(\<le>)" "(<)" sup top bot "(*)"   "one_unitinterval"   "divide_unitinterval"
  apply (standard; transfer)
  subgoal by (auto simp: algebra_simps min_absorb1 divide_ereal_def) 
  subgoal by (auto simp: algebra_simps min_absorb1 divide_ereal_def) 
  subgoal by (auto simp: algebra_simps min_absorb1 divide_ereal_def) 
  subgoal by (auto simp: algebra_simps min_absorb1 divide_ereal_def) 
  subgoal by (metis mult_1 divv_def eq_iff ereal_0_less_1 min.cobounded2
                    min.commute unitinterval_adjoint zero_less_one_ereal)  
  subgoal by (auto simp: algebra_simps min_absorb1 divide_ereal_def)  
  subgoal  
    by (metis divide_ereal_def eq_iff ereal_mult_right_mono ereal_zero_le_0_iff min.mono zero_le_divide_ereal)  
  subgoal  
    by (metis divide_ereal_def ereal_inverse_antimono ereal_mult_left_mono min.mono order_refl)  
  subgoal by (auto simp: algebra_simps min_absorb1 divide_ereal_def) 
  subgoal for c A apply(simp add: mm)
    apply(cases "A={}") 
    subgoal apply auto by (metis ereal_mult_zero max_bot2 mm)  
    subgoal apply(subst SUP_ereal_mult_left[where f=id, simplified]) by auto
    done   
  subgoal apply(rule order.trans) apply(rule ereal_mult_left_mono)
    prefer 3 apply(rule ereal_mult_right_mono) by auto 
  subgoal  
    apply(rule unitinterval_adjoint[unfolded divv_alt]) by auto 
  subgoal by (auto simp: algebra_simps min_absorb1 divide_ereal_def) 
  done



definition star_prob (infixl "**\<^sub>w" 60) where "star_prob == PROB.sep_conj_q"
definition wand_prob (infixl "-*\<^sub>w" 60) where "wand_prob == PROB.sep_impl_qq"



lemma times_fun': "f * g = (\<lambda>h. f h * g h)"
  apply(rule ext) by simp


subsubsection \<open>Star and Magic Wand with State\<close>


definition sep_conj_us (infixr "\<star>\<^sub>u" 35) where "sep_conj_us == PROB.sep_conj_s_q"
definition sep_impl_us (infixr "-\<star>\<^sub>u" 35) where "sep_impl_us == PROB.sep_impl_s_q"
definition "sep_empty_s\<^sub>u \<equiv> PROB.sep_empty_s_q" 
definition "emb\<^sub>u \<equiv> PROB.emb" 

lemma sep_conj_us_alt:
  fixes P :: "(_ \<times> 'a::{sep_algebra} \<Rightarrow> unitinterval)"
  shows "(P \<star>\<^sub>u Q) = (\<lambda>(s,h). Sup { P(s,x) * Q(s,y) | x y. h=x+y \<and> x ## y})"
  by (simp add: PROB.sep_conj_s_q_def PROB.sep_conj_q_def sep_conj_us_def)

term sep_impl_us

lemma sep_impl_us_alt:
  "(P -\<star>\<^sub>u Q) = (\<lambda>(s,h). INF h': { h'. h ## h' \<and> (bot < P(s,h') \<or> bot < Q(s,h+h') )
                                \<and> ( P(s,h') < top \<or> Q(s,h+h') < top)}. 
                                   Q (s,h + h') /\<^sub>u P (s,h') )"
  by (simp add: PROB.sep_impl_qq_def PROB.sep_impl_s_q_def  sep_impl_us_def)

lemma sep_empty_s\<^sub>u_alt: "sep_empty_s\<^sub>u = (\<lambda>(s, y). emb\<^sub>u (\<lambda>h. h = 0) y)"
  by (auto simp: PROB.sep_empty_s_q_def PROB.sep_empty_q_def emb\<^sub>u_def sep_empty_s\<^sub>u_def )

lemmas sep_conj_es_commute =  PROB.sep_conj_s_q_commute[folded sep_conj_us_def]
lemmas sep_conj_es_neutral = PROB.sep_conj_s_q_neutral[folded sep_conj_us_def sep_empty_s\<^sub>u_def]
lemmas sep_conj_es_assoc = PROB.sep_conj_s_q_assoc[folded sep_conj_us_def]
lemmas sep_conj_es_left_commute_s = PROB.sep_conj_q_left_commute_s[folded sep_conj_us_def]

lemmas sep_conj_es_c = PROB.sep_conj_q_s_c[folded sep_conj_us_def]


lemma theorem_3_6_s:
  fixes P Q R :: "(_ \<times> 'a::{sep_algebra} \<Rightarrow> unitinterval)"
  shows 
  "(P \<star>\<^sub>u sup Q R) = (\<lambda>s. sup ((P \<star>\<^sub>u Q) s) ((P \<star>\<^sub>u R) s))"
  (*  "(P \<star> (\<lambda>s. Q s + R s)) \<le> (\<lambda>s. (P \<star> Q) s + (P \<star> R) s)" *)
  "( (emb\<^sub>u \<phi>) \<star>\<^sub>u (Q * R)) \<le> ((emb\<^sub>u \<phi>) \<star>\<^sub>u Q) * ((emb\<^sub>u \<phi>) \<star>\<^sub>u R)"
  subgoal using PROB.theorem_3_6_s(1)[folded sep_conj_us_def]
    unfolding sup_fun_def .
  subgoal
    apply(subst (1) times_fun')    
    using PROB.theorem_3_6_s(2)[folded sep_conj_us_def emb\<^sub>u_def]
     by (auto simp: le_fun_def)
  done

lemmas sep_conj_es_mono = PROB.sep_impl_s_q_mono[folded sep_impl_us_def emb\<^sub>u_def] 

lemma adjoint_general_s:
  shows "(X \<star>\<^sub>u P) \<le> Y \<longleftrightarrow> X \<le> (P -\<star>\<^sub>u Y)" 
  using PROB.adjoint_general_s[folded sep_impl_us_def sep_conj_us_def emb\<^sub>u_def] 
  unfolding le_fun_def by blast


lemma quant_modus_ponens_general_s:
  shows "( P \<star>\<^sub>u (P -\<star>\<^sub>u X)) \<le> X"
  using PROB.quant_modus_ponens_general_s [folded sep_impl_us_def sep_conj_us_def emb\<^sub>u_def] 
  unfolding le_fun_def by blast


definition "pure\<^sub>u \<equiv> PROB.pure_q"

lemma pure\<^sub>u_alt: "pure\<^sub>u X \<longleftrightarrow> (\<forall>s h1 h2. X (s,h1) = X (s,h2))"
  using PROB.pure_q_def unfolding pure\<^sub>u_def .

lemma  theorem_3_11_1: "pure\<^sub>u X \<Longrightarrow> X * Y \<le> (X \<star>\<^sub>u Y)"
    apply(subst (1) times_fun')   
  using PROB.theorem_3_11_1[folded sep_impl_us_def sep_conj_us_def emb\<^sub>u_def pure\<^sub>u_def] 
  unfolding le_fun_def by blast

lemma theorem_3_11_3:
  "pure\<^sub>u X \<Longrightarrow> ((X * Y) \<star>\<^sub>u Z) = X * (Y \<star>\<^sub>u Z)"
    apply(subst times_fun')+
  using PROB.theorem_3_11_3[folded sep_impl_us_def sep_conj_us_def emb\<^sub>u_def pure\<^sub>u_def] 
  unfolding le_fun_def by blast 




end