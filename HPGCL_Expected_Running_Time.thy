\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
chapter \<open>A Calculus for the expected running time of hpGCL\<close>
theory HPGCL_Expected_Running_Time
imports QSL_For_Potentials
 HPGCL "HOL-Eisbach.Eisbach" "Differential_Game_Logic.Lib"
begin


paragraph \<open>Summary\<close>

text \<open>This theory introduces the expected running time (ERT) calculus
        for hpGCL.

      We use the ert calculus for pGCL and extend it to heap manipulating programs.

  
      This theory is experimental.\<close>



lemma propagate_star: "\<And>var val. (A \<star>\<^sub>p Q) ((fst h)(var := val), snd h) = ((\<lambda>(s,h). A (s(var := val),  h))  \<star>\<^sub>p (\<lambda>(s,h). Q (s(var := val),  h))) h"
  "\<And>var val. (A \<star>\<^sub>p Q) (x(var := val), y) = ((\<lambda>(s,h). A (s(var := val),  h))  \<star>\<^sub>p (\<lambda>(s,h). Q (s(var := val),  h))) (x,y)"
  unfolding star_pot_method_alt''
  by(auto simp add: split_beta)  


method simp_ennreal = (simp del: ennreal_half ennreal_numeral ennreal_1 
                    add: ennreal_1[symmetric]  ennreal_numeral[symmetric]
                      ennreal_minus ennreal_mult[symmetric] divide_ennreal
                          ennreal_plus[symmetric] )
thm divide_ennreal ennreal_minus 


definition pt :: "(stack \<Rightarrow> addrs) \<Rightarrow> (stack \<Rightarrow> val) \<Rightarrow> stack \<times> heap \<Rightarrow>  ennreal" 
        ("[_ \<mapsto> _]" [56,51] 56) where
  "pt e e' \<equiv> (\<lambda>(s,h). if dom (map_of_heap h) = {e s} \<and> h (e s) = TRIV (e' s) then 0 else top)"

lemma pt_emb: "pt e e' = emb\<^sub>p (ptb e e')"
  unfolding pt_def emb\<^sub>p_alt ptb_def by auto 


subsection \<open>the "allocated pointer predicate"\<close>
definition ptany :: "(stack \<Rightarrow> addrs)  \<Rightarrow> stack \<times> heap \<Rightarrow>  ennreal" 
      ("[_ \<mapsto> -]" [56] 56) where
  "ptany e \<equiv> (\<lambda>(s,h).  if   dom (map_of_heap h) = {e s}  then 0 else top)"

lemma ptany_emb: "ptany e  = emb\<^sub>p (ptanyb e )"
  unfolding ptany_def emb\<^sub>p_alt ptanyb_def  by auto

term "(P -\<star>\<^sub>p Q)"

primrec ert :: "hpgcl \<Rightarrow> (stack \<times> heap \<Rightarrow> ennreal) \<Rightarrow> stack \<times> heap \<Rightarrow> ennreal"  where
  "ert Skip X = (\<lambda>x. X x + 1)"
| "ert (Seq c1 c2) X = ert c1 (ert c2 X)" 
(* | "ert (Coin c1 p c2) X = (\<lambda>s. p * ert c1 X s + (1-p) * ert c2 X s)"  *)
| "ert (If b c1 c2) X = (\<lambda>(s,h). (if b s then ert c1 X (s,h) else ert c2 X (s,h)))"
| "ert (While b c) X = lfp (\<lambda>Y (s,h). 1 + (if b s then ert c Y (s,h) else X (s,h) ))" 
| "ert (Assign v e) X = (\<lambda>(s,h). X (s(v:=e s),h) + 1)"

| "ert (New x ve) X = (\<lambda>(s,h). Sup { (( (pt (\<lambda>_. a) ve))  -\<star>\<^sub>p (\<lambda>(s,h). X (s(x:=a),h))) (s,h) |a::int. True } + 1 )"
| "ert (Free ae) X = (\<lambda>x. ((ptany ae) \<star>\<^sub>p X) x + 1)"
| "ert (Lookup x ae) X =                             
     (\<lambda>(s,h). Inf { ((pt ae (\<lambda>_. val)) \<star>\<^sub>p ( (pt ae (\<lambda>_. val)) -\<star>\<^sub>p (\<lambda>(s,h). X (s(x:=val),h)))) (s,h)
       |val::int. True } + 1)"
| "ert (Update ae ve) X = (\<lambda>h. (ptany ae \<star>\<^sub>p (( (pt ae ve)) -\<star>\<^sub>p X)) h + 1)"





lemma sup_continuous_ert: "sup_continuous (ert P)"
  apply (induction P)
  (* apply   (auto intro!: order_continuous_intros sup_continuous_lfp''[THEN sup_continuous_applyD]
           dest: sup_continuous_compose sup_continuous_applyD) *)
  oops

 

lemma ert_If_alt: "ert (If b c1 c2) X = inf (emb\<^sub>p (\<lambda>(s,h). b s) + ert c1 X) (emb\<^sub>p (\<lambda>(s,h). \<not>b s) + ert c2 X)"
  by(auto simp add: sup_fun_def emb\<^sub>p_alt top_add  split: if_splits prod.splits)  


text \<open>sub-distributivity of \<open>\<star>\<^sub>p\<close> over inf \<close>

lemma sub_distributivity_of_star_over_inf:
  "(X \<star>\<^sub>p (inf Y Z)) \<ge> inf (X \<star>\<^sub>p Y) (X \<star>\<^sub>p Z)"
  unfolding star_pot_method_alt'
  apply(rule le_funI)
  apply auto
proof -
  fix a b 
  let ?f = "(\<lambda>(x,y). X (a, x) + Y (a, y))"
  let ?g = "(\<lambda>(x,y). X (a, x) + Z (a, y))"
  have "inf (Inf {X (a, x) + Y (a, y) |x y. b = x + y \<and> x ## y}) (Inf {X (a, x) + Z (a, y) |x y. b = x + y \<and> x ## y})
    = inf (Inf (?f `{(x,y) |x y. b = x + y \<and> x ## y})) (Inf (?g ` {(x,y) |x y. b = x + y \<and> x ## y}))"
    apply (rule arg_cong2[where f=inf]) apply(rule arg_cong[where f=Inf]) apply auto
    apply(rule arg_cong[where f=Inf]) apply auto done
  also have "\<dots> = (INF a\<in>{(x,y) |x y. b = x + y \<and> x ## y}. inf (?f a) (?g a))"
    apply(subst INF_inf_distrib) by simp
  also have "\<dots> \<le> Inf {X (a, x) + ENNREAL_PLUS.fsup Y Z (a, y) |x y. b = x + y \<and> x ## y}"
    apply(rule Inf_mono)
    apply auto
    subgoal for x y
      apply(rule exI[where x=x])
      apply(rule exI[where x=y]) apply auto 
      by (simp add: ENNREAL_PLUS.sup_times_distrib)
    done
  finally show " inf (Inf {X (a, x) + Y (a, y) |x y. b = x + y \<and> x ## y})
                   (Inf {X (a, x) + Z (a, y) |x y. b = x + y \<and> x ## y})
         \<le> Inf {X (a, x) + ENNREAL_PLUS.fsup Y Z (a, y) |x y. b = x + y \<and> x ## y}"
    .
qed
     


lemma sub_distributivity_of_star_over_inf':
  "((inf Y Z) \<star>\<^sub>p X ) \<ge> inf (Y \<star>\<^sub>p X) (Z \<star>\<^sub>p X)"
  apply(subst (3) star_pot_method_commute)    
  apply(subst (1) star_pot_method_commute)  
  apply(subst (2) star_pot_method_commute)
  apply(subst sub_distributivity_of_star_over_inf)
  by simp


lemma ert_mono:
  "f\<le>g \<Longrightarrow> ert c f \<le> ert c g"
proof (induct c arbitrary: f g)
case Skip
  then show ?case by (auto simp: le_fun_def)
next
case (Assign x1 x2)
  then show ?case by (auto simp: le_fun_def)
next
  case (Seq c1 c2)
then show ?case by (auto simp: le_fun_def)
(*next
  case (Coin c1 x2 c2)
  then show ?case 
    apply (auto simp: le_fun_def)
    apply(rule add_mono)
    subgoal apply(rule mult_left_mono) by auto
    subgoal apply(rule mult_left_mono) by auto
    done *)
next
  case (If x1 c1 c2)
  then show ?case 
    by (auto simp: le_fun_def)
next
  case (While x1 c)
  then show ?case 
    apply (auto simp:  )
    apply(rule lfp_mono) by (auto simp: le_fun_def)
next
  case (New x1 x2)
  then show ?case
    apply (auto simp: le_fun_def)
    apply (rule Sup_mono)
    apply safe
    apply auto
    subgoal for a b ab
      apply(rule exI[where x="([(\<lambda>_. ab) \<mapsto> x2] -\<star>\<^sub>p (\<lambda>(s, h). g (s(x1 := ab), h))) (a, b)"])
      apply safe apply(rule exI[where x=ab]) apply simp
      apply(rule wand_pot_method_Rmono) by auto
    done
next
  case (Free x)
  then show ?case
    by (auto simp: le_fun_def intro: star_pot_method_mono)
next
  case (Lookup x1 x2)
  then show ?case
    apply (auto simp: le_fun_def)
    apply (rule Inf_mono)
    apply safe 
    apply auto
    subgoal for a b val
      apply(rule exI[where x=" ([x2 \<mapsto> (\<lambda>_. val)] \<star>\<^sub>p [x2 \<mapsto> (\<lambda>_. val)] -\<star>\<^sub>p (\<lambda>(s, h). f (s(x1 := val), h))) (a, b)"])
      apply safe apply(rule exI[where x=val]) apply simp
      apply(rule star_pot_method_mono) apply simp
      apply(rule wand_pot_method_Rmono) by auto
    done
next
  case (Update x1 x2)
  then show ?case 
    by (auto simp: le_fun_def intro!: star_pot_method_mono  wand_pot_method_Rmono) 
qed 

lemma ert_mono':
  "f\<le>g \<Longrightarrow> ert c f x\<le> ert c g x"
  using ert_mono  
  by (simp add: le_funD)


definition chara where
  "chara b c X Y = (\<lambda>(s,h). 1 + (if b s then ert c Y (s,h) else X (s,h)))"


thm lfp_lowerbound

theorem invariant_rule:
  assumes "chara b c X I \<le> I"
  shows "ert (While b c) X \<le> I"
  using assms  by(auto intro: lfp_lowerbound simp add: chara_def) 


subsection \<open>Dollar Assertion\<close>


definition dollar where
  "dollar c = (\<lambda>(s,h). if h=0 then c else \<infinity>)"

lemma plus_as_dollar_conv: "\<And>Q a c. Q a + c = (Q \<star>\<^sub>p dollar c) a"  
  unfolding dollar_def star_pot_method_alt''
  apply auto
  apply(rule antisym)
  subgoal apply(rule Inf_greatest) apply auto  
    by (simp add: add_top)  
  subgoal for Q a b apply(rule Inf_lower)
    apply ( rule image_eqI[where x="(b,0)"]) apply simp apply simp done
  done

lemma plus_as_dollar_conv': "\<And>Q. (\<lambda>a. Q a + c) = (Q \<star>\<^sub>p dollar c)"  
  apply (rule ext) by(rule plus_as_dollar_conv)


lemma ert_New_alt: "ert (New x ve) X =
     ((\<lambda>(s,h). (SUP a\<in>UNIV.  (( (pt (\<lambda>_. a) ve))  -\<star>\<^sub>p (\<lambda>(s,h). X (s(x:=a),h))) (s,h)) ) \<star>\<^sub>p dollar 1) "
  apply simp
  apply(rule ext)  apply simp
  unfolding plus_as_dollar_conv[symmetric]
  apply simp
  apply(rule arg_cong[where f=Sup]) by auto


lemma ert_Lookup_alt: "ert (Lookup x ae) X =
     ((\<lambda>(s,h). (INF val\<in>UNIV.  ((pt ae (\<lambda>_. val)) \<star>\<^sub>p ( (pt ae (\<lambda>_. val)) -\<star>\<^sub>p (\<lambda>(s,h). X (s(x:=val),h)))) (s,h)
        )) \<star>\<^sub>p dollar 1)"
  apply simp
  apply(rule ext)  apply simp
  unfolding plus_as_dollar_conv[symmetric]
  apply simp
  apply(rule arg_cong[where f=Inf]) by auto


subsection \<open>Hoare triples\<close>


definition "Hoare_triple \<Phi> c \<Psi> \<equiv> \<Phi> \<ge> ert c \<Psi>"

lemma Hoare_tripleI[intro]: "\<Phi> \<ge> ert c \<Psi> \<Longrightarrow> Hoare_triple \<Phi> c \<Psi>"
  unfolding Hoare_triple_def .

lemma Hoare_tripleD: "Hoare_triple \<Phi> c \<Psi> \<Longrightarrow> \<Phi> \<ge> ert c \<Psi>"
  unfolding Hoare_triple_def .





subsection \<open>Quantitative Frame Rule\<close>

lemma Assign_propagates_star: "x1 \<notin> Vars \<Pi> \<Longrightarrow>
     ((\<lambda>(s, h). \<Psi> (s(x1 := x2 s), h)) \<star>\<^sub>p \<Pi>) (a, b)
      = ( \<Psi>  \<star>\<^sub>p \<Pi>) (a(x1 := x2 a), b)"
  unfolding star_pot_method_alt'
  apply simp
  apply(rule arg_cong[where f=Inf])
  apply auto
  subgoal for xa y
    apply(rule exI[where x=xa])
    apply(rule exI[where x=y])
    apply safe 
    apply(drule not_in_Vars_upd_okay[where s=a and v="x2 a" and h=y]) 
    by simp
  subgoal for xa y
    apply(rule exI[where x=xa])
    apply(rule exI[where x=y])
    apply safe 
    apply(drule not_in_Vars_upd_okay[where s=a and v="x2 a" and h=y]) 
    by simp 
  done
    
lemma quantitative_frame_rule_aux: "(Mod c1 \<union> Mod c2) \<inter> Vars \<Pi> = {}
    \<Longrightarrow> Mod c1  \<inter> Vars \<Pi> = {} \<and> Mod c2 \<inter> Vars \<Pi> = {}" by auto

lemma theorem_3_11_3': "pure\<^sub>p X \<Longrightarrow> ((X + Y) \<star>\<^sub>p Z) = (X + (Y \<star>\<^sub>p Z))"
  unfolding plus_fun_def
  using theorem_3_11_3[of X Y Z]  
  .


lemma zz: "(a::ennreal) * Inf G \<le> (INF x\<in>G. a * x)"
  apply(rule Inf_greatest)
  apply auto
  by (simp add: ENNREAL_PLUS.Sup_upper mult_left_mono)

lemma zz2: "ENNREAL_PLUS.SUPR {f (x,y) |x y. ba = x + y \<and> x ## y} g
  = ENNREAL_PLUS.SUPR {(x,y)|x y. ba = x + y \<and> x ## y} (g o f)"
  apply auto 
  apply(rule arg_cong[where f=Inf]) by auto

(*
lemma blab: "((\<lambda>s. a*F s+b*G s) \<star>\<^sub>p (\<lambda>s. a*F' s+b*G' s)) \<ge> (\<lambda>s. a*(F\<star>\<^sub>pF') s+b*(G\<star>\<^sub>pG') s)"
  unfolding star_pot_method_alt'
  apply(rule le_funI)
  apply auto
  apply(rule order.trans)
   apply(rule add_mono)
    apply(rule zz) apply(rule zz)
  supply [[unify_trace_failure]]
  apply(subst zz2)
  apply(rule order.trans)
  using ENNREAL_PLUS.SUP_times_distrib2_general
  apply(rule ENNREAL_PLUS.SUP_times_distrib2_general)
  sorry
*)


lemma qfr_aux1: "Sup ((\<lambda>x. Inf ((\<lambda>y. (f x y)::ennreal)`Y) )`X) \<le> Inf ((\<lambda>y. Sup ((\<lambda>x. f x y)`X))`Y)"
  by (simp add: ENNREAL_PLUS.SUP_least ENNREAL_PLUS.SUP_upper SUP_mono')


lemma star_pot_method_alt''':
  "(P \<star>\<^sub>p Q) = (\<lambda>(s,h). INF (x,y)\<in> { (x, y). x ## y}. if  h=x+y then P(s,x) + Q(s,y) else top )"
  unfolding star_pot_method_alt'  
  apply(rule ext)
  apply auto
  apply(rule antisym)
  subgoal
    by (smt ENNREAL_PLUS.bot_least Inf_greatest Inf_lower imageE mem_Collect_eq split_beta) 
  subgoal
    apply(rule Inf_greatest)
    apply auto apply(rule Inf_lower2)
    by auto
  done


lemma SUP_to_UNIV: "(SUP h\<in>M. f h) = (SUP h\<in>UNIV. if h\<in>M then f h else (bot::'b::complete_lattice))"  
  apply(rule antisym)
  subgoal 
    apply(rule Sup_least)
    apply(rule Sup_upper2) by auto
  subgoal    
    by (smt SUP_least Sup_upper ccSUP_empty empty_iff image_eqI) 
  done

lemma INF_to_UNIV: "(INF h\<in>M. f h) = (INF h\<in>UNIV. if h\<in>M then f h else (top::'b::complete_lattice))"  
  apply(rule antisym)
  subgoal 
    by (smt INF_greatest Inf_lower image_eqI top_greatest) 
  subgoal
    apply(rule Inf_greatest)
    apply auto apply(rule Inf_lower2)
    by auto
  done

lemma If_Inf_commute: "(if b then Inf (f`G) else bot) \<le> Inf ((\<lambda>x. (if b then (f x)::ennreal else bot))`G) "
  apply(cases b) by auto

lemma If_Sup_commute_bot: "(if b then Sup (f`G) else bot) \<le> Sup ((\<lambda>x. (if b then (f x)::ennreal else bot))`G) "
  apply(cases b) by auto
lemma If_Sup_commute_top: "(if b then Sup (f`G) else top) \<ge> Sup ((\<lambda>x. (if b then (f x)::ennreal else top))`G) "
  apply(cases b) by auto

lemma tta: "(if b then x - y else bot) \<le> (if b then x else bot) - (y::ennreal)"
  by(auto)


thm ENNREAL_PLUS.Sup_mult_right_distrib


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

thm continuous_diff
thm continuous_add

lemma "Inf (f`X) - c = Inf ((\<lambda>x. (f x::ennreal) - c)`X)"
  apply(cases  "X={}")
  subgoal by simp
  subgoal 
    oops


text \<open>
  The following lemma can also be stated using monotone functions @{term f} and  @{term g}. But then
  the continuity assumption needs to be for all cardinals, not only countable.
\<close>

lemma lfp_parallel_induct[consumes 2, case_names bot step cont]:
  assumes f: "sup_continuous f" and g: "sup_continuous g"
  assumes bot: "R bot bot"
  assumes step: "\<And>x y. R x y \<Longrightarrow> R (f x) (g y)"
  assumes cont: "\<And>X Y. (\<And>i::nat. R (X i) (Y i)) \<Longrightarrow> mono X \<Longrightarrow> mono Y \<Longrightarrow> R (SUP i. X i) (SUP i. Y i)"
  shows "R (lfp f) (lfp g)"
  unfolding f[THEN sup_continuous_lfp] g[THEN sup_continuous_lfp]
proof (rule cont)
  show "incseq (\<lambda>i. (f ^^ i) bot)" "incseq (\<lambda>i. (g ^^ i) bot)"
    by (intro mono_funpow f[THEN sup_continuous_mono] g[THEN sup_continuous_mono])+
  show "R ((f ^^ i) bot) ((g ^^ i) bot)" for i
    by (induction i) (auto intro: bot step)
qed



lemma ennreal_SUP_add_left_le:
  fixes c :: ennreal
  shows "(SUP i\<in>I. f i + c) \<le> (SUP i\<in>I. f i) + c"
  apply(cases "I={}")
   apply simp
  apply(subst ennreal_SUP_add_left) apply auto
  done

lemma INF_ennreal_add_const:
  fixes f g :: "_ \<Rightarrow> ennreal"
  shows "(INF i. f i + c) = (INF i. f i) + c"
  using continuous_at_Inf_mono[of "\<lambda>x. x + c" "f`UNIV"]
  using continuous_add[of "at_right (Inf (range f))", of "\<lambda>x. x" "\<lambda>x. c"]
  by (auto simp: mono_def image_comp)


lemma INF_ennreal_const_add'':
  fixes f  :: "_ \<Rightarrow> ennreal" 
  shows " c + Inf (f`X) = Inf ((\<lambda>x. c + f x)`X)" 
    using  INF_ennreal_const_add' by metis

abbreviation "Supl \<equiv> ENNREAL_PLUS.INFI"
abbreviation "Infl \<equiv> ENNREAL_PLUS.SUPR"


definition "pt_m ae e = ((pt ae e)\<star>\<^sub>p(emb\<^sub>p (\<lambda>_. True)))"

lemma lemmaB1: "((pt ae e) \<star>\<^sub>p ( (pt ae e) -\<star>\<^sub>p X)) = (pt_m ae e + X)"
    

  sorry

lemma pt_m_reduce: "a ## b \<Longrightarrow> pt_m x2 e (s, a + b) \<le> pt_m x2 e (s, a)"
  unfolding pt_m_def
  unfolding star_pot_method_alt'' apply auto
  apply(rule INF_mono) apply auto
  subgoal for x y
    apply(rule exI[where x=x])
    apply(rule exI[where x="y+b"])
    apply safe
    subgoal using sep_add_assoc sep_add_disjD by blast 
    subgoal using sep_disj_addI3 by auto 
    subgoal by (simp add: emb\<^sub>p_alt)
    done
  done


lemma ert_Lookup_alt': "ert (Lookup x ae) X =
     ((\<lambda>(s,h). (INF val\<in>UNIV.  (pt_m ae (\<lambda>_. val) + (\<lambda>(s,h). X (s(x:=val),h))) (s,h))) \<star>\<^sub>p dollar 1)"
  unfolding ert_Lookup_alt
  apply(subst lemmaB1)   by auto


lemma Inf_swap: "\<And>X f. Infl UNIV (\<lambda>u. Infl X (\<lambda>x. f u x)) = Infl X (\<lambda>x. Infl UNIV (\<lambda>u. f u x))"
    using ENNREAL_PLUS.SUP_commute by blast 



text \<open>Appendix B.12 in @{cite batzPOPL19}\<close>
lemma quantitative_frame_rule: 
  shows "Mod c \<inter> Vars \<Pi> = {} \<Longrightarrow> ert c (\<Psi> \<star>\<^sub>p \<Pi>) \<le> (ert c \<Psi> \<star>\<^sub>p \<Pi>)"
proof (induct c arbitrary: \<Psi>)
  case Skip
  then show ?case
    apply (simp add: plus_as_dollar_conv  ) 
    apply(subst (2) star_pot_method_commute)
    apply(subst (3) star_pot_method_commute)
    apply(subst star_pot_method_assoc[symmetric]) 
    by simp
next
  case (Assign x1 x2)
  then show ?case 
    apply (simp add: plus_as_dollar_conv  )
    apply(rule le_funI)
    apply auto
    apply(subst Assign_propagates_star) apply simp
    apply(subst (2) star_pot_method_commute)
    apply(subst (3) star_pot_method_commute)
    apply(subst star_pot_method_assoc[symmetric]) 
    by simp
next
  case (Seq c1 c2)
  then show ?case
    apply (auto intro!: ert_mono)
    apply (drule quantitative_frame_rule_aux)
    apply(rule order.trans)
     apply(rule ert_mono[where g="ert c2 \<Psi> \<star>\<^sub>p \<Pi>"])
    by simp_all
(*next
  case (Coin c1 x2 c2)


  {
    fix a b
    have "x2 * ert c1 (\<Psi> \<star>\<^sub>p \<Pi>) (a, b) + (1 - x2) * ert c2 (\<Psi> \<star>\<^sub>p \<Pi>) (a, b)
         \<le> G" sorry
    also have "\<dots> \<le> ((\<lambda>a. x2 * ert c1 \<Psi> a + (1 - x2) * ert c2 \<Psi> a) \<star>\<^sub>p \<Pi>) (a, b)"
      sorry
    also have "\<dots> \<le> ((\<lambda>a. x2 * ert c1 \<Psi> a + (1 - x2) * ert c2 \<Psi> a) \<star>\<^sub>p (x2 * \<Pi> + (1-x2) * \<Pi>)) (a, b)"
      sorry
    finally have "x2 * ert c1 (\<Psi> \<star>\<^sub>p \<Pi>) (a, b) + (1 - x2) * ert c2 (\<Psi> \<star>\<^sub>p \<Pi>) (a, b)
       \<le> ((\<lambda>a. x2 * ert c1 \<Psi> a + (1 - x2) * ert c2 \<Psi> a) \<star>\<^sub>p \<Pi>) (a, b)"
      .
  }

  from Coin show ?case
    apply (auto simp: le_fun_def) 
    using theorem_3_11_3
    apply(rule add_mono)
    sorry *)
next
  case (If x1 c1 c2)
  then show ?case
    unfolding ert_If_alt Mod.simps
    apply -
    apply (drule quantitative_frame_rule_aux)
    apply(rule order.trans[OF _ sub_distributivity_of_star_over_inf'])
    apply(subst theorem_3_11_3')
    subgoal 
      unfolding emb\<^sub>p_alt pure\<^sub>p_alt by auto
    apply(subst theorem_3_11_3')
    subgoal 
      unfolding emb\<^sub>p_alt pure\<^sub>p_alt by auto
    apply(rule inf_mono)
    subgoal 
     (* supply [[unify_trace_failure]] *)
      apply(rule le_funI)
      apply(simp only: plus_fun_def)
      apply(rule add_left_mono) by (auto simp add: le_fun_def)  
    subgoal 
     (* supply [[unify_trace_failure]] *)
      apply(rule le_funI)
      apply(simp only: plus_fun_def)
      apply(rule add_left_mono) by (auto simp add: le_fun_def)  
    done
next
  case (While x1 c)

  let ?f = "(\<lambda>Y (s, h). 1 + (if x1 s then ert c Y (s, h) else (\<Psi> \<star>\<^sub>p \<Pi>) (s, h)))"
  let ?g = "(\<lambda>Y (s, h). 1 + (if x1 s then ert c Y (s, h) else \<Psi> (s, h)))"
  have fg: "mono ?f" "mono ?g" 
    by (auto intro!: monoI ert_mono le_funI ert_mono[THEN le_funD])

  thm lfp_lockstep_induct[where f="?f"]

  show ?case
    apply clarsimp
  proof(induct rule: lfp_lockstep_induct[where f="?f" and g="?g"])
    case monof
    then show ?case using fg by simp
  next
    case monog
    then show ?case using fg by simp
  next
    case (step A B)
     
    have *: "\<And>a b. Inf {ert c B (a, x) + \<Pi> (a, y) |x y. b = x + y \<and> x ## y}
        = Inf ((\<lambda>(x,y). ert c B (a, x) + \<Pi> (a, y))`{(x,y)|x y. b = x + y \<and> x ## y})"
      apply(rule arg_cong[where f=Inf]) by auto
    have **: "\<And>a b. Inf {1+ ert c B (a, x) + \<Pi> (a, y) |x y. b = x + y \<and> x ## y}
        = Inf ((\<lambda>(x,y). 1+ ert c B (a, x) + \<Pi> (a, y))`{(x,y)|x y. b = x + y \<and> x ## y})"
      apply(rule arg_cong[where f=Inf]) by auto
    have ***: "\<And>a b. Inf {\<Psi> (a, x) + \<Pi> (a, y) |x y. b = x + y \<and> x ## y}
            = Inf ((\<lambda>(x,y). \<Psi> (a, x) + \<Pi> (a, y))`{(x,y)|x y. b = x + y \<and> x ## y})"
      apply(rule arg_cong[where f=Inf]) by auto
    have ****: "\<And>a b. Inf {1 + \<Psi> (a, x) + \<Pi> (a, y) |x y. b = x + y \<and> x ## y}
            = Inf ((\<lambda>(x,y). 1 + \<Psi> (a, x) + \<Pi> (a, y))`{(x,y)|x y. b = x + y \<and> x ## y})"
      apply(rule arg_cong[where f=Inf]) by auto
    show ?case
      apply -
      apply (rule le_funI)
      apply auto
       apply(rule order.trans)
        apply(rule add_left_mono) 
      apply(rule ert_mono')  
         apply(rule step(3))
       apply(rule order.trans)
        apply(rule add_left_mono)   
        apply(rule While(1)[THEN le_funD])
      subgoal using While(2) by auto
      subgoal unfolding star_pot_method_alt
        apply auto
        unfolding *
        apply(subst INF_ennreal_const_add'') 
        unfolding **    
        apply(rule INF_mono) by force 
      subgoal unfolding star_pot_method_alt
        apply auto
        unfolding ***
        apply(subst INF_ennreal_const_add'') 
        unfolding ****   
        apply(rule INF_mono) by force 
      done
  next
    case (union M)
    show ?case 
      unfolding fst_proj_def snd_proj_def 
      apply(rule Sup_least) apply auto
      subgoal for A B
        using union[rule_format, of "(A,B)"] apply simp
        apply(rule order.trans)
         apply(assumption)
        apply(rule le_funI)
        apply(rule star_pot_method_mono) apply(rule Sup_upper) by auto
      done
  qed
next
  case (New x1 x2)
  then have tt: "\<And>y a ma . \<Pi> (a(x1 := ma), y)  = \<Pi> (a, y)"
    by (simp add: not_in_Vars_upd_okay) 

  show ?case
    unfolding ert_New_alt
    apply(rule le_funI)  
    apply(subst (1) star_pot_method_assoc[symmetric])
    apply(subst (4) star_pot_method_commute)
    apply(subst (1) star_pot_method_assoc)
    apply(rule star_pot_method_mono[rotated]) apply simp
    apply simp
    apply(case_tac sh) apply simp
  proof -
    fix s h
    have " Supl UNIV (\<lambda>a. ([(\<lambda>_. a) \<mapsto> x2] -\<star>\<^sub>p (\<lambda>(s, h). (\<Psi> \<star>\<^sub>p \<Pi>) (s(x1 := a), h))) (s,h))
        \<le> Supl UNIV (\<lambda>x. ([(\<lambda>_. x) \<mapsto> x2] -\<star>\<^sub>p
             (\<lambda>(s, h). Infl {(x, y). h = x + y \<and> x ## y}
                               (\<lambda>(xa, y). \<Psi> (s(x1 := x), xa) + \<Pi> (s(x1 := x), y))))  (s,h))"
      unfolding star_pot_method_alt'' by simp
    also have "\<dots> \<le> Supl UNIV (\<lambda>x. ([(\<lambda>_. x) \<mapsto> x2] -\<star>\<^sub>p (\<lambda>(s, h). Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>(xa, y). \<Psi> (s(x1 := x), xa) + \<Pi> (s, y))))  (s,h))"
      apply(subst tt) by simp
    also have "\<dots> \<le>  Supl UNIV (\<lambda>x. Supl {h'. h ## h' \<and> ptb (\<lambda>_. x) x2 (s, h')}
                   (\<lambda>h'. Infl {(h1, h2). h + h' = h1 + h2 \<and> h1 ## h2} (\<lambda>(h1, h2). \<Psi> (s(x1 := x), h1) + \<Pi> (s, h2))))"
      unfolding pt_emb  wand_pot_method_emb_alt by simp
    also have "\<dots> \<le>  Supl UNIV (\<lambda>x. Supl {h'. h ## h' \<and> ptb (\<lambda>_. x) x2 (s, h')}
                       (\<lambda>h'. Infl {(h1, h2). h = h1 + h2 \<and> h1 ## h2} (\<lambda>(h1, h2). \<Psi> (s(x1 := x), h1 + h') + \<Pi> (s, h2))))"
      \<comment> \<open>choose h' \<subseteq> h1\<close>
      apply(rule SUP_mono)
      apply auto
      subgoal for x
        apply(rule exI[where x=x])
        apply(rule SUP_mono) apply auto
        subgoal for h' 
          apply(rule exI[where x="h'"]) apply auto
          apply(rule INF_mono) apply auto
          subgoal for a b apply(rule exI[where x="a + h'"])
            apply(rule exI[where x="b"]) apply auto
            subgoal
              by (metis sep_add_assoc sep_add_commute sep_add_disjD sep_add_disjI1)  
            subgoal 
              using sep_add_disjI1 by blast  
            done
          done
        done
      done
    also have "\<dots>  \<le> Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>x. case x of (x, y) \<Rightarrow> Supl UNIV (\<lambda>xa. Supl {h'. x ## h' \<and> ptb (\<lambda>_. xa) x2 (s, h')} (\<lambda>xaa. \<Psi> (s(x1 := xa), x + xaa)+ \<Pi> (s, y))) )"
      apply(rule order.trans)
       apply(rule SUP_mono') 
       apply(rule qfr_aux1)
      apply(rule order.trans) 
       apply(rule qfr_aux1)
      apply(rule INF_mono)
      subgoal for m
        apply(rule bexI[where x=m])  apply auto
        apply(rule SUP_mono) apply auto
        subgoal for x y a apply(rule exI[where x=a])
          apply(rule Sup_mono)
          apply auto
          using sep_add_disjD by blast   
        done
      done
    also have "\<dots>  \<le> Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>x. case x of (x, y) \<Rightarrow> Supl UNIV (\<lambda>xa. Supl {h'. x ## h' \<and> ptb (\<lambda>_. xa) x2 (s, h')} (\<lambda>xaa. \<Psi> (s(x1 := xa), x + xaa))) + \<Pi> (s, y))"
      apply(rule INF_mono)
      subgoal for m
        apply(rule bexI[where x=m])  
         apply auto
        apply(rule order.trans[rotated])
         apply(rule ennreal_SUP_add_left_le)    
        apply(rule SUP_mono)
        subgoal for x y u
          apply(rule bexI[where x=u])  apply auto
          apply(rule ennreal_SUP_add_left_le) done
        done
      done
   
    also have "\<dots>  \<le> Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>x. case x of (x, y) \<Rightarrow> Supl UNIV (\<lambda>a. ([(\<lambda>_. a) \<mapsto> x2] -\<star>\<^sub>p (\<lambda>(s, h). \<Psi> (s(x1 := a), h))) (s, x)) + \<Pi> (s, y))"
      unfolding pt_emb  wand_pot_method_emb_alt apply simp done
    also have "\<dots>  \<le> ((\<lambda>(s, h). Supl UNIV (\<lambda>a. ([(\<lambda>_. a) \<mapsto> x2] -\<star>\<^sub>p (\<lambda>(s, h). \<Psi> (s(x1 := a), h))) (s, h))) \<star>\<^sub>p \<Pi>)  (s,h)"
      unfolding star_pot_method_alt'' apply simp done
    finally show " Supl UNIV (\<lambda>a. ([(\<lambda>_. a) \<mapsto> x2] -\<star>\<^sub>p (\<lambda>(s, h). (\<Psi> \<star>\<^sub>p \<Pi>) (s(x1 := a), h)))  (s,h))
         \<le> ((\<lambda>(s, h). Supl UNIV (\<lambda>a. ([(\<lambda>_. a) \<mapsto> x2] -\<star>\<^sub>p (\<lambda>(s, h). \<Psi> (s(x1 := a), h))) (s, h))) \<star>\<^sub>p \<Pi>)  (s,h)"
      .
  qed
   

 
next
  case (Free x)
  then show ?case
    apply simp
    apply(rule le_funI)
    unfolding plus_as_dollar_conv' plus_as_dollar_conv
    by(auto simp: star_pot_method_commute star_pot_method_commute_c)
next
  case (Lookup x1 x2)
  then have tt: "\<And>y a ma . \<Pi> (a(x1 := ma), y)  = \<Pi> (a, y)"
    by (simp add: not_in_Vars_upd_okay) 


  show ?case
    unfolding ert_Lookup_alt'
    apply(rule le_funI) 
    apply(subst (1) star_pot_method_assoc[symmetric])
    apply(subst (4) star_pot_method_commute)
    apply(subst (1) star_pot_method_assoc)
    apply(rule star_pot_method_mono[rotated]) apply simp
    apply auto
  proof -
    fix s h
    have "Infl UNIV (\<lambda>x. pt_m x2 (\<lambda>_. x) (s, h) + (\<Psi> \<star>\<^sub>p \<Pi>) (s(x1 := x), h))
        \<le> Infl UNIV (\<lambda>x. pt_m x2 (\<lambda>_. x) (s, h) + Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>(xa, y). \<Psi> (s(x1 := x), xa) + \<Pi> (s(x1 := x), y)))"
      unfolding star_pot_method_alt'' apply simp done
    also have "\<dots> \<le>
         Infl UNIV (\<lambda>x. pt_m x2 (\<lambda>_. x) (s, h) + Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>(xa, y). \<Psi> (s(x1 := x), xa) + \<Pi> (s, y)))"
      apply(subst tt) apply simp done
    also have "\<dots> \<le> Infl UNIV (\<lambda>x. Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>(h1,h2). (pt_m x2 (\<lambda>_. x) (s, h) + (\<Psi> (s(x1 := x), h1)) + \<Pi> (s, h2))))"
      \<comment> \<open>Algebra\<close>
      apply(subst INF_ennreal_const_add'') 
      apply(simp only: split_beta) apply(rule INF_mono') apply(rule INF_mono') by auto
    also have "\<dots> \<le> Infl UNIV (\<lambda>x. Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>(h1,h2). (pt_m x2 (\<lambda>_. x) (s, h1) + (\<Psi> (s(x1 := x), h1)) + \<Pi> (s, h2))))"
      \<comment> \<open>take subset in which [pt_m] is evaluated in h1 instead of h\<close>
      apply(rule INF_mono) apply auto
      subgoal for u apply(rule exI[where x=u]) 
      apply(rule INF_mono) apply auto
        subgoal for a b 
          apply(rule exI[where x=a])
          apply(rule exI[where x=b])
          apply safe apply(rule add_right_mono)
          apply(rule add_right_mono)
          apply(rule pt_m_reduce) by simp
        done
      done
    also have "\<dots> \<le> Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>x. case x of (x, y) \<Rightarrow> Infl UNIV (\<lambda>xa. pt_m x2 (\<lambda>_. xa) (s, x) + \<Psi> (s(x1 := xa), x)) + \<Pi> (s, y))"
      apply(subst Inf_swap)
      apply(rule INF_mono') apply auto
      apply(subst INF_ennreal_add_const)
      by auto 
    also have "\<dots> \<le> ((\<lambda>(s, h). Infl UNIV (\<lambda>x. pt_m x2 (\<lambda>_. x) (s, h) + \<Psi> (s(x1 := x), h))) \<star>\<^sub>p \<Pi>)  (s, h)"
      unfolding star_pot_method_alt'' apply simp done
    finally show "Infl UNIV (\<lambda>x. pt_m x2 (\<lambda>_. x) (s, h) + (\<Psi> \<star>\<^sub>p \<Pi>) (s(x1 := x), h))
         \<le> ((\<lambda>(s, h). Infl UNIV (\<lambda>x. pt_m x2 (\<lambda>_. x) (s, h) + \<Psi> (s(x1 := x), h))) \<star>\<^sub>p \<Pi>) (s, h)"
      .
  qed
next
  case (Update x1 x2) 
  
  have *: "\<And>x. (([x1 \<mapsto> x2] -\<star>\<^sub>p \<Psi> \<star>\<^sub>p \<Pi>)) x \<le> (\<Pi> \<star>\<^sub>p ([x1 \<mapsto> x2] -\<star>\<^sub>p \<Psi>)) x"
    apply(case_tac x) apply simp
  proof -
    fix s h
    have "(([x1 \<mapsto> x2] -\<star>\<^sub>p \<Psi> \<star>\<^sub>p \<Pi>)) (s,h)
       = Supl {h'. h ## h' \<and> ptb x1 x2 (s, h')} (\<lambda>h'. (\<Psi> \<star>\<^sub>p \<Pi>) (s, h + h'))"
      unfolding pt_emb  wand_pot_method_emb_alt by simp
    also have "\<dots> = Supl {h'. h ## h' \<and> ptb x1 x2 (s, h')}
                          (\<lambda>h'. Infl {(x, y). h + h' = x + y \<and> x ## y}
                            (\<lambda>(x, y). \<Psi> (s, x) + \<Pi> (s, y)))" 
      unfolding star_pot_method_alt''  by simp

    also have "\<dots> \<le> Supl {h'. h ## h' \<and> ptb x1 x2 (s, h')}
                          (\<lambda>h'. Infl {(h1, h2). h = h1 + h2 \<and> h1 ## h2}
                            (\<lambda>(h1, h2). \<Psi> (s, h1 + h') + \<Pi> (s, h2)))" 
      \<comment> \<open>choose h' \<subseteq> h1\<close> (* the same step as in the New case, maybe factor it out? *)
      apply(rule SUP_mono)
      apply auto
      subgoal for h'
        apply(rule exI[where x=h']) apply simp
        apply(rule INF_mono) apply auto
        subgoal for a b apply(rule exI[where x="a + h'"])
          apply(rule exI[where x="b"]) apply auto
          subgoal
            by (metis sep_add_assoc sep_add_commute sep_add_disjD sep_add_disjI1)  
          subgoal 
            using sep_add_disjI1 by blast  
          done
        done
      done

    also have "\<dots> \<le> Infl {(h1, h2). h = h1 + h2 \<and> h1 ## h2} 
                          (\<lambda>x. case x of (h1, h2) \<Rightarrow> 
                                   Supl {h'. h1 ## h' \<and> ptb x1 x2 (s, h')} (\<lambda>h'. \<Psi> (s, h1 + h') + \<Pi> (s, h2)) ) " 

      apply(rule order.trans) 
       apply(rule qfr_aux1)
      apply(rule INF_mono)
      subgoal for m apply(rule bexI[where x=m])  apply auto
        apply(rule SUP_mono) apply auto
        subgoal for x y a apply(rule exI[where x=a]) apply auto  
          using sep_add_disjD by blast   
        done
      done
       
    also have "\<dots> \<le> Infl {(h1, h2). h = h1 + h2 \<and> h1 ## h2} 
                          (\<lambda>x. case x of (h1, h2) \<Rightarrow> 
                                   Supl {h'. h1 ## h' \<and> ptb x1 x2 (s, h')} (\<lambda>h'. \<Psi> (s, h1 + h')) + \<Pi> (s, h2)) "
      apply(rule INF_mono')
      apply auto
      by(rule ennreal_SUP_add_left_le)
    also have "\<dots> = Infl {(x, y). h = x + y \<and> x ## y} (\<lambda>x. case x of (x, y) \<Rightarrow> ([x1 \<mapsto> x2] -\<star>\<^sub>p \<Psi>) (s, x) + \<Pi> (s, y) )"
      unfolding pt_emb  wand_pot_method_emb_alt by simp
    also have "\<dots> = (([x1 \<mapsto> x2] -\<star>\<^sub>p \<Psi>) \<star>\<^sub>p \<Pi>) (s,h)"
      unfolding star_pot_method_alt'' by simp
    also have "\<dots> = (\<Pi> \<star>\<^sub>p ([x1 \<mapsto> x2] -\<star>\<^sub>p \<Psi>)) (s,h)"
      apply(subst star_pot_method_commute) by simp
    finally show "(([x1 \<mapsto> x2] -\<star>\<^sub>p \<Psi> \<star>\<^sub>p \<Pi>)) (s,h) \<le> (\<Pi> \<star>\<^sub>p ([x1 \<mapsto> x2] -\<star>\<^sub>p \<Psi>)) (s,h)"
      by simp
  qed
    

  show ?case
    apply simp
    apply(rule le_funI)
    unfolding plus_as_dollar_conv' plus_as_dollar_conv 
    using star_pot_method_commute_c
    apply(subst (1) star_pot_method_assoc[symmetric])
    apply(subst (2) star_pot_method_assoc[symmetric])
    apply(subst star_pot_method_assoc[symmetric])
    apply(rule star_pot_method_mono) apply simp
    apply(subst (2) star_pot_method_commute)
    apply(subst (3) star_pot_method_commute)
    apply(subst  star_pot_method_assoc[symmetric])
    apply(rule star_pot_method_mono) apply simp
    apply(rule *) done
qed



lemma Frame_rule:
  assumes "Hoare_triple \<Phi> c \<Psi>"
  and "Mod c \<inter> Vars \<Pi> = {}"
  shows "Hoare_triple (\<Phi> \<star>\<^sub>p \<Pi>) c (\<Psi> \<star>\<^sub>p \<Pi>)"
proof 
  have "ert c (\<Psi> \<star>\<^sub>p \<Pi>) \<le> ((ert c \<Psi>) \<star>\<^sub>p \<Pi>)"
    apply(rule quantitative_frame_rule)
    by fact
  also have "\<dots> \<le> (\<Phi> \<star>\<^sub>p \<Pi>)"
    apply(rule le_funI)
    apply(rule star_pot_method_mono)
    subgoal using assms(1)[THEN Hoare_tripleD] using le_fun_def by metis
    by simp
  finally show "ert c (\<Psi> \<star>\<^sub>p \<Pi>) \<le> (\<Phi> \<star>\<^sub>p \<Pi>)" .
qed
    






lemma "(X \<star>\<^sub>p (\<lambda>_. 1)) = X + (\<lambda>_. 1)"
  oops 


subsection "example"


(* for "garbage collection" *)
definition "trueheap = (\<lambda>_. 0::ennreal)"
           
term sep_true

lemma "trueheap = emb\<^sub>p (sep_true)" unfolding trueheap_def   emb\<^sub>p_alt by auto


lemma GC: "trueheap \<le> X"  unfolding trueheap_def le_fun_def by auto
lemma GC': "trueheap x \<le> X x"  unfolding trueheap_def le_fun_def by auto

lemma addd_true_heaps: "((\<lambda>_. a) \<star>\<^sub>p (\<lambda>_. b)) = (\<lambda>_. a+b)"
  apply (rule antisym)
  unfolding star_pot_method_alt
  subgoal apply(rule le_funI) apply (simp add: split_beta)
    apply(rule Inf_lower) apply auto apply(rule exI[where x=0]) 
    by(auto simp: sep_add_ac)
  subgoal apply(rule le_funI) apply (simp add: split_beta) 
    apply(rule Inf_greatest) by auto
  done


lemma adjoint_general_s'':
  "Y \<le> (X \<star>\<^sub>p Z) \<Longrightarrow> (Z -\<star>\<^sub>p Y) sh  \<le> X sh"
  using adjoint_general_s' unfolding le_fun_def by fast

 
thm adjoint_general_s[no_vars]
lemma currying: "\<And>h. (\<And>h. Y h \<le> (X \<star>\<^sub>p A) h) \<Longrightarrow>  (A -\<star>\<^sub>p Y) h \<le> X h" using adjoint_general_s by blast

lemma currying': "\<And>h. (\<And>h. Y (s,h) \<le> (X \<star>\<^sub>p A) (s,h)) \<Longrightarrow>  (A -\<star>\<^sub>p Y) (s,h) \<le> X (s,h)" using adjoint_general_s_liberal by metis
 





  

experiment 
  fixes p   p' :: int
begin



definition P where "P = Seq (Lookup ''x'' (\<lambda>_. p)) (Update (\<lambda>_. p') (\<lambda>s. s ''x''))"


thm quant_modus_ponens_general_s

thm star_pot_method_mono


lemma f2: "(a::ennreal)+1\<le>b+3 \<longleftrightarrow> a\<le>b+2" sorry
lemma f3: "(a::ennreal)+1\<le>b+2 \<longleftrightarrow> a\<le>b+1" sorry
lemma f1: "(a::ennreal)+1\<le>b+1 \<longleftrightarrow> a\<le>b" sorry
lemma f: "(a::ennreal)+1\<le>b+4 \<longleftrightarrow> a\<le>b+3" apply auto
  subgoal  
    sorry (* by (metis Groups.add_ac(2) Groups.add_ac(3) ennreal_add_left_cancel_le infinity_ennreal_def numeral.simps(2) numeral.simps(3) numeral_code(1) top.extremum)  *)
  subgoal  
    by (smt ENNREAL_PLUS.oper_left_mono ab_semigroup_add_class.add_ac(1) add.commute one_plus_numeral semiring_norm(2) semiring_norm(4))  
  done
thm  ENNREAL_PLUS.oper_left_mono
term "pt (\<lambda>_. p') ve "
lemma e: "(([(\<lambda>_. p) \<mapsto>  (\<lambda>_. v)] \<star>\<^sub>p [(\<lambda>_. p') \<mapsto>  (\<lambda>_. ve)]) x + c) \<ge> ([(\<lambda>_. p) \<mapsto>  (\<lambda>_. v)] \<star>\<^sub>p (\<lambda>y. (pt (\<lambda>_. p')  (\<lambda>_. ve) y) + c)) x"
  sorry
lemma e2: "(([(\<lambda>_. p) \<mapsto>  (\<lambda>_. v)] \<star>\<^sub>p [(\<lambda>_. p') \<mapsto>  -]) x + c) \<ge> ([(\<lambda>_. p) \<mapsto>  (\<lambda>_. v)] \<star>\<^sub>p (\<lambda>y. (ptany (\<lambda>_. p') y) + c)) x"
  sorry


lemma gg: "([(\<lambda>_. p') \<mapsto> (\<lambda>_. ve)]) sh + c = (\<lambda>sh. pt (\<lambda>_. p')  (\<lambda>_. ve)  sh + c) sh" sorry

lemma "([(\<lambda>_. p) \<mapsto> (\<lambda>_. v)] -\<star>\<^sub>p (\<lambda>(s, h). ([(\<lambda>_. p') \<mapsto> -] \<star>\<^sub>p [(\<lambda>_. p') \<mapsto> (\<lambda>s. s ''x'')] -\<star>\<^sub>p [(\<lambda>_. p) \<mapsto> (\<lambda>_. v)] \<star>\<^sub>p [(\<lambda>_. p') \<mapsto> (\<lambda>_. v)]) (s(''x'' := v), h) + 1))
      = ([(\<lambda>_. p) \<mapsto> (\<lambda>_. v)] -\<star>\<^sub>p (\<lambda>(s, h). ([(\<lambda>_. p') \<mapsto> -] \<star>\<^sub>p [(\<lambda>_. p') \<mapsto> (\<lambda>s. s ''x'')] -\<star>\<^sub>p [(\<lambda>_. p) \<mapsto> (\<lambda>_. v)] \<star>\<^sub>p [(\<lambda>_. p') \<mapsto> (\<lambda>_. v)]) (s(''x'' := v), h) + 1))"
  sorry

lemma 3: "\<And>p p'::int. ((\<lambda>a. Y a + c) \<star>\<^sub>p X) h
      = (  Y  \<star>\<^sub>p X) h + c" sorry 

term "([(\<lambda>_. p') \<mapsto> -] \<star>\<^sub>p [(\<lambda>_. p') \<mapsto> (\<lambda>s. s ''x'')] -\<star>\<^sub>p [(\<lambda>_. p) \<mapsto> (\<lambda>_. v)] \<star>\<^sub>p [(\<lambda>_. p') \<mapsto> (\<lambda>_. v)]) ((fst h)(''x'' := v), snd h)"


lemma propagate_wand: "\<And>var val. (A -\<star>\<^sub>p Q) ((fst h)(var := val), snd h) = ((\<lambda>(s,h). A (s(var := val),  h))  -\<star>\<^sub>p (\<lambda>(s,h). Q (s(var := val),  h))) h"
  unfolding wand_pot_method_alt
  by(simp add: split_beta)  

term " ((\<lambda>(s, h). ([(\<lambda>_. p') \<mapsto> (\<lambda>s. s ''x'')]) (s(''x'' := v), h)))"
lemma reduce: "\<And>p'. ([(\<lambda>_. p') \<mapsto> (\<lambda>s. s ''x'')]) (s(''x'' := v), h)
        =   ([(\<lambda>_. p') \<mapsto> (\<lambda>s. v)]) (s, h)" unfolding pt_def by auto
lemma reduce2: "\<And>p'. ([(\<lambda>_. p') \<mapsto> (\<lambda>s. c)]) (s(''x'' := v), h)
        =   ([(\<lambda>_. p') \<mapsto> (\<lambda>s. c)]) (s, h)" unfolding pt_def by auto

lemma "ert P ( (pt (\<lambda>_. p) (\<lambda>_. v)) \<star>\<^sub>p (pt (\<lambda>_. p')  (\<lambda>_. v))) x \<le> ( (pt (\<lambda>_. p)  (\<lambda>_. v)) \<star>\<^sub>p (ptany (\<lambda>_. p')  )) x + 2"
  unfolding P_def 
  apply(subst ert.simps)
  apply(subst ert.simps)
  apply(subst ert.simps) 

  apply(simp add: split_beta)

  (* pay *)
  apply(subst f3) 

  apply(rule Inf_lower2)
   apply auto
  apply(rule order.trans)
  defer apply(rule e2)
  apply(rule star_pot_method_mono) 
   apply(rule order.refl) 
  apply(rule currying)

  apply(simp add: split_beta) 
  unfolding 3 apply(subst f1)
  apply(subst (3) star_pot_method_commute)
  unfolding 3[symmetric]
  apply(subst (3) star_pot_method_commute)
                  
  apply(subst propagate_star)
  apply(rule star_pot_method_mono) 

  subgoal  unfolding ptany_def pt_def 
    by(simp add: split_beta) 

  
  apply(simp add: split_beta) (* why is currying applicable here!? *)
  apply(subst propagate_wand)
  apply(subst reduce)
  apply(rule currying)
  apply(simp add: split_beta)
  apply(subst propagate_star)
  apply(subst reduce2)
  apply(subst reduce2)

  apply(subst (1) star_pot_method_commute)
  apply(subst (2) star_pot_method_commute)

  apply(rule star_pot_method_mono) 
  apply simp
  by(simp add: split_beta)
  


lemma "ert P (trueheap) x \<le> ( (pt (\<lambda>_. p)  (\<lambda>_. v)) \<star>\<^sub>p (pt (\<lambda>_. p')  (\<lambda>_. ve))) x + 4"
  unfolding P_def 
  apply(subst ert.simps)
  apply(subst ert.simps)
  apply(subst ert.simps)  

  apply(simp add: split_beta)

  (* pay *)
  apply(subst f) 

  apply(rule Inf_lower2)
   apply auto
  apply(rule order.trans)
  defer apply(rule e)
  apply(rule star_pot_method_mono) 
   apply(rule order.refl) 
  apply(rule currying)

  apply(simp add: split_beta) 
  unfolding 3 apply(subst f2)
  apply(subst (2) star_pot_method_commute)
  unfolding 3[symmetric]
  apply(subst (2) star_pot_method_commute)
                  
  apply(subst propagate_star)
  apply(rule star_pot_method_mono) 

  subgoal  unfolding ptany_def pt_def 
    by(simp add: split_beta) 

  
  apply(simp add: split_beta) (* why is currying applicable here!? *)
  apply(subst propagate_wand)
  apply(subst reduce)
  apply(rule currying)
  apply(simp add: split_beta)
  unfolding trueheap_def by simp  


end

lemma A3: "6 * (5 / 10) = (3::ennreal)"
proof -
  have f: "6 * (5 / 10) = (3::real)" by auto
  have "6 * (5 / 10) =
      ennreal (6 * (5 / 10))" apply (subst ennreal_mult) apply simp apply simp
    apply (subst divide_ennreal[symmetric]) apply simp  apply simp
    by simp
    also have "\<dots> = ennreal 3" using f by auto
  also have "\<dots> = 3" by auto
  finally show ?thesis .
qed 
lemma A: "2 * (5 / 10) = (1::ennreal)"
proof -
  have f: "2 * (5 / 10) = (1::real)" by auto
  have "2 * (5 / 10) =
      ennreal (2 * (5 / 10))" apply (subst ennreal_mult) apply simp apply simp
    apply (subst divide_ennreal[symmetric]) apply simp  apply simp
    by simp
    also have "\<dots> = ennreal 1" using f by auto
  also have "\<dots> = 1" by auto
  finally show ?thesis .
qed 
lemma B: "(1 - 5 / 10) = (5 / 10::ennreal)"   
proof -
  have f: "(1 - 5 / 10) = (5 / 10::real)" by auto
  have "(1 - 5 / 10) =
      ennreal (1 - 5 / 10)" apply(subst ennreal_minus[symmetric])
    apply simp apply (subst divide_ennreal[symmetric]) apply simp  apply simp by simp 
  also have "\<dots> = ennreal (5 / 10)" using f by auto
  also have "\<dots> = ((5 / 10)::ennreal)"  
    by (metis ennreal_divide_numeral ennreal_numeral zero_le_numeral)   
  finally show ?thesis .
qed 


experiment 
  fixes p   p' :: int
begin

definition "P = Seq (Assign  ''x'' (\<lambda>_. 1)) 
                (While (\<lambda>s. s ''x'' = 1) (Coin (Assign  ''x'' (\<lambda>_. 0)) (0.5) (Assign  ''x'' (\<lambda>_. 1))))"


lemma f2: "(a::ennreal)+1\<le> 6 \<longleftrightarrow> a\<le> 5" sorry
lemma f3: "1+(a::ennreal)\<le> 5 \<longleftrightarrow> a\<le>4" sorry


lemma "ert P (\<lambda>_. 0) x \<le> 6"
  unfolding P_def 
  apply(subst ert.simps)
  apply(subst ert.simps(6))
  apply(simp del:  ert.simps add: split_beta)
  apply(subst f2)
  apply(rule order.trans)
   apply(rule invariant_rule[where I="\<lambda>sh. (if (fst sh) ''x'' = 1 then 5 else 1)", THEN le_funD])
  unfolding chara_def  
  subgoal apply (rule le_funI)
    apply(auto simp  add: split_beta)
    apply(subst f3)
    apply(rule order.trans)
     apply(rule add_mono)
    apply(rule order.refl)
     apply(rule order.refl)
    by(auto simp: algebra_simps A3 A B) 
  subgoal by auto 
  done
 


end





experiment 
  fixes p   p' :: int
  and bA bB :: "stack \<Rightarrow>  bool" and A B :: hpgcl
begin

definition "P = Seq (While bA A) (While bB B)"

lemma ert_mono: "(\<And>x. f x \<le> f' x) \<Longrightarrow> ert C f x \<le> ert C f' x"
  sorry


lemma assumes "G=(\<lambda>_.0)"
  shows "Q x \<ge> ert P G x"
  unfolding P_def 
  apply(subst ert.simps(2))
  apply(rule order.trans)
   apply(rule ert_mono)  
   apply(rule invariant_rule[where I=IB, THEN le_funD])
  subgoal
    unfolding chara_def 
    apply(rule le_funI)
    apply(auto simp  add: split_beta)
    subgoal (* loop B preservation *)
      sorry
    subgoal (* loop B exit *)
      sorry
    done
  subgoal (* loop B init *)
  apply(rule order.trans)
     apply(rule invariant_rule[where I=IA, THEN le_funD])
  subgoal 
    unfolding chara_def 
    apply(rule le_funI)
    apply(auto simp  add: split_beta)
    subgoal (* loop A preservation *)
      sorry
    subgoal (* loop A exit *)
      sorry
    done
  subgoal (* loop A init *) sorry
  done
  done


end

lemma propagate_pt: "pt addr v ((fst h)(var:=val),snd h) = pt (\<lambda>s. addr(s(var:=val))) (\<lambda>s. v(s(var:=val))) h" 
   "pt addr v ((x)(var:=val),y) = pt (\<lambda>s. addr(s(var:=val))) (\<lambda>s. v(s(var:=val))) (x,y)" 
unfolding pt_def by (auto  simp add: split_beta)

fun slist :: "ennreal \<Rightarrow> addrs \<Rightarrow> addrs \<Rightarrow> nat \<Rightarrow> stack \<times> heap \<Rightarrow> ennreal"  where
  "slist n p q 0 = (\<lambda>(s,h). (if p=q \<and> h=0 then 0 else \<infinity>::ennreal))"
| "slist n p r (Suc l) = Inf { (pt (\<lambda>_. p) (\<lambda>_. q)) \<star>\<^sub>p slist n q r l  |q::addrs. True }"


lemma slist_not_null: "slist c a 0 L sh < top \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> \<exists>L'. L = Suc L'"
  sorry

lemma "(X = Y)  \<Longrightarrow> (B \<star>\<^sub>p X) = (B \<star>\<^sub>p Y) " sorry


lemma slist_doesnt_care: 
  "slist n p q L (s(var := val), h) = slist n p q L (s,h)"
  apply(induct L arbitrary: p h)
   apply simp
  apply simp apply(rule INF_cong) apply simp
  apply auto apply(simp add: propagate_star)
  apply(simp add: propagate_pt)
  apply(rule antisym)
  subgoal  
    apply(rule star_pot_method_mono_more) apply(rule order.refl)
    by( simp  add: split_beta) 
  subgoal (* some preciseness reasoning *)
    sorry
  done


experiment 
  fixes p   p' :: int   and y :: addrs
begin

definition "P = Seq (Assign  ''x'' (\<lambda>_. 1)) 
                (While (\<lambda>s. s ''x'' = 1) (Coin (Assign  ''x'' (\<lambda>_. 0)) (0.5) ((New ''y'' (\<lambda>s. s ''y'')))))"


definition "P2 = Seq (Seq (Assign  ''x'' (\<lambda>_. 1))  (Assign  ''y'' (\<lambda>_. y)))
                (While (\<lambda>s. s ''x'' = 1) (Coin (Assign  ''x'' (\<lambda>_. 0)) (0.5) ((New ''y'' (\<lambda>s. s ''y'')))))"


definition "false\<^sub>p = (\<lambda>(s, h). top::ennreal)"

lemma false_star_collapse: "(A \<star>\<^sub>p false\<^sub>p) = false\<^sub>p"
  unfolding false\<^sub>p_def star_pot_method_alt'' by auto

definition pureassn\<^sub>p :: "(stack \<Rightarrow> bool) \<Rightarrow> stack \<times> heap \<Rightarrow> ennreal" where
  "pureassn\<^sub>p A = (\<lambda>(s, h). if  h = 0 \<and> A s then 0 else \<infinity>)"

lemma pureassn\<^sub>p_True_emp_conv: "pureassn\<^sub>p (\<lambda>_. True) = sep_empty\<^sub>p"
  unfolding   sep_empty\<^sub>p_alt pureassn\<^sub>p_def emb\<^sub>p_alt by auto



lemma "pure\<^sub>p (pureassn\<^sub>p A)"
  unfolding pureassn\<^sub>p_def pure\<^sub>e_alt apply auto oops

lemma "q' \<noteq> 0\<Longrightarrow> slist 0 q p L (s, b) = slist 0 q' p L (s, b) \<Longrightarrow> q = q'"
  apply(induct L arbitrary: s b q q')
   subgoal apply (auto split: if_splits) oops

lemma *: "ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y )))} (\<lambda>f. f (a, b)) + 4
    = 5/10 * (ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y )))} (\<lambda>f. f (a, b)  + 2)) +
        5/10 * (ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y )))} (\<lambda>f. f (a, b)  + 5) + 1)" sorry
lemma t: "(1 - 5 / 10) = 5/10" sorry
lemma tt: "1+b\<le>c+(5::ennreal) \<longleftrightarrow> b \<le> c + 4" sorry
lemma ll: "ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y )))} (\<lambda>x. x (a(''x'' := 0), b)) + 1 + 1
      = ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y )))} (\<lambda>x. x (a(''x'' := 0), b) + 2)"
  sorry

lemma pureassn\<^sub>p_emp: "(\<And>x. X x) \<Longrightarrow> pureassn\<^sub>p X = sep_empty\<^sub>p"
  unfolding sep_empty\<^sub>p_alt pureassn\<^sub>p_def emb\<^sub>p_def ENNREAL_PLUS.emb_def by auto

lemma propagate_pureassn: 
   " pureassn\<^sub>p A ( s(var := val) , h) 
                  =  pureassn\<^sub>p (\<lambda>s. A (s(var := val))) (s , h)"
" pureassn\<^sub>p A (f s , h)
                  =  pureassn\<^sub>p (\<lambda>s. A (f s)) (s , h)" unfolding pureassn\<^sub>p_def by auto



lemma Inf_star_commute2: 
  fixes A  :: "_ \<Rightarrow> _ \<Rightarrow> stack \<times> heap \<Rightarrow> ennreal" 
    and  B :: "stack \<times> heap \<Rightarrow> ennreal" and P
  shows 
    "(Inf { A x y | x y. P x y } \<star>\<^sub>p B) = Inf { A x y \<star>\<^sub>p B | x y. P x y }"
  unfolding star_pot_method_alt'' apply auto
  apply(rule antisym)
  subgoal 
    apply(rule Inf_greatest) apply auto apply(rule le_funI) apply auto
    apply(rule INF_mono) apply auto subgoal for xa y a aa ba
      apply(rule exI[where x=aa]) apply(rule exI[where x=ba])
      apply safe apply(rule add_right_mono) apply (rule Inf_lower) by auto
    done
  subgoal 
    apply(rule le_funI) apply auto
    apply(rule Inf_greatest) apply auto
    apply(subst INF_ennreal_add_const_local2[symmetric])
    apply(rule Inf_greatest) apply auto
    apply (rule Inf_lower2) apply auto
    apply (rule Inf_lower2) by auto
  done
lemma Inf_star_commute: 
  fixes A  :: "_ \<Rightarrow> stack \<times> heap \<Rightarrow> ennreal" 
    and  B :: "stack \<times> heap \<Rightarrow> ennreal" and P
  shows 
    "(Inf { A x | x. P x } \<star>\<^sub>p B) = Inf { A x \<star>\<^sub>p B | x. P x }"
  unfolding star_pot_method_alt'' apply auto
  apply(rule antisym)
  subgoal 
    apply(rule Inf_greatest) apply auto apply(rule le_funI) apply auto
    apply(rule INF_mono) apply auto subgoal for xa a aa ba
      apply(rule exI[where x=aa]) apply(rule exI[where x=ba])
      apply safe apply(rule add_right_mono) apply (rule Inf_lower) by auto
    done
  subgoal 
    apply(rule le_funI) apply auto
    apply(rule Inf_greatest) apply auto
    apply(subst INF_ennreal_add_const_local2[symmetric])
    apply(rule Inf_greatest) apply auto
    apply (rule Inf_lower2) apply auto
    apply (rule Inf_lower2) by auto
  done

lemma func: "\<And>A::_\<Rightarrow>_\<Rightarrow>ennreal. (\<lambda>a. Inf {A x a |x. True}) =   Inf {A x  |x. True}"
  apply auto apply(rule ext) apply auto 
  apply(rule antisym)
  subgoal  
    by (smt ENNREAL_PLUS.Sup_upper INF_greatest mem_Collect_eq)  
  subgoal apply(rule Inf_greatest) apply auto apply(rule Inf_lower) by auto   
      done
lemma funcA: "\<And>A::_\<Rightarrow>_\<Rightarrow>ennreal. (\<lambda>a. Inf {A x a |x. Pr x}) =   Inf {A x  |x. Pr x}"
  apply(rule ext) apply auto 
  apply(rule antisym)
  subgoal  
    by (smt ENNREAL_PLUS.Sup_upper INF_greatest mem_Collect_eq)  
  subgoal apply(rule Inf_greatest) apply auto apply(rule Inf_lower) by auto   
  done
lemma funcA2: "\<And>A::_\<Rightarrow>_\<Rightarrow>_\<Rightarrow>ennreal. (\<lambda>a. Inf {A y x a |x y. Pr x y}) =   Inf {A y x  |x y. Pr x y}"
  apply(rule ext) apply auto 
  apply(rule antisym)
  subgoal  
    by (smt ENNREAL_PLUS.Sup_upper INF_greatest mem_Collect_eq)  
  subgoal apply(rule Inf_greatest) apply auto apply(rule Inf_lower) by auto   
  done

lemma func2: "\<And>a A::_\<Rightarrow>_\<Rightarrow>ennreal.   Inf {A x a |x. True}  =   Inf {A x  |x. True} a"
  using func  
  by metis

lemma func2A: "\<And>a A::_\<Rightarrow>_\<Rightarrow>ennreal. Inf {A x  |x. Pr x} a = Inf {A x a |x. Pr x}"
  apply simp sorry
lemma func2B: "\<And>a A::_\<Rightarrow>_\<Rightarrow>_\<Rightarrow>ennreal. Inf {A x y  |x y. Pr x y} a = Inf {A x y a |x y. Pr x y}"
  apply simp sorry

definition boundedInf :: "('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> ennreal) \<Rightarrow> ennreal" where
  "boundedInf t R = Inf { R x | x. t x}"

lemma "boundedInf t1 (\<lambda>x. boundedInf t2 (\<lambda>y. R x y))
      = boundedInf t2 (\<lambda>y. boundedInf t2 (\<lambda>x. R x y))"
  unfolding boundedInf_def 
  apply(rule antisym)
  subgoal   sorry
  subgoal   sorry
  done


lemma assumes "G=(\<lambda>_.0)"  
  (*
    tighter postcondition:
    "G= (\<lambda>(s,h). ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p pureassn\<^sub>p (\<lambda>s. s ''y'' = y))} (\<lambda>f. f (s, h)))"
  *)
  shows "ert P2 G x \<le> (slist 0 y 0 L) x + 7"
  unfolding P2_def
  apply(simp del:  ert.simps(5) add: split_beta) 
  apply(rule order.trans)
  apply(rule add_right_mono)
   apply(rule add_right_mono)
   apply(rule invariant_rule[where I="\<lambda>sh. (Inf { slist 0 y 0 L' \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y )) |L' y. True}) sh + (if (fst sh) ''x'' = 1 then 5 else 1)", THEN le_funD])
  subgoal
    unfolding chara_def apply auto
    apply(rule le_funI) 
  apply(auto simp  add: split_beta) 
    subgoal  for s h
      apply(subst t)
      apply(subst tt)
      apply(subst *)
      apply(rule add_mono)
      subgoal
        apply(rule mult_left_mono)
        subgoal
        apply(subst ll)
        apply(rule Inf_mono) apply auto
        subgoal for L y' apply(rule exI[where x="slist 0 y' 0 L \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y' ))"])
          apply auto
          apply(subst propagate_star)
          apply(subst slist_doesnt_care)
            apply(subst propagate_pureassn) by simp
        done 
      by simp
      subgoal
        apply(rule mult_left_mono)
        apply(rule add_right_mono)
         apply(rule Sup_least) apply auto
        apply(rule currying')        
        apply(auto simp  add: split_beta)
      proof -
        fix a :: addrs
        fix h
    (*    assume a: "a\<noteq>0"  *)

        have "(\<lambda>a. ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p pureassn\<^sub>p (\<lambda>s. s ''y'' = y))} (\<lambda>x. x a))
        =  (\<lambda>a. Inf ((\<lambda>x. x a) ` { (slist 0 y 0 L' \<star>\<^sub>p pureassn\<^sub>p (\<lambda>s. s ''y'' = y)) | L' y. True}) )"
          apply(rule ext)   apply(rule arg_cong[where f=Inf]) by auto
        also have "\<dots> =(\<lambda>a. Inf ( { (slist 0 y 0 L' \<star>\<^sub>p pureassn\<^sub>p (\<lambda>s. s ''y'' = y)) a | L' y. True}) )"
          apply(rule ext) apply(rule arg_cong[where f=Inf]) by auto
        also have "\<dots> = Inf ( { (slist 0 y 0 L' \<star>\<^sub>p pureassn\<^sub>p (\<lambda>s. s ''y'' = y))   | L' y. True}) "
          apply(subst funcA2) by simp
        finally have hihi: "(\<lambda>a. ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p pureassn\<^sub>p (\<lambda>s. s ''y'' = y))} (\<lambda>x. x a))
            =  Inf ( { (slist 0 y 0 L' \<star>\<^sub>p pureassn\<^sub>p (\<lambda>s. s ''y'' = y))   | L' y. True}) " .


        have "\<And>f::_\<Rightarrow>_\<Rightarrow>('c::{complete_lattice}). Inf { Inf {f x y |x. True} |y. True} \<ge> Inf { f x y |x y. True}"
          apply simp  
          by (smt Collect_mono Inf_greatest Inf_superset_mono mem_Collect_eq)  
        (*
         have "\<And>f::_\<Rightarrow>_\<Rightarrow>('c::{complete_lattice}). Inf { Inf {f x y |x. True} |y. True} \<le> Inf { f x y |x y. True}"
          apply simp   sorry *)

        have " ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y )))} (\<lambda>x. x (s(''y'' := a), h)) + 5
            =  Inf { (slist 0 y 0 L' \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y ))) (s(''y'' := a), h) + 5 |L' y. True}"
              apply(subst plus_as_dollar_conv)
              apply(subst plus_as_dollar_conv)
          apply(subst hihi) 
          apply(subst Inf_star_commute2)
          apply(subst func2B) by simp
        also have "\<dots> =  Inf {((\<lambda>(s, h). slist 0 y 0 L' (s, h)) \<star>\<^sub>p (\<lambda>(s, h). pureassn\<^sub>p (\<lambda>s. a = y) (s, h))) (s, h) + 5 |L' y. True}"
          apply(subst propagate_star)
          apply(subst slist_doesnt_care)
          apply(subst propagate_pureassn) by simp
        also have " Inf {((\<lambda>(s, h). slist 0 y 0 L' (s, h)) \<star>\<^sub>p (\<lambda>(s, h). pureassn\<^sub>p (\<lambda>s. a = y) (s, h))) (s, h) + 5 |L' y. True}
               \<le> Inf {  slist 0 a 0 (Suc  L') (s, h) + 5 |L' . True}"
          apply(rule Inf_mono_strong)
          apply (auto simp del: slist.simps)   
          subgoal for L'  
            apply(rule exI[where x="(slist 0 a 0 (Suc L')) (s, h) + 5"])
            apply safe apply(rule exI[where x="Suc L'"]) apply(rule exI[where x="a"])
            by (simp add: pureassn\<^sub>p_emp star_pot_method_neutral) 
          done
        also   
        have "Inf {  slist 0 a 0 (Suc  L') (s, h) + 5 |L' . True} \<le> 
                Inf { (\<lambda>(s, h).([(\<lambda>_. a) \<mapsto> (\<lambda>_. q)] \<star>\<^sub>p slist 0 q 0 L') (s,h)    ) (s, h) + 5 |L' q. True}" apply simp 
          apply(rule Inf_mono) apply auto
          subgoal for L' q apply(rule exI[where x="ENNREAL_PLUS.SUPR {[(\<lambda>_. a) \<mapsto> (\<lambda>_. q)] \<star>\<^sub>p slist 0 q 0 L' |q. True} (\<lambda>f. f (s, h) ) + 5 "])
            apply safe
            subgoal 
              apply(rule exI[where x=L']) by simp
              
            subgoal 
              subgoal apply(rule add_right_mono) apply(rule Inf_lower)     by auto 
              done 
            done
          done
        also

        have pff: "\<And>Q a. ENNREAL_PLUS.SUPR {uu:: stack \<times> heap \<Rightarrow> ennreal. \<exists>L' y. uu = Q L' y} (\<lambda>x. x a + 5::ennreal)
              = Inf { (\<lambda>x. (\<lambda>(L',y). Q L' y) x a + 5::ennreal) x |x. (\<lambda>_. True) x}" apply auto
          apply(rule arg_cong[where f=Inf]) by auto  
        thm INF_ennreal_const_add' 




          term class.complete_distrib_lattice   thm complete_distrib_lattice_class.axioms        
        have " Inf { (\<lambda>(s, h).([(\<lambda>_. a) \<mapsto> (\<lambda>_. q)] \<star>\<^sub>p slist 0 q 0 L') (s,h)    ) (s, h) + 5 |L' q. True }

                 \<le>  ((\<lambda>a. ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p (pureassn\<^sub>p (\<lambda>s. s ''y''=y )))} (\<lambda>x. x a + 5)) \<star>\<^sub>p [(\<lambda>_. a) \<mapsto> (\<lambda>s. s ''y'')]) (s, h)"
          
          apply simp
          apply(subst pff)  
          apply(subst func)  
          apply(subst Inf_star_commute)
          apply(subst func2[symmetric])
          apply(rule Inf_mono) apply auto subgoal for L p
            apply(rule exI[where x="([(\<lambda>_. a) \<mapsto> (\<lambda>_. p)] \<star>\<^sub>p slist 0 p 0 L) (s, h) + 5"])
            apply safe
            subgoal apply(rule exI[where x=L])  apply(rule exI[where x=p]) by simp  
            subgoal
              apply(subst plus_as_dollar_conv) 
              apply(subst plus_as_dollar_conv')
              apply(subst (2) star_pot_method_commute)
              apply(subst (4) star_pot_method_commute)
              apply(subst (1) star_pot_method_assoc[symmetric]) 
              apply(rule star_pot_method_mono) apply simp
              apply(subst  star_pot_method_commute)
              apply(subst (1) star_pot_method_assoc[symmetric]) 
              apply(rule star_pot_method_mono) apply simp
              unfolding star_pot_method_alt''
              apply auto apply(rule Inf_greatest) apply auto unfolding pureassn\<^sub>p_def pt_def by auto
              
            done
          done 
        finally  show "ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p pureassn\<^sub>p (\<lambda>s. s ''y'' = y))} (\<lambda>x. x (s(''y'' := a), h)) + 5
           \<le> ((\<lambda>a. ENNREAL_PLUS.SUPR {uu. \<exists>L' y. uu = (slist 0 y 0 L' \<star>\<^sub>p pureassn\<^sub>p (\<lambda>s. s ''y'' = y))} (\<lambda>f. f a + 5)) \<star>\<^sub>p [(\<lambda>_. a) \<mapsto> (\<lambda>s. s ''y'')]) (s, h)"
          .
      qed
      done
    subgoal using assms by auto 
    done
  subgoal
    apply(subst func2B)
    apply(subst propagate_star)
    apply(subst propagate_star) apply simp
    apply(subst propagate_pureassn)
    apply(subst propagate_pureassn)
      apply(subst slist_doesnt_care)
      apply(subst slist_doesnt_care) apply simp
    apply(rule order.trans)
    apply(rule add_right_mono)
    apply(rule order.trans)
      apply(rule add_right_mono) 
    apply(rule order.trans)
       apply(rule add_right_mono)
         
       apply(rule Inf_lower2[where u="slist 0 y 0 L x"]) apply simp
    subgoal apply(rule exI[where x=L]) apply(rule exI[where x=y]) apply simp
      by(simp add: star_pot_method_neutral pureassn\<^sub>p_True_emp_conv)
    by auto
  done
  


lemma f2: "(a::ennreal)+1\<le> b+6 \<longleftrightarrow> a\<le> b+5" sorry
lemma f32: "1+(a::ennreal)\<le> b+5 \<longleftrightarrow> a\<le> b+4" sorry
thm propagate_star
lemma propagate_trueheap:
    "trueheap ((fst h)(var:=val),snd h) = trueheap h"
    "trueheap (x(var:=val),y) = trueheap (x,y)"
  unfolding trueheap_def by auto

(*
lemma propagate_ptany: "ptany addr ((fst h)(var:=val),snd h) = ptany (\<lambda>s. addr(s(var:=val))) h"
    "ptany addr (x(var:=val),y) = ptany (\<lambda>s. addr(s(var:=val))) (x,y)" 
  unfolding ptany_def by (auto  simp add: split_beta)
*)

lemma u: "\<And>x aa c X. (X \<star>\<^sub>p trueheap) x + c = (X \<star>\<^sub>p (\<lambda>sh. trueheap sh +  c)) x"
  sorry

lemma trueheap_absorb: "(trueheap \<star>\<^sub>p trueheap) = trueheap" 
  unfolding star_pot_method_alt''
  apply(rule antisym)
  subgoal apply(rule le_funI) apply auto
    unfolding trueheap_def  subgoal for s h
    apply(rule Inf_lower2)
       apply(rule image_eqI[where x="(h,0)"]) apply simp
      apply simp by simp 
  done
  subgoal unfolding trueheap_def apply(rule le_funI) by auto
  done
lemma I: "5 / 10 * ((trueheap \<star>\<^sub>p trueheap) (a, b) + 5 + 1) = ((1/2) * (trueheap \<star>\<^sub>p trueheap) (a, b)) + 3" sorry
lemma II: "5 / 10 * (([(\<lambda>s. s ''y'') \<mapsto> -] \<star>\<^sub>p trueheap) (a, b) + 1 + 1) = ( (1/2) * ([(\<lambda>s. s ''y'') \<mapsto> -] \<star>\<^sub>p trueheap) (a, b)) + 1" sorry

lemma kl: "1+(b::ennreal) \<le> 4+c \<longleftrightarrow> b \<le> 3+c"
  sorry
lemma zz: "1/2 * (a+a) = (a::ennreal)" sorry


lemma ert_mono: "(\<And>x. f x \<le> f' x) \<Longrightarrow> ert C f x \<le> ert C f' x"
  sorry

lemma assumes "G=(\<lambda>_.0)"
  shows "ert P G x \<le> ([(\<lambda>s. s ''y'') \<mapsto> -] \<star>\<^sub>p trueheap) x + 6"
  unfolding P_def 
  apply(subst ert.simps(2))
  apply(rule order.trans)
   apply(rule ert_mono)  
   apply(rule invariant_rule[where I=I, THEN le_funD])
  subgoal
    unfolding chara_def 
    apply(rule le_funI)
    apply(auto simp  add: split_beta)
    subgoal (* loop preservation *)
      sorry
    subgoal (* loop exit *)
      sorry
    done
  subgoal (* loop init *)
    apply(auto simp  add: split_beta) sorry
  done


text \<open>The theory is broken from here.\<close>
\<^cancel>\<open>

lemma assumes "G=(\<lambda>_.0)"
  shows "ert P G x \<le> ([(\<lambda>s. s ''y'') \<mapsto> -] \<star>\<^sub>p trueheap) x + 6"
  unfolding P_def 
  apply(simp del:  ert.simps(5) add: split_beta) 
  apply(rule order.trans)
  apply(rule add_right_mono)
   apply(rule invariant_rule[where I="\<lambda>sh. ((ptany (\<lambda>s. s ''y'')) \<star>\<^sub>p trueheap) sh + (if (fst sh) ''x'' = 1 then 5 else 1)", THEN le_funD])
  unfolding chara_def  
  subgoal apply (rule le_funI)
    apply(auto simp  add: split_beta)
     apply(subst f32)
     apply(rule order.trans)
      apply(rule add_mono)
       apply(rule mult_left_mono)
        apply(subst propagate_star)
        apply(subst propagate_trueheap)
        apply(subst propagate_ptany) apply simp
        apply(rule order.refl) apply simp
      apply(subst B)
      apply(rule mult_left_mono)
       apply(rule add_right_mono)
       apply(rule Sup_least) apply safe
       apply(rule currying')
       apply(simp  add: split_beta)
       apply (simp add: propagate_star propagate_trueheap propagate_ptany u)
       apply(subst (2) star_pot_method_commute)
       apply(rule star_pot_method_mono) 
    subgoal unfolding pt_def ptany_def 
      by(auto simp  add: split_beta)
       apply(rule order.refl) apply simp
     apply(subst (3) trueheap_absorb[symmetric])
     apply(subst I)
     apply(subst II)
     apply(auto simp: algebra_simps)
     apply(subst kl)
     apply(rule add_left_mono)
    subgoal 
      apply(rule order.trans[where b="1/2 * (([(\<lambda>s. s ''y'') \<mapsto> -] \<star>\<^sub>p trueheap) _)+ 1/2*(([(\<lambda>s. s ''y'') \<mapsto> -] \<star>\<^sub>p trueheap) _)"])
       defer  apply(subst (12) zz[symmetric]) apply(simp add: ring_distribs(1)) apply(rule order.refl)
      apply(rule add_mono) apply(rule mult_left_mono) apply(rule star_pot_method_mono)
      subgoal unfolding trueheap_def by auto apply simp apply simp apply simp
      done
    subgoal (* exit the loop *)
      using assms by auto
    done
  subgoal apply simp
    apply(subst propagate_star) 
    apply(subst propagate_trueheap)
    apply(subst propagate_ptany)
    by simp
  done
 

lemma pff: "b\<ge>a \<Longrightarrow> a + B \<le> C + (b::ennreal) \<longleftrightarrow>  B \<le> C + (b-a)"
  by (smt add.left_commute add_diff_inverse_ennreal diff_eq_0_iff_ennreal ennreal_add_left_cancel_le ennreal_minus_eq_top minus_top_ennreal not_le)

 

lemma "((5-1/2)::real) = 9/2"
  apply simp oops
lemma "((5-1)::nat) = 4"
  apply simp oops
lemma "((5-1)::ennreal) = 4"
  apply (simp del: ennreal_numeral ennreal_1 add: ennreal_1[symmetric]  ennreal_numeral[symmetric] ennreal_minus) oops
lemma "((5-1)::ennreal) = 4"
  by simp_ennreal
lemma "((5-1)::ennreal) \<le> 100"
  by simp_ennreal
lemma "3+a \<le> b+(4::ennreal) \<longleftrightarrow> a\<le>b+1"
  apply  (simp del: ennreal_numeral ennreal_1 add: ennreal_1[symmetric]  ennreal_numeral[symmetric]   )
  sorry
lemma "((5-2)::ereal) = 3"
  apply simp oops
lemma "((13-2)::ereal) = 11"
  apply simp oops
lemma "((5-1)::enat) = 4"
  apply simp oops 


lemma "x\<ge>0 \<Longrightarrow> ennreal x + 1 = ennreal (x+1)"
    sorry 

  thm numeral_eq_ereal  

lemma "numeral x \<ge> (0::real)"  
  by simp  
lemma numeral_eq_ennreal:  "numeral w = ennreal (numeral w)"
  apply (induct w rule: num_induct)
  apply (simp only: numeral_One  ennreal_1 )
  by (simp)  

lemma divide_le_ennreal: "b \<noteq> 0 \<Longrightarrow> b < top \<Longrightarrow> a / b \<le> c \<longleftrightarrow> a \<le> (c * b :: ennreal)"
  apply (cases a; cases b; cases c)
         apply  (auto simp: divide_ennreal ennreal_mult[symmetric] ennreal_less_iff field_simps ennreal_top_mult ennreal_top_divide)
  subgoal  
    using ennreal_neq_top neq_top_trans by blast  
  subgoal  
    using ennreal_neq_top neq_top_trans by blast  
  done

lemma assumes "G=(\<lambda>_.0)"
  shows "ert P G x \<le> ([(\<lambda>s. s ''y'') \<mapsto> -] \<star>\<^sub>p trueheap) x + 6"
  unfolding P_def 
  apply(subst ert.simps)
  apply(subst ert.simps(6))
  apply(simp del:  ert.simps add: split_beta)
  apply(subst f2)
  apply(rule order.trans)
   apply(rule invariant_rule[where I="\<lambda>sh. (trueheap) sh + (if (fst sh) ''x'' = 1 then 5 else 1)", THEN le_funD])
  unfolding chara_def  
  subgoal apply (rule le_funI)
    apply(auto simp  add: split_beta)
    subgoal
      apply(subst f32)
      apply(rule order.trans)
       apply(rule add_mono)
        apply(rule mult_left_mono) 
         apply(subst propagate_trueheap) 
         apply(rule order.refl) apply simp
       apply(subst B)
       apply(rule mult_left_mono)
        apply(rule add_right_mono)
        apply(rule Sup_least) apply safe
        apply(rule currying')
        apply(simp  add: split_beta)
        apply (simp add: propagate_star propagate_trueheap propagate_ptany ) 

        apply(subst trueheap_absorb[symmetric])
        apply(simp add: u)
        apply(subst (1) star_pot_method_commute) 
        apply(rule star_pot_method_mono) apply(rule order.refl) 
      subgoal unfolding     trueheap_def
        by(auto simp  add: split_beta)
       apply simp  
      apply(auto simp: algebra_simps) 
      apply(subst pff) apply simp_ennreal 
      apply(subst pff) apply simp_ennreal
         apply simp_ennreal 
      apply(subst pff)  apply simp_ennreal
      apply simp_ennreal
      apply(subst ring_distribs(1)[symmetric])
         apply simp_ennreal by simp    
    subgoal (* exit the loop *)
      using assms by auto
    done
  subgoal apply simp 
    apply(subst propagate_trueheap)
    unfolding trueheap_def 
    by simp
  done


end


experiment
begin

definition P where "P = Seq (New ''a'' (\<lambda>_. 1)) (Skip)"


lemma f: "1+l\<le>2 \<longleftrightarrow> l\<le>(1::ennreal)"
  apply rule 
  subgoal by (metis ennreal_add_left_cancel_le infinity_ennreal_def one_add_one top.extremum)  
  subgoal by (metis ennreal_add_left_cancel_le one_add_one)
  done

lemma "ert P (\<lambda>_. 0) x \<le> 2"
  unfolding P_def 
  apply(subst ert.simps)
  apply(subst ert.simps)
  apply(subst ert.simps) 
  apply (auto simp: algebra_simps)
  apply(subst f) apply(rule Sup_least) apply auto
  apply(subst wand_pot_method_alt') apply auto
  apply(cases x) apply auto
  apply(rule SUP_least) by simp  
 
lemma "(Sup A) x = Sup ((\<lambda>a. a x) ` A)"
  by simp

lemma pp: "(\<lambda>x. (Sup A) x) = (\<lambda>x. Sup ((\<lambda>a. a x) ` A))"
  by simp
 
lemma "(\<lambda>(s,h). if empb (s,h) then 2::ennreal else \<infinity>) \<ge> (\<lambda>_. 2)"
  apply (rule le_funI) by auto 

lemma "ert P (\<lambda>_. 0)  \<le> (\<lambda>_. 2)"
  unfolding P_def 
  apply(subst ert.simps)
  apply(subst ert.simps)
  apply(subst ert.simps)
  apply(rule le_funI)
  apply(simp add: split_beta)
  apply (auto simp: algebra_simps)
  apply(subst f) apply(rule Sup_least)
  apply auto  
  apply(rule adjoint_general_s'')

  apply auto
  apply(rule le_funI)
  apply(rule order.trans)
   defer apply(rule star_pot_method_mono[where B="(\<lambda>_.1)"]) apply simp oops (*
    defer 
      apply(rule GC'[where X="emb\<^sub>p (ptb (\<lambda>_. _) (\<lambda>_. 1))"])
   defer  apply simp 
  unfolding trueheap_def 
  apply(subst addd_true_heaps) by auto  *)
   

end


experiment
begin

definition P where "P = Seq (New ''a'' (\<lambda>_. 1)) (Coin Skip (0.5) (Lookup ''b'' (\<lambda>s. s ''a'')))"


lemma f: "1+l\<le>2 \<longleftrightarrow> l\<le>(1::ennreal)"
  apply rule 
  subgoal by (metis ennreal_add_left_cancel_le infinity_ennreal_def one_add_one top.extremum)  
  subgoal by (metis ennreal_add_left_cancel_le one_add_one)
  done


lemma "ert P (\<lambda>_. 0) x \<le> 2"
  unfolding P_def 
  apply(subst ert.simps)
  apply(subst ert.simps)
  apply(subst ert.simps)
  apply(subst ert.simps)
  apply(subst ert.simps) 
  apply(simp add: split_beta)
  apply (auto simp: algebra_simps)
  apply(subst f) apply(rule Sup_least)
  apply auto
  apply(rule order.trans)
  apply(rule wand_pot_method_Rmono) 
   apply(simp add: split_beta)
  apply(rule add_left_mono)
  apply(rule add_left_mono)
   apply(rule mult_left_mono) 
    apply(rule Inf_mono[where B="{uu. \<exists>val. uu = ((\<lambda>(s, h). 0)) ((fst _)(''a'' := _), snd _)}"]) 
  apply simp


  thm quant_modus_ponens_general_s



  apply(rule adjoint_general_s'')
  apply(simp add: split_beta)
  apply auto oops

\<close>

end