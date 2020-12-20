theory NewDomain          
imports QuantSepCon "../NREST/NREST"
 begin



 term mm2

fun eo_plus :: "enat option \<Rightarrow> enat option \<Rightarrow> enat option" where
  "eo_plus None _ = None"
| "eo_plus _ None = None"
| "eo_plus (Some a) (Some b) = Some (a+b)"

lemma eo_plus_comm: "eo_plus a b = eo_plus b a"
  apply(cases a; cases b) apply auto done

lemma "mm2 (Some (a+enat b)) (Some (enat b)) = Some a"
  unfolding mm2_def 
  apply simp  
  by (metis add.commute add_diff_cancel_enat enat.distinct(2))

lemma "(a<\<infinity>\<or>b<\<infinity>) \<Longrightarrow>
  mm2 (Some (a+b)) (Some (b)) = Some a"
  unfolding mm2_def 
  apply simp   
  oops



lemma GC: "(A \<le> mm2 B C) \<longleftrightarrow> eo_plus C A \<le> B"
  apply(cases C)
  subgoal unfolding mm2_def  by simp
  subgoal for c apply(cases c)
    subgoal unfolding mm2_def apply simp
      apply(cases A; cases B) apply auto
      subgoal  
        using le_less_trans by fastforce  
      subgoal  
        by (simp add: enat_plus_minus_aux2)  
      subgoal  
        by (simp add: enat_plus_minus_aux1)  
      done
    subgoal unfolding mm2_def
      apply(cases A) apply simp apply simp
      apply(cases B) apply simp apply simp done
    done
  done 

lemma f_GC_antimono:
  fixes x y :: "(enat option)"
    and f :: "_ \<Rightarrow> _ \<Rightarrow> (enat option)"
  assumes GC: "(\<And>A B C. (A \<le> f B C) = (g C A \<le> B))"
     and *: "x \<le> y"
   shows "f q x \<ge> f q y"
  oops  

lemma f_GC_mono:
  fixes x y :: "('b::{order})"
    and f :: "_ \<Rightarrow> _ \<Rightarrow> ('a::{order})"
  assumes GC: "(\<And>A B C. (A \<le> f B C) = (g C A \<le> B))"
     and *: "x \<le> y"
  shows "f x q \<le> f y q"
  apply(subst GC)
  apply(rule order.trans) 
   apply(subst GC[symmetric])
   defer apply (rule *)  by simp  

 


lemma mm2_mono: " x \<le> y \<Longrightarrow> mm2 x q \<le> mm2 y q"
  using GC
      by (metis order.trans order_mono_setup.refl) 

lemma mm2_mono_miraculous: "x \<le> y \<Longrightarrow> mm2 x q \<le> mm2 y q"
  apply(subst GC)
  apply(rule order.trans) 
   apply(subst GC[symmetric])
  defer apply simp by simp 



lemma mm2_mono': "x \<le> y \<Longrightarrow> mm2 x q \<le> mm2 y q"
  unfolding mm2_def apply(cases q) apply (auto split: option.splits)
  using le_some_optE apply blast apply(rule helper) by auto
 



lemma mm_continous: "mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x = Inf {u. \<exists>y. u = mm (f y) m x}" 
  apply(rule antisym)
  subgoal apply(rule Inf_greatest) apply clarsimp
  proof (cases "Inf {u. \<exists>y. u = f y x}")
    case None
    have f: "m x \<noteq> None \<Longrightarrow> mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x = None" unfolding mm_def None apply(cases "m x") by (auto ) 
    then show "\<And>y. mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x \<le> mm (f y) m x"
      apply(cases "m x") apply(auto simp: f) unfolding mm_def by auto
  next
    case (Some l)
    then show "\<And>y. mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x \<le> mm (f y) m x"
      apply(cases "m x") subgoal unfolding mm_def by auto
    proof -
      fix y a assume I: "Inf {u. \<exists>y. u = f y x} = Some l" " m x = Some a"
      from I have i: "\<And>y. f y x \<ge> Some l"
        by (metis (mono_tags, lifting) Inf_lower mem_Collect_eq) 
      show "mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x \<le> mm (f y) m x"
        apply(rule mm_mono) unfolding I apply(rule i) .
    qed 
  qed
  subgoal   apply(rule Inf_lower) apply clarsimp 
  proof -
    have "\<exists>y. Inf {u. \<exists>y. u = f y x} = f y x"
      unfolding Inf_option_def apply auto unfolding Inf_enat_def apply auto
      apply (metis (mono_tags) empty_iff in_these_eq mem_Collect_eq option.exhaust)
      by (smt LeastI in_these_eq mem_Collect_eq)
    then obtain y where z: "Inf {u. \<exists>y. u = f y x} = f y x" by blast
    show "\<exists>y. mm (\<lambda>x. Inf {u. \<exists>y. u = f y x}) m x = mm (f y) m x"
      apply(rule exI[where x=y]) unfolding mm_def z ..
  qed
  done



lemma enat_plus_Sup_distrib:
  "A\<noteq>{} \<Longrightarrow> (a::enat) + Sup A = Sup ((+) a ` A)"
  apply(cases a)
  subgoal 
  unfolding Sup_enat_def apply auto
   apply (metis Max.hom_commute empty_iff enat_add_left_cancel_le max_def plus_enat_simps(2))
  apply(subst (asm) finite_image_iff)
  subgoal unfolding inj_on_def by auto
  subgoal apply simp done
  done
  subgoal by simp
  done


lemma eo_plus_Sup_distrib:
  "eo_plus (c::enat option) (Sup A) = Sup (eo_plus c ` A)"
proof (cases c)
  case None
  then show ?thesis apply auto  
    by (metis SUP_bot_conv(2) Sup_empty empty_Sup) 
next
  case (Some a)
  then show ?thesis
  proof (cases "A = {} \<or> A = {None} ")
    case True
    then show ?thesis 
      unfolding Sup_option_def  apply(cases c) by auto
  next
    case False
    then have *: "A\<noteq>{}" "A \<noteq> {None}" by auto
    have 2: "A\<subseteq>UNIV" by auto 
    have 3: "\<exists>x. Some x \<in> A"
      using *  2 unfolding UNIV_option_conv by blast
    then have "\<exists>x. Some x \<in> eo_plus c ` A"
      using Some apply auto
      subgoal for x apply(rule exI[where x="a+x"])
        apply(rule image_eqI[where x="Some x"]) by auto
      done
    then have nn: "eo_plus c ` A \<noteq> {None}" by auto
    from * have ne: "eo_plus c ` A \<noteq> {}" by simp
    from 3 have "Option.these A \<noteq>{}"
      unfolding Option.these_def by auto

    have k: "Option.these (eo_plus (Some a) ` A)
            = ((+) a) ` (Option.these A)"
      apply rule 
      subgoal apply rule
        subgoal   for x
          unfolding Option.these_def apply clarsimp
          subgoal for xa
            apply(cases xa)
             apply simp 
            subgoal for v
              apply(rule image_eqI[where x=v]) apply simp
              apply(rule image_eqI[where x="Some v"]) by auto
            done
          done
        done
      subgoal apply rule
        subgoal   for x
          unfolding Option.these_def
          apply clarsimp
          subgoal for v  
            apply(rule image_eqI[where x="eo_plus (Some a) (Some v)"])
             apply simp
            by force 
          done
        done
      done 

    show ?thesis
      unfolding Sup_option_def 
      using * nn ne Some apply simp 
      unfolding k
      by (simp add: \<open>Option.these A \<noteq> {}\<close> enat_plus_Sup_distrib)
  qed
qed



lemma mm2_continous: "mm2 (Inf A) m = Inf ((\<lambda>x. mm2 x m) ` A)"
  using eo_plus_Sup_distrib GC 
  using dual_order.trans order_mono_setup.refl
  sorry


interpretation ENOPT_PLUS:
 quant_sep_con_one Inf Sup inf "(\<le>)" "(<)" sup top bot "eo_plus" "mm2" "(Some 0)::(enat option)" 
  unfolding quant_sep_con_def quant_sep_con_one_def comm_quantale_def apply safe
  subgoal by standard
  subgoal apply standard
    subgoal for a b c by (cases a; cases b; cases c) auto
    subgoal for a b by (cases a; cases b) auto
    subgoal for a apply(cases a) by auto  
    done
  subgoal apply standard
    apply(subst eo_plus_Sup_distrib) by simp
  subgoal apply standard
    subgoal by auto
    subgoal  by(simp add: mm2_mono)
    subgoal by (simp add: mm2_antimono)  
    subgoal apply(subst GC)  apply(subst eo_plus_comm) ..
    subgoal unfolding bot_option_def by simp  
    done
  subgoal apply standard apply (auto simp: bot_option_def top_option_def top_enat_def)
    oops


end