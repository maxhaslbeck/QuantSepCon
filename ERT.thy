theory ERT
imports PotentialMethod
 Sep_Heap_Instance hpGCL
begin

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
| "ert (Coin c1 p c2) X = (\<lambda>s. p * ert c1 X s + (1-p) * ert c2 X s)"  
| "ert (If b c1 c2) X = (\<lambda>(s,h). (if b s then ert c1 X (s,h) else ert c2 X (s,h)))"
| "ert (While b c) X = lfp (\<lambda>Y (s,h). 1 + (if b s then ert c Y (s,h) else X (s,h) ))" 
| "ert (Assign v e) X = (\<lambda>(s,h). X (s(v:=e s),h) + 1)"

| "ert (New x ve) X = (\<lambda>(s,h). Sup { (( (pt (\<lambda>_. a) ve))  -\<star>\<^sub>p (\<lambda>(s,h). X (s(x:=a),h))) (s,h) |a::int. a\<noteq>0 } + 1 )"
| "ert (Free ae) X = (\<lambda>x. ((ptany ae) \<star>\<^sub>p X) x + 1)"
| "ert (Lookup x ae) X =                             
     (\<lambda>(s,h). Inf { ((pt ae (\<lambda>_. val)) \<star>\<^sub>p ( (pt ae (\<lambda>_. val)) -\<star>\<^sub>p (\<lambda>(s,h). X (s(x:=val),h)))) (s,h)
       |val::int. True } + 1)"
| "ert (Update ae ve) X = (\<lambda>h. (ptany ae \<star>\<^sub>p (( (pt ae ve)) -\<star>\<^sub>p X)) h + 1)"





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
   defer apply(rule star_pot_method_mono[where B="(\<lambda>_.1)"])
    defer 
      apply(rule GC'[where X="emb\<^sub>p (ptb (\<lambda>_. _) (\<lambda>_. 1))"])
   defer  apply simp 
  unfolding trueheap_def 
  apply(subst addd_true_heaps) by auto 
   

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



end