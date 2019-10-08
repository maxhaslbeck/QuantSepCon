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

| "ert (New x ve) X = (\<lambda>(s,h). Sup { ((emb\<^sub>p (ptb (\<lambda>_. a) ve))  -\<star>\<^sub>p (\<lambda>(s,h). X (s(x:=a),h))) (s,h) |a::int. a\<noteq>0 } + 1 )"
| "ert (Free ae) X = (\<lambda>x. ((ptany ae) \<star>\<^sub>p X) x + 1)"
| "ert (Lookup x ae) X =                             
     (\<lambda>(s,h). Inf { ((pt ae (\<lambda>_. val)) \<star>\<^sub>p (emb\<^sub>p (ptb ae (\<lambda>_. val)) -\<star>\<^sub>p (\<lambda>(s,h). X (s(x:=val),h)))) (s,h)
       |val::int. True } + 1)"
| "ert (Update ae ve) X = (\<lambda>h. (ptany ae \<star>\<^sub>p ((emb\<^sub>p (ptb ae ve)) -\<star>\<^sub>p X)) h + 1)"





subsection "example"

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





end


end