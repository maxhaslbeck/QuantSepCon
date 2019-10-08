theory QSL
imports
  "Expectations"
  "Sep_Heap_Instance"
begin

section \<open>Heap-predicates and quantities\<close>

subsection \<open>the "empty-heap predicate"\<close>

definition emp :: "stack \<times> heap \<Rightarrow> ennreal" ("[emp]") where
  "emp \<equiv> (\<lambda>(s,h). if dom (map_of_heap h) = {} then 1 else 0)"

lemma emp_emb: "emp = emb\<^sub>e (empb)"
  unfolding emp_def emb\<^sub>e_def empb_def by auto 

subsection \<open>the "points-to predicate"\<close>

definition pt :: "(stack \<Rightarrow> addrs) \<Rightarrow> (stack \<Rightarrow> val) \<Rightarrow> stack \<times> heap \<Rightarrow>  ennreal" 
        ("[_ \<mapsto> _]" [56,51] 56) where
  "pt e e' \<equiv> (\<lambda>(s,h). if dom (map_of_heap h) = {e s} \<and> h (e s) = TRIV (e' s) then 1 else 0)"

lemma pt_emb: "pt e e' = emb\<^sub>e (ptb e e')"
  unfolding pt_def emb\<^sub>e_def ptb_def by auto 

definition pts :: "(stack \<Rightarrow> addrs) \<Rightarrow> ((stack \<Rightarrow> val) list) \<Rightarrow> stack \<times> heap \<Rightarrow>  ennreal"
        ("[_ \<mapsto> _]" [56,51] 56)  where
  "pts e es' \<equiv> (\<lambda>(s,h). if dom (map_of_heap h) = {e s..e s + length es'} \<and> (\<forall>x<length es'. h (e s + x) = TRIV ((es' ! x) s))
                         then 1 else 0)"

lemma pts_emb: "pts e es  = emb\<^sub>e (ptsb e es)"
  unfolding pts_def emb\<^sub>e_def ptsb_def by auto 

subsection \<open>the "allocated pointer predicate"\<close>
definition ptany :: "(stack \<Rightarrow> addrs)  \<Rightarrow> stack \<times> heap \<Rightarrow>  ennreal" 
      ("[_ \<mapsto> -]" [56] 56) where
  "ptany e \<equiv> (\<lambda>(s,h).  if   dom (map_of_heap h) = {e s}  then 1 else 0)"

lemma ptany_emb: "ptany e  = emb\<^sub>e (ptanyb e )"
  unfolding ptany_def emb\<^sub>e_def ptanyb_def by auto 


subsection \<open>the "contains-pointer predicates"\<close>
definition ptt ("[_ \<hookrightarrow> _]" [56,51] 56) where
    "ptt ae ve \<equiv> ((pt ae ve) \<star>\<^sub>e (\<lambda>_. 1))" 

definition ptts ("[_ \<hookrightarrow> _]" [56,51] 56) where
    "ptts ae ve \<equiv> ((pts ae ve) \<star>\<^sub>e (\<lambda>_. 1))" 

definition pttany ("[_ \<hookrightarrow> -]" [56] 56) where
    "pttany ae ve \<equiv> ((ptany ae) \<star>\<^sub>e (\<lambda>_. 1))" 


subsection \<open>"heap-size quantity"\<close>

definition size :: "(stack \<times> heap) \<Rightarrow> ennreal"  where
  "size \<equiv> (\<lambda>(s,h). ennreal (card (dom (map_of_heap h))) )"


section "examples"

text \<open>We would like to write @{term \<open>[2\<mapsto>1]\<close>} for the heap containing value 1
  at adress 2, using the "points-to assertion". The arguments of it are functions
  @{typ \<open>stack \<Rightarrow> val\<close>}. Thus we have to write the following verbose thing:\<close>

term "[(\<lambda>_. 1)\<hookrightarrow>(\<lambda>_. 2)]"

text \<open>Using variables looks like this:\<close>

text \<open>at the adress ''a'', the value is ''b''+1, where a and b are evaluated in
  the current stack.\<close>
term "[(\<lambda>s. s ''a'')\<hookrightarrow>(\<lambda>s. s ''b'' + 1)]"


(* TODO: introduce fancy syntax that surpresses the lambda ?! *) 

lemma assumes "h= heap_of_map [1 \<mapsto> 2, 2 \<mapsto> 3, 4 \<mapsto> 5]"
  shows 
    "( [(\<lambda>_. 1)\<mapsto>(\<lambda>_. 2)] \<star>\<^sub>e size ) (s,h) = size (s,h) - 1"
  (* ... *)
    
    "( [(\<lambda>_. 1)\<mapsto>(\<lambda>_. 2)] -\<star>\<^sub>e size ) (s,h) = \<infinity>"
    "( [(\<lambda>_. 3)\<mapsto>(\<lambda>_. 4)] -\<star>\<^sub>e ([(\<lambda>_. 3)\<mapsto>(\<lambda>_. 4)] -\<star>\<^sub>e size) ) (s,h) = \<infinity>"  
  sorry




end