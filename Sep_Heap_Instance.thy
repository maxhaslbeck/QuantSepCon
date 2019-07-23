theory Sep_Heap_Instance
imports Misc
begin



type_synonym vars = string
type_synonym val = int
type_synonym stack = "vars \<Rightarrow> val"


type_synonym addrs = int

text \<open>Instead of @{typ \<open>'a option\<close>} we use @{typ "'a tsa_opt"}, as it is defined in
    Sep_Algebra_Add, as int should not be interpreted as typ which is a 
  separation_algebra.  \<close>
type_synonym heap = "addrs \<Rightarrow> int tsa_opt"


subsection "basic expectations"
 
text \<open>conversion from a heap to a map from addresses to values\<close>
definition map_of_heap :: "heap \<Rightarrow> addrs \<Rightarrow> val option"  where
  "map_of_heap h a = (case h a of ZERO \<Rightarrow> None | TRIV a \<Rightarrow> Some a)"

definition heap_of_map :: "(addrs \<Rightarrow> val option) \<Rightarrow> heap"  where
  "heap_of_map h a = (case h a of None \<Rightarrow> ZERO | Some a \<Rightarrow> TRIV a)"

text \<open>points to assertion (as a boolean!)\<close>
definition ptb :: "(stack \<Rightarrow> addrs) \<Rightarrow> (stack \<Rightarrow> val) \<Rightarrow> stack \<times> heap \<Rightarrow>  bool" where
  "ptb e e' \<equiv> (\<lambda>(s,h). dom (map_of_heap h) = {e s} \<and> h (e s) = TRIV (e' s)  )"

text \<open>points to list assertion (as boolean!)\<close>
definition ptsb :: "(stack \<Rightarrow> addrs) \<Rightarrow> ((stack \<Rightarrow> val) list) \<Rightarrow> stack \<times> heap \<Rightarrow>  bool" where
  "ptsb e es' \<equiv> (\<lambda>(s,h). if dom (map_of_heap h) = {e s..e s + length es'} \<and> (\<forall>x<length es'. h (e s + x) = TRIV ((es' ! x) s))
                         then True else False)"

text \<open>points-to any\<close>


definition ptanyb :: "(stack \<Rightarrow> addrs)  \<Rightarrow> stack \<times> heap \<Rightarrow>  bool" where
  "ptanyb e \<equiv> (\<lambda>(s,h). dom (map_of_heap h) = {e s})"

lemma 
  "ptanyb e = (\<lambda>(s,h). \<exists>v. dom (map_of_heap h) = {e s} \<and> h (e s) = TRIV v)"
  unfolding ptanyb_def map_of_heap_def apply(rule ext) apply auto 
  by (metis domIff singletonI tsa_opt.collapse tsa_opt.simps(4))  

text \<open>empty assertion\<close>
definition empb :: "stack \<times> heap \<Rightarrow> bool" where
  "empb \<equiv> (\<lambda>(s,h). dom (map_of_heap h) = {} )"



end