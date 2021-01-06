\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
chapter \<open>The heap-manipulating probabilistic guarded command language\<close>
theory HPGCL
  imports 
    "Sep_Heap_Instance"
begin


paragraph \<open>Summary\<close>

text \<open>This theory introduces the  heap-manipulating probabilistic guarded command language (hpGCL)
      from the Paper by Batz et al @{cite batzPOPL19}.\<close>





subsection "hpGCL"

datatype hpgcl =   Skip 
                 | Assign vars "stack \<Rightarrow> val"
                 | Seq (left: "hpgcl") (right: "hpgcl") ("_;;/ _"  [60, 61] 60)
            (*     | Coin (left: "hpgcl") ennreal (right: " hpgcl") *)
                 | If "stack \<Rightarrow> bool" (left: "hpgcl") (right: "hpgcl")
                 | While "stack \<Rightarrow> bool" "hpgcl" ("(WHILE _/ DO _)"  [0, 61] 61)
                 | New vars "(stack \<Rightarrow> val) " (* list *)
                 | Free "(stack \<Rightarrow> addrs) " 
                 | Lookup vars "(stack \<Rightarrow> addrs) " 
                 | Update "(stack \<Rightarrow> addrs)" "(stack \<Rightarrow> val)"




subsubsection "Modifies and Vars"

fun Mod where
  "Mod Skip = {}"
| "Mod (Free _) = {}"
| "Mod (Update _ _) = {}"

| "Mod (Assign v ve) = {v}"
| "Mod (New v ve) = {v}"
| "Mod (Lookup v ae) = {v}"

| "Mod (Seq c1 c2) = Mod c1 \<union> Mod c2"
(* | "Mod (Coin c1 _ c2) = Mod c1 \<union> Mod c2" *)
| "Mod (If _ c1 c2) = Mod c1 \<union> Mod c2"
| "Mod (While _ c) = Mod c"

term Vars

definition "Vars P = {x. \<exists>s::stack. \<exists>h::heap. \<exists>v v'::int. P (s(x:=v),h) \<noteq> P (s(x:=v'),h) }"


lemma not_in_Vars_upd_okay: "x \<notin> Vars P \<Longrightarrow> P (s(x:=v),h) = P (s,h)"
  unfolding Vars_def  
  by (smt CollectI fun_upd_triv)


end