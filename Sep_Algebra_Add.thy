\<^marker>\<open>creator "Peter Lammich"\<close>
\<^marker>\<open>contributor "Maximilian P. L. Haslbeck"\<close>
chapter \<open>Misc Theory for Separation Algebra\<close>
theory Sep_Algebra_Add
imports "Separation_Algebra.Sep_Tactics"
begin

paragraph \<open>Summary\<close>

text \<open>Some miscellaneous theory about spearation algebras.\<close>



section \<open>Simp-Lemmas for Separation Algebra\<close>

named_theorems sep_algebra_simps \<open>Advanced simplification lemmas for separation algebra\<close>

lemmas [sep_algebra_simps] = sep_conj_exists
lemmas [simp] = sep_conj_assoc

lemmas sep_conj_c = sep_conj_commute sep_conj_left_commute


section \<open>Separation Algebra with a Unique Zero\<close>

class unique_zero_sep_algebra = sep_algebra +
  assumes unique_zero: "x##x \<Longrightarrow> x=0"
begin
  lemma unique_zero_simps[simp]: 
    "a##a \<longleftrightarrow> a=0"
    "a##b \<Longrightarrow> a+b = a \<longleftrightarrow> b=0"
    "a##b \<Longrightarrow> a+b = b \<longleftrightarrow> a=0"
    "a##b \<Longrightarrow> a + b = 0 \<longleftrightarrow> a=0 \<and> b=0"
    apply -
    using local.sep_disj_zero local.unique_zero apply blast
    apply (metis local.sep_add_disjD local.sep_add_zero local.unique_zero)
    apply (metis local.sep_add_disjD local.sep_add_zero_sym local.sep_disj_commute local.unique_zero)
    by (metis local.sep_add_disjD local.sep_add_zero local.sep_disj_zero local.unique_zero)

end

section \<open>Standard Instantiations\<close>

instantiation "fun" :: (type,plus) plus
begin
  definition [simp]: "(f1 + f2) x = (f1 x + f2 x)"
  instance
    by standard
end

instantiation "fun" :: (type,sep_algebra) sep_algebra
begin
  definition "f1 ## f2 \<longleftrightarrow> (\<forall>x. f1 x ## f2 x)"
 (* definition [simp]: "(f1 + f2) x = (f1 x + f2 x)" *)
  definition [simp]: "0 x \<equiv> 0"

  instance
    apply standard
    unfolding sep_disj_fun_def plus_fun_def zero_fun_def
    apply (auto)
    subgoal
      by (simp add: sep_disj_commute)
    subgoal
      using sep_add_commute by auto
    subgoal 
      by (simp add: sep_add_assoc) 
    subgoal 
      using sep_disj_addD1 by blast 
    subgoal 
      by (simp add: sep_disj_addI1) 
    done  
  
end

instance "fun" :: (type,unique_zero_sep_algebra) unique_zero_sep_algebra
  apply standard
  unfolding sep_disj_fun_def plus_fun_def zero_fun_def
  by (metis unique_zero)
  
lemma disj_fun_upd_iff[simp]: 
  "\<lbrakk>f a = 0; g a = 0\<rbrakk> \<Longrightarrow> (f(a:=x) ## g(a:=y)) \<longleftrightarrow> (f ## g \<and> x ## y)"
  unfolding sep_disj_fun_def by force


instantiation option :: (sep_algebra) sep_algebra begin

  fun sep_disj_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
    "sep_disj None None \<longleftrightarrow> True"
  | "sep_disj None (Some _) \<longleftrightarrow> True"  
  | "sep_disj (Some _) None \<longleftrightarrow> True"
  | "sep_disj (Some x) (Some y) \<longleftrightarrow> x##y"

  lemma sep_disj_option_add_simps[simp]: 
    "sep_disj None x" 
    "sep_disj x None" 
    by (cases x; simp)+
        
  fun plus_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where 
    "plus None None = None"
  | "plus None (Some x) = Some x"
  | "plus (Some x) None = Some x" 
  | "plus (Some x) (Some y) = Some (x+y)"

  lemma plus_option_add_simps[simp]: "plus None x = x" "plus x None = x"
    by (cases x; simp)+
  
  definition "0 = None"
    
  instance 
    apply standard
    apply (simp_all add: zero_option_def)
    apply (case_tac x; case_tac y; simp add: sep_disj_commute)
    apply (case_tac x; case_tac y; auto simp add: sep_disj_commute sep_add_commute)
    apply (case_tac x; case_tac y; case_tac z; simp add: sep_add_assoc)
    apply (case_tac x; case_tac y; case_tac z; auto dest: sep_disj_addD1)
    apply (case_tac x; case_tac y; case_tac z; auto dest: sep_disj_addI1)
    done    
  
end


instantiation prod :: (sep_algebra, sep_algebra) sep_algebra
begin
  definition "a##b \<longleftrightarrow> fst a ## fst b \<and> snd a ## snd b"
  definition "a+b = (fst a + fst b, snd a + snd b)"  
  definition "0 = (0,0)"
  
  instance
    apply standard
    unfolding sep_disj_prod_def plus_prod_def zero_prod_def
    by (auto 
      simp: sep_add_ac 
      intro: sep_disj_commuteI sep_disj_addD1 sep_disj_addI1)
end

lemma sep_disj_prod_lower[sep_algebra_simps]: "(a,b) ## (c,d) \<longleftrightarrow> a##c \<and> b##d"
  by (simp add: sep_disj_prod_def)
  
lemma plus_prod_lower[sep_algebra_simps]: "(a,b) + (c,d) = (a+c,b+d)"
  by (simp add: plus_prod_def)

instance prod :: (unique_zero_sep_algebra,unique_zero_sep_algebra) unique_zero_sep_algebra
  by standard (auto simp: zero_prod_def sep_algebra_simps)

lemma prod_Z_lower[sep_algebra_simps]: 
  "(a,b) = 0 \<longleftrightarrow> a=0 \<and> b=0"
  "0 = (a,b) \<longleftrightarrow> a=0 \<and> b=0"
  by (auto simp: zero_prod_def)

lemma plus_prod_eqI: "(a+b,c+d) = (a,c) + (b,d)" by (simp add: sep_algebra_simps)
      

datatype 'a tsa_opt = ZERO | TRIV (the_tsa: 'a)

instantiation tsa_opt :: (type) unique_zero_sep_algebra begin
  definition sep_disj_tsa_opt :: "'a tsa_opt \<Rightarrow> 'a tsa_opt \<Rightarrow> bool" 
    where "a##b \<longleftrightarrow> a=ZERO \<or> b=ZERO"

  definition "a+b \<equiv> (case (a,b) of (ZERO,x) \<Rightarrow> x | (x,ZERO) \<Rightarrow> x)"
  definition "0 = ZERO"

  instance
    apply standard
    by (auto simp: zero_tsa_opt_def sep_disj_tsa_opt_def plus_tsa_opt_def split: tsa_opt.splits)
  
end
  
instance tsa_opt :: (type) cancellative_sep_algebra
  apply standard
  by (auto simp: zero_tsa_opt_def sep_disj_tsa_opt_def plus_tsa_opt_def split: tsa_opt.splits)
  

(* Lowering lemmas. If one side of operation breaks abstraction level, 
  the other side is also lowered
*)  
lemma TRIV_not_zero[simp]: "TRIV x \<noteq> 0" "0\<noteq>TRIV x" by (auto simp: zero_tsa_opt_def)
lemma TRIV_Z_lower[intro!]: 
  "ZERO = 0" 
  "0 = ZERO" 
  by (auto simp: zero_tsa_opt_def)  
  
lemma triv_Z_lower2[sep_algebra_simps]:  
  "x + ZERO = x"
  "ZERO + x = x"
  by (auto simp: zero_tsa_opt_def plus_tsa_opt_def split: tsa_opt.splits)  
  
lemma TRIV_disj_simps[sep_algebra_simps]:
  "TRIV a ## b \<longleftrightarrow> b=ZERO"
  "b ## TRIV a \<longleftrightarrow> b=ZERO"
  by (auto simp: sep_disj_tsa_opt_def)
  
section \<open>Additional Simplifier Setup\<close>

(* 
  This may cause trouble on non-eta-normalized terms.
    (\<lambda>s. \<box> s) \<rightarrow> \<lambda>s. s=0
  The next lemma hopefully fixes that.
*)    

lemma sep_empty_app[sep_algebra_simps]: "\<box> h \<longleftrightarrow> h=0"
  by (simp add: sep_empty_def)

lemma sep_empty_I[sep_algebra_simps]: "(\<lambda>h. h=0) = \<box>"
  by (simp add: sep_empty_def)
  
  
section \<open>Pure Assertions\<close>

text \<open>The Separation Algebra entry only defines @{term "\<langle>\<Phi>\<rangle>"}, which
  makes no constraint on the heap. We define \<open>\<up>\<Phi>\<close>, which requires an empty heap, 
  and is more natural when using separation logic with deallocation.
\<close>      

definition pred_lift :: "bool \<Rightarrow> 'a::sep_algebra \<Rightarrow> bool" ("\<up>_" [100] 100)
  where "(\<up>\<Phi>) s \<equiv> \<Phi> \<and> \<box> s"

text \<open>Relation between \<open>pred_lift\<close> and \<open>pred_K\<close>. Warning, do not use 
  as simp-lemma, as \<open>sep_true\<close> is an abbreviation for \<open>\<langle>True\<rangle>\<close>\<close>  
lemma "\<langle>\<Phi>\<rangle> = (\<up>\<Phi> ** sep_true)" by (auto simp: pred_lift_def sep_conj_def sep_algebra_simps) 
  
lemma pred_lift_move_front_simps[sep_algebra_simps]:
  "(\<up>\<Phi> ** \<up>\<Psi>) = (\<up>(\<Phi>\<and>\<Psi>))"
  "(\<up>\<Phi> ** \<up>\<Psi> ** B) = (\<up>(\<Phi>\<and>\<Psi>) ** B)"
  "NO_MATCH (\<up>X) A \<Longrightarrow> (A ** \<up>\<Phi> ** B) = (\<up>\<Phi> ** A ** B)"
  "NO_MATCH (\<up>X) A \<Longrightarrow> (A ** \<up>\<Phi>) = (\<up>\<Phi> ** A)"
  by (auto simp: pred_lift_def sep_conj_def sep_algebra_simps)
  
lemma pred_lift_extract_simps:
  "(\<up>\<Phi>) h \<longleftrightarrow> \<Phi> \<and> h=0"
  "(\<up>\<Phi> ** A) h \<longleftrightarrow> \<Phi> \<and> A h"
  by (auto simp: pred_lift_def sep_conj_def sep_algebra_simps)
  
lemma pure_true_conv[sep_algebra_simps]: "\<up>True = \<box>" by (auto simp: sep_algebra_simps pred_lift_extract_simps)

lemma pred_lift_false_conv[simp]: "\<up>False = sep_false" by (auto simp: sep_algebra_simps pred_lift_extract_simps)


lemmas sep_conj_false_simps =
  pred_lift_false_conv
  sep_conj_false_left sep_conj_false_right



end
