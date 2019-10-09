(*
  Author: Maximilian P. L. Haslbeck
  Author: Christoph Matheja
  Author: Kevin Batz
*)
theory QuantSepCon
  imports 
    "Separation_Algebra.Separation_Algebra" "HOL-Library.Extended_Nat"
    "HOL-Library.Extended_Nonnegative_Real" 
    Misc        
begin 


section \<open>Quantitative Separating Connectives\<close>

term "class.complete_lattice"


subsection \<open>The Locale quant_sep_con\<close>
 
locale comm_quantale =  complete_lattice Inf Sup inf le less sup bot top
  + comm_monoid oper neutr
  for   Inf :: "'b set \<Rightarrow> 'b" ("\<Sqinter>_" [900] 900)
    and Sup ("\<Squnion>_" [900] 900)
    and inf
    and le (infix "\<le>" 50) and  less (infix "<" 50)
    and sup bot top 
    and oper :: "'b  \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>*" 70)
    and neutr :: "'b" ("\<^bold>1") +
  assumes 
    Sup_mult_left_distrib: "\<And>c A. c \<^bold>* Sup A = Sup (((\<^bold>*) c) ` A)"
begin

lemma mult_bot: "\<And>x. x \<^bold>* bot = bot"
  using Sup_mult_left_distrib[where A="{}"] by simp

lemma Sup_mult_right_distrib: "Sup I \<^bold>* c = Sup ((\<lambda>i. i \<^bold>* c) ` I)" 
  by (auto simp add: commute Sup_mult_left_distrib) 

lemma oper_left_mono: "(a::'b) \<le> b \<Longrightarrow> c \<^bold>* a \<le> c \<^bold>* b"
  using Sup_mult_left_distrib[where A="{a,b}" and c=c]
  by (simp add: sup.absorb_iff2)

lemma oper_right_mono: "\<And>a b c. a \<le> b \<Longrightarrow> a \<^bold>* c \<le> b \<^bold>* c"
  using oper_left_mono by (auto simp add: commute)

lemma oper_mono: "\<And>a b c d. a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a \<^bold>* c \<le> b \<^bold>* d"
  apply (erule oper_right_mono [THEN order_trans])
  by (erule oper_left_mono)

end



locale quant_sep_con =  comm_quantale Inf Sup inf le less sup bot top  oper neutr
  for   Inf :: "'b set \<Rightarrow> 'b" ("\<Sqinter>_" [900] 900)
    and Sup ("\<Squnion>_" [900] 900)
    and inf
    and le (infix "\<le>" 50) and  less (infix "<" 50)
    and sup bot top
    and oper :: "'b  \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>*" 70)
    and neutr :: "'b" ("\<^bold>1") +
  fixes
    divide :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>div" 70)
  assumes 
    \<comment>\<open>Facts about div\<close>
    divide_neutral: "\<And>x::'b. x \<^bold>div \<^bold>1 = x"   (* maybe \<^bold>\<le> suffices *)
    and divide_right_mono_general: "\<And>a b c. a \<le> b \<Longrightarrow> a \<^bold>div c \<le> b \<^bold>div c" 
    and divide_right_antimono_general: "\<And>a b c. c \<le> b \<Longrightarrow> a \<^bold>div b \<le> a \<^bold>div c"  
    \<comment> \<open>oper and divide are "adjoint" = The essence of equation 79\<close>
    and div_mult_adjoint:
    "\<And>A B C :: 'b.  \<lbrakk>(bot < C \<or> bot < B ) ; (C < top \<or> B < top) \<rbrakk> \<Longrightarrow> (A \<le> B \<^bold>div C) \<longleftrightarrow> A \<^bold>* C \<le> B"
    \<comment> \<open>bot is not neutral\<close>
    and bot_not_neutral: "bot < \<^bold>1" 
begin   


subsection \<open>stuff about complete lattices:\<close>

lemma nn: "(\<not> x < (top)) = (x = top)" 
  using top.not_eq_extremum by blast

lemma nn_bot: "(\<not> bot <  x) = (x = bot)" 
  using bot.not_eq_extremum by blast

lemma botnottop: "bot \<noteq> top"
  using bot_not_neutral by auto

lemma gt_botI: "\<not> a \<le> bot \<Longrightarrow> bot < a" 
  using local.bot_less by blast 

lemma lt_topI: "\<not> e \<le> A \<Longrightarrow>  A < top"
  using local.top.not_eq_extremum local.top_greatest by blast

lemma le_sideconditions:
  fixes a b c :: 'b
  shows "((bot < a \<or> bot < b) \<and> (a < top \<or> b < top) \<longrightarrow> a \<le> b) \<longleftrightarrow> (a \<le> b)" 
  by (auto simp: nn nn_bot mult_bot botnottop intro: gt_botI)  

lemma l_Sup_cong: "\<And>S S'. S=S' \<Longrightarrow> Sup S = Sup S'"
  by simp
 
abbreviation SUPR :: "'c set \<Rightarrow>('c \<Rightarrow> 'b) \<Rightarrow> 'b" 
  where "SUPR A f \<equiv> \<Squnion>(f ` A)" 

abbreviation INFI :: "'c set \<Rightarrow>('c \<Rightarrow> 'b) \<Rightarrow> 'b" 
  where "INFI A f \<equiv> \<Sqinter>(f ` A)" 

lemma INF_mono_strong: "(\<And>m. m \<in> B \<Longrightarrow> g m < top \<Longrightarrow> \<exists>n\<in>A. f n \<le> g m) \<Longrightarrow> (INFI A f) \<le> (INFI B g)"
  using Inf_mono_strong [of "g ` B" "f ` A"] by auto

lemma SUP_UNION: "(SUPR (\<Union>y\<in>A. g y) (\<lambda>x. f x)) = (SUPR A (\<lambda>y. SUPR (g y) (\<lambda>x. f x )))"
  apply (rule antisym)
  by  (blast intro: SUP_least SUP_upper2)+

lemma SUP_times_distrib2_general:
  fixes g :: "_\<Rightarrow>_\<Rightarrow>'b"
  shows "SUPR A (\<lambda>(x,y). f x y \<^bold>* g x y) \<le> 
            SUPR A (\<lambda>(x,y). f x y) \<^bold>* SUPR A (\<lambda>(x,y). g x y)"  
  by (auto intro!: SUP_least intro: SUP_upper2  oper_mono)

lemma SUP_mult_left_distrib: "\<And>c f. c \<^bold>* SUPR I (\<lambda>i. f i) = SUPR I (\<lambda>i. c \<^bold>* f i)" 
  by (simp add: image_image Sup_mult_left_distrib)

lemma SUP_mult_right_distrib: "SUPR I (\<lambda>i. f i) \<^bold>* c = SUPR I (\<lambda>i. f i \<^bold>* c)" 
  by (simp add: image_image Sup_mult_right_distrib)

lemma sup_times_distrib: "(a::'b) \<^bold>* sup b c = sup (a\<^bold>*b) (a\<^bold>*c)"  
  using Sup_mult_left_distrib[where A="{b,c}"] by simp

subsection \<open>Facts derived from @{thm div_mult_adjoint}}:\<close>

lemma top_divide:  "\<And>x. x < top \<Longrightarrow>  top \<^bold>div x = top"
  using div_mult_adjoint
  by (metis local.bot_less local.top_greatest local.top_unique)  

lemma divide_bot: "\<And>x::'b. bot < x \<Longrightarrow> x \<^bold>div bot = top"   
  using div_mult_adjoint  
  by (metis bot.extremum mult_bot le_less_trans nn top.extremum_unique) 
 



context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin
   

subsection \<open>Quantitative Separating Conjunction\<close>

definition
  sep_conj_q  (infixr "**q" 35)
  where
  "P **q Q \<equiv> \<lambda>h. Sup { P x \<^bold>* Q y | x y. h=x+y \<and> x ## y}" 

lemma sep_conj_q_alt :
  "(P **q Q) = (\<lambda>h. SUPR {(x,y). h=x+y \<and> x ## y} (\<lambda>(x,y). P x \<^bold>* Q y))"
  unfolding  sep_conj_q_def
  apply(rule ext)  by (auto intro!: l_Sup_cong)  


lemma sep_conj_q_SUP:
  "(P **q Q) = (\<lambda>h. (SUPR {(x,y)| x y. h=x+y \<and> x ## y} (\<lambda>i. (\<lambda>(x,y). P x \<^bold>* Q y) i)))"
  unfolding  sep_conj_q_def
  apply(rule ext)  by (auto intro!: l_Sup_cong)  


subsection \<open>Quantitative Separating Implication - Magic Wand\<close>
 
definition
  sep_impl_qq  :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a  \<Rightarrow> 'b ) \<Rightarrow> 'a \<Rightarrow> 'b"   (infixr "-*qq" 35)
  where 
  "P -*qq Q \<equiv> \<lambda>h. INFI { h'. h ## h' \<and> (bot < P h' \<or> bot < Q (h+h') )
                                \<and> (P h' < top \<or> Q (h+h') < top)}
                               (\<lambda>h'. (Q (h + h')) \<^bold>div (P h'))"


subsection \<open>Embedding of SL into QSL\<close>

definition emb  where "emb P = (\<lambda>h. if P h then \<^bold>1 else bot)"

lemma emb_range: "emb P x \<in> {bot,\<^bold>1}" unfolding emb_def by auto

lemma emb_squared: "emb P x = emb P x \<^bold>* emb P x"
  apply (cases "emb P x = bot") using emb_range apply (auto simp: mult_bot) by fastforce

lemma emb_1: "emb P h = \<^bold>1 \<longleftrightarrow> P h"
  apply (auto simp: emb_def) using bot_not_neutral by blast  

definition sep_empty_q :: "'a \<Rightarrow> 'b"  where
  "sep_empty_q \<equiv> emb (\<lambda>h. h = 0)"

text \<open>The restricted wand with an predicate in the first component:\<close>

abbreviation sep_impl_q (infixr "-*q" 35) where   "(P -*q Q) \<equiv> (emb P -*qq Q)" 
 
 

lemma sep_impl_q_alt_general:
  fixes  Q :: "'a \<Rightarrow> 'b" 
  shows 
    "inf \<^bold>1 ((P -*q Q) h) = inf \<^bold>1 (INFI  { h'. h ## h' \<and> P h'} (\<lambda>h'. Q (h + h')))"
proof -
  have T: "{h'. h ## h' \<and> ((bot::'b) < emb P h' \<or> (bot::'b) < Q (h + h'))
                       \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}
      = {h'. h ## h' \<and>  (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < top)}
       \<union>  {h'. h ## h' \<and>(bot::'b) = emb P h' \<and> (bot::'b) < Q (h + h')
                       \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}" 
    using bot.not_eq_extremum by fastforce    

  let ?A = "{h'. h ## h' \<and> Q (h + h') < top \<and> P h'}"
  let ?B = "{h'. h ## h' \<and> (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}"
  have AB: "?A \<subseteq> ?B"  by (auto simp: emb_def bot_not_neutral)
  

  have KK: "\<^bold>1 \<le> (INFI (?B-?A) (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))"
    by(auto simp: le_Inf_iff emb_def divide_neutral intro: lt_topI)   

  have 1: "inf \<^bold>1 (INFI ?B (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))
      = inf \<^bold>1 (INFI ?A (\<lambda>x. Q (h + x)))"
  proof -
    have B_decompose: "?B = (?B - ?A) \<union> (?A)"  using AB by blast 
    have i: "(INFI ?A (\<lambda>h'. Q (h + h') \<^bold>div emb P h')) = (INFI ?A (\<lambda>h'.  Q (h + h')))"
       by (auto simp: emb_def divide_neutral)

    have ii: "inf \<^bold>1 (INFI (?B-?A) (\<lambda>h'. Q (h + h') \<^bold>div emb P h')) = \<^bold>1" 
      using KK by (auto intro: antisym) 

    have "(INFI (?B) (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))
            = inf (INFI (?B - ?A) (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))
                   (INFI (?A) (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))"
      apply(subst B_decompose) by(rule INF_union)
    also have "\<dots> = inf (INFI (?B - ?A) (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))
                          (INFI (?A) (\<lambda>h'.  Q (h + h')))"
      unfolding i by simp
    finally
    have iii: "(INFI (?B) (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))
           = inf (INFI (?B - ?A) (\<lambda>h'. Q (h + h') \<^bold>div emb P h')) (INFI (?A) (\<lambda>h'.  Q (h + h')))" .

    have "inf \<^bold>1 (INFI (?B) (\<lambda>h'. Q (h + h') \<^bold>div emb P h')) 
              = inf \<^bold>1 (inf (INFI (?B-?A) (\<lambda>h'. Q (h + h') \<^bold>div emb P h')) 
                            (INFI (?A) (\<lambda>h'.  Q (h + h'))))"
      unfolding iii by simp
    also have "\<dots> = inf (inf \<^bold>1 (INFI (?B-?A) (\<lambda>h'. Q (h+h') \<^bold>div emb P h')))
                        (INFI ?A (\<lambda>h'. Q (h+h')))"
      by(simp add: inf.assoc)
    also have "\<dots> = inf \<^bold>1 (INFI (?A) (\<lambda>h'.  Q (h + h')))"
      unfolding ii by simp
    finally show ?thesis .
  qed 


  have "(\<exists>h'. h ## h' \<and> (bot::'b) < top \<and> Q (h + h') < top  \<and> P h')
             \<Longrightarrow> (INFI { h'. h ## h' \<and> P h'} (\<lambda>h'. Q (h + h'))) < top"
    apply safe subgoal for h' 
      apply(rule order.strict_trans1)
       apply(rule INF_lower[where i=h']) by auto
    done

  have "~(\<exists>h'. h ## h' \<and> (bot::'b) < top \<and> Q (h + h') < top  \<and> P h')
           \<Longrightarrow> (INFI { h'. h ## h' \<and> P h'} (\<lambda>h'. Q (h + h'))) = top"
    apply auto  
    by (metis Inf_UNIV Inf_top_conv(2) UNIV_I top.not_eq_extremum)  

  have 2: "(INFI {h'. h ## h' \<and> (bot::'b) = emb P h' \<and> (bot::'b) < Q (h + h') 
                   \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}
                 (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))
      = top" 
    by (simp_all add: divide_bot) 

  have F: "{ h'. h ## h' \<and> P h'} = { h'. h ## h' \<and> P h' \<and> Q (h + h') = top}
                                     \<union> { h'. h ## h' \<and> P h' \<and> Q (h + h') < top}"
    using top.not_eq_extremum by blast

  have 3: "(INFI {h'. h ## h' \<and> P h' \<and> Q (h + h') = top} (\<lambda>h'. Q (h + h'))) = top"
    by auto

  have "inf \<^bold>1 ((P -*q Q) h)
     = inf \<^bold>1 (inf (INFI {h'. h ## h' \<and> (bot::'b) < emb P h'
                               \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}
                          (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))
                   (INFI {h'. h ## h' \<and> (bot::'b) = emb P h'\<and> (bot::'b) < Q (h + h')
                               \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}
                          (\<lambda>h'. Q (h + h') \<^bold>div emb P h')))"
    unfolding sep_impl_qq_def T INF_union
    by simp
  also have "\<dots> =  inf \<^bold>1 (inf (INFI {h'. h ## h' \<and> (bot::'b) < emb P h'
                               \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}
                          (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))
     top)"
    unfolding 2 by simp
  also have "\<dots> = inf \<^bold>1 (INFI {h'. h ## h' \<and> (bot::'b) < emb P h'
                              \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}
                           (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))"
    by simp
  also have "\<dots>  = inf \<^bold>1 (INFI {h'.  h ## h'  \<and> Q (h + h') < top \<and> P h'} (\<lambda>x. Q (h + x)))"
    unfolding 1 by simp
  also have "\<dots> = inf \<^bold>1 ( INFI { h'. h ## h' \<and> P h'} (\<lambda>h'. Q (h + h')))"
    unfolding F INF_union 3
    apply(rule arg_cong[where f="\<lambda>x. inf \<^bold>1 x"])
    by (auto intro: INF_cong)
  finally show "inf \<^bold>1 ((P -*q Q) h) =  inf \<^bold>1 (INFI {h'. h ## h' \<and> P h'} (\<lambda>h'. Q (h + h')))" .
qed

lemma sep_impl_q_alt_general':
  fixes  Q :: "'a \<Rightarrow> 'b" 
  assumes "\<^bold>1 = top"
  shows 
  "((P -*q Q) h) = (INFI { h'. h ## h' \<and> P h'} (\<lambda>h'. Q (h + h')))"
  using assms sep_impl_q_alt_general by simp

subsubsection \<open>Conservativity of QSL as an assertion language\<close>

lemma Sup_zeroone: "P \<subseteq> {bot,\<^bold>1} \<Longrightarrow> Sup P \<in> {bot,\<^bold>1}" 
proof -
  assume " P \<subseteq> {bot,\<^bold>1}"
  then consider "P = {}" | "P={bot}" | "P={\<^bold>1}" | "P={bot,\<^bold>1}" by auto
  then show ?thesis apply(cases)
    by auto
qed 

lemma sep_conj_q_range: "((emb P) **q (emb Q)) h \<in> {bot,\<^bold>1}"
  unfolding sep_conj_q_def  
  apply(rule Sup_zeroone) 
  apply (auto simp: emb_def) using   divide_neutral divide_bot mult_bot      by auto  
   

lemma Inf_zeroone: "P \<noteq> {} \<Longrightarrow> P \<subseteq> {bot,\<^bold>1} \<Longrightarrow> Inf P \<in> {bot,\<^bold>1}" 
proof -
  assume "P \<noteq> {}" " P \<subseteq> {bot,\<^bold>1}"
  then consider  "P={bot}" | "P={\<^bold>1}" | "P={bot,\<^bold>1}" by auto
  then show ?thesis apply(cases)
    by auto
qed  

lemma Inf_zeroonetop: " P \<subseteq> {bot,\<^bold>1,top} \<Longrightarrow> Inf P \<in> {bot,\<^bold>1,top}"    
  by (smt insertI2 insert_Diff insert_absorb2 insert_commute insert_not_empty
        local.Inf_insert local.Inf_lower local.ccInf_empty local.inf_top.right_neutral
        local.le_bot singleton_insert_inj_eq' subset_antisym subset_insert_iff)  

(*
lemma Inf_zeroonetop: "P \<subseteq> {bot,\<^bold>1,top} \<Longrightarrow> Inf P \<in> {bot,\<^bold>1,top}"    
proof -
  assume " P \<subseteq> {bot,\<^bold>1,top}"
  then consider "P = {}"
    | "P={bot}" | "P={\<^bold>1}" | "P={top}"
    | "P={bot,\<^bold>1}" | "P={bot,top}" | "P={top,\<^bold>1}"
    | "P={bot,\<^bold>1,top}" by auto
  then show ?thesis apply(cases)
    by auto
qed  *)

lemma sep_conj_q_leq1: "((emb P) **q (emb Q)) h \<le> \<^bold>1"
  using sep_conj_q_range[of P Q h] by auto 

lemma emb_not_bot: "bot < emb P h \<longleftrightarrow> emb P h = \<^bold>1"
  using bot_not_neutral by (auto simp: emb_def) 

lemma emb_not_bot2: "bot \<noteq> emb P h \<longleftrightarrow> emb P h = \<^bold>1"
    "emb P h \<noteq> bot \<longleftrightarrow> emb P h = \<^bold>1"
  using bot_not_neutral by (auto simp: emb_def) 
 
lemma sep_impl_q_rangezeroonetop: "((P -*q (emb Q)) h) \<in> {bot,\<^bold>1,top}"  
  unfolding sep_impl_qq_def  
    apply(rule Inf_zeroonetop)  
  subgoal apply (auto simp: emb_not_bot emb_not_bot2 divide_neutral  )
    apply(auto simp: emb_def divide_neutral divide_bot bot_not_neutral)
    done
  done

lemma inf_1_cuts: "a \<in> {bot, \<^bold>1, top} \<Longrightarrow> inf \<^bold>1 a \<in> {bot, \<^bold>1}"
proof -
  assume "a \<in> {bot, \<^bold>1, top}" 
  then have "inf \<^bold>1 a \<in> { \<^bold>1, bot}"
    using inf_bot_right inf_idem inf_top_right by blast
  then show ?thesis
    using bot_ennreal by auto
qed

lemma sep_impl_q_range: "inf \<^bold>1 ((P -*q (emb Q)) h) \<in> {bot, \<^bold>1}"  
  apply(rule inf_1_cuts) by(rule sep_impl_q_rangezeroonetop)   

lemma quant_wand_conservative: 
  fixes P :: "'a \<Rightarrow> bool"
  shows "(P  \<longrightarrow>* Q) h  \<longleftrightarrow> inf \<^bold>1 (((emb P) -*qq (emb Q)) h)  = \<^bold>1"
proof - 
  (* rather ugly proof, DB's fault ;) *)
  fix h 
  have " ((inf \<^bold>1 ((P -*q (emb Q)) h)) = \<^bold>1)
         \<longleftrightarrow> ((inf \<^bold>1 ((INFI {h'. h ## h' \<and> P h'} (\<lambda>h'. emb Q (h + h'))))) = \<^bold>1)" 
    unfolding sep_impl_q_alt_general by simp 
  also have "\<dots> \<longleftrightarrow> (\<forall>h'. h ## h' \<and> P h' \<longrightarrow> Q (h + h'))"
    apply(rule iffI)
    subgoal 
      apply(cases "{h'. h ## h' \<and> P h'} = {}")
      subgoal by auto
      subgoal proof (safe, goal_cases)
        case (1 h' x)
        from 1(2-4) have "inf \<^bold>1 (INFI {h'. h ## h' \<and> P h'} (\<lambda>h'. emb Q (h + h'))) \<le> bot" 
          apply(intro le_infI2)
          apply(intro INF_lower2[where i=h']) by (auto simp: emb_def)
        then show ?case using 1(1) bot_not_neutral by auto
      qed 
      done 
    subgoal  
      by(auto simp add: emb_def INF_constant cong: INF_cong_simp  ) 
    done
  also have "\<dots> \<longleftrightarrow> (P  \<longrightarrow>* Q) h" unfolding sep_impl_def by auto
  finally show "(P  \<longrightarrow>* Q) h \<longleftrightarrow> inf \<^bold>1 ((P -*q (emb Q)) h) = \<^bold>1" by simp
qed 


lemma quant_wand_conservative':
  fixes P :: "'a \<Rightarrow> bool"
  assumes "\<^bold>1 = top"
  shows "(P  \<longrightarrow>* Q) h  \<longleftrightarrow> (((emb P) -*qq (emb Q)) h)  = \<^bold>1"
  using assms quant_wand_conservative by simp

lemma quant_star_conservative:
  fixes P :: "'a \<Rightarrow> bool"
  shows "(P ** Q) h \<longleftrightarrow> ((emb P) **q (emb Q)) h = \<^bold>1" 
proof -
  have "(P ** Q) h = (\<exists>xa y. xa ## y \<and> h = xa + y \<and> emb P xa = \<^bold>1 \<and> emb Q y = \<^bold>1)"
    unfolding sep_conj_def emb_1 by auto
  also have "\<dots> = (Sup { emb P x \<^bold>* emb Q y | x y. h=x+y \<and> x ## y} = \<^bold>1)"
    apply rule
    subgoal  
      apply(rule antisym)
      subgoal apply(subst sep_conj_q_leq1[unfolded sep_conj_q_def] ) by simp
      subgoal apply(rule Sup_upper) by force 
      done
    subgoal
    proof (rule ccontr, goal_cases)
      case 1
      from 1(2) have "\<And>x y. (x,y) \<in> {(x,y) | x y. h = x + y \<and> x ## y}
               \<Longrightarrow> emb P x \<^bold>* emb Q y = bot" 
        by (auto simp: emb_def split: if_splits simp: mult_bot)  
      then have "Sup {emb P x \<^bold>* emb Q y |x y. h = x + y \<and> x ## y} \<le>  bot"
          by (auto intro: Sup_least)
      with 1(1) show "False" using bot_not_neutral by simp 
    qed 
    done
  also have "\<dots> = (((emb P) **q (emb Q)) h = \<^bold>1)" unfolding sep_conj_q_def by simp
  finally show ?thesis .
qed
 


subsection \<open>Properties of Quantitative Separating Connectives\<close> 

subsubsection \<open>Commutative monoid\<close>



lemma SUP_UNION_my: "(SUPR A (\<lambda>y. SUPR (g y) (\<lambda>x. f y x ))) = (SUPR (\<Union>y\<in>A. Pair y ` g y) (\<lambda>xy. f (fst xy) (snd xy)))"
  apply (rule antisym)
  subgoal 
    apply(rule SUP_least) 
    apply(rule SUP_least) 
    subgoal for x y 
      apply(rule SUP_upper2[where i="(x,y)"]) by auto
    done
  subgoal 
    apply(rule SUP_least)
    apply auto subgoal for x y
    apply(rule SUP_upper2[where i=x]) apply simp
      apply(rule SUP_upper2[where i=y]) by auto 
    done
  done


lemma pp: "(\<And>x. gg (g x) = x) \<Longrightarrow> SUPR S f = SUPR (g ` S) (f o gg)"
  by (simp add: image_image)

lemma star_assoc:
  fixes x y z :: "'a \<Rightarrow> 'b"
  shows  "(x **q (y **q z))  = ((x **q y) **q z) "
proof (rule ext)
  fix h 
  have "(x **q (y **q z)) h 
      = (SUPR {(x, y) |x y. h = x + y \<and> x ## y} (\<lambda> (xa, ya). 
          x xa \<^bold>* (SUPR {(x, y) |x y. ya = x + y \<and> x ## y} (\<lambda> (x, ya). y x \<^bold>* z ya))))" 
    unfolding sep_conj_q_SUP by auto 
  also have "\<dots> = (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>xa.
                    case xa of (xa, ya) \<Rightarrow> SUPR {(x, y). ya = x + y \<and> x ## y} (\<lambda>i.
                          (case i of (h21, h22) \<Rightarrow> x xa \<^bold>* y h21 \<^bold>* z h22))))"
    by(simp add: SUP_mult_left_distrib prod.case_distrib assoc)  
  also have "\<dots> = (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>xa.
                    SUPR {((fst xa),x, y)| x y . snd xa = x + y \<and> x ## y}
                        (\<lambda>i. (case i of (b, h21, h22) \<Rightarrow> x b \<^bold>* y h21 \<^bold>* z h22))))"
      by(force intro!: arg_cong[where f=Sup]) 
  also have "\<dots> = (SUPR {(h1, h2, h3). h = h1 + h2 + h3 \<and> h1 ## h2 + h3
                                           \<and> h1 ## h2 \<and> h1 ## h3 \<and> h3 ## h2 }
                    (\<lambda>xa. case xa of (h1, h2, h3) \<Rightarrow> x h1 \<^bold>* y h2 \<^bold>* z h3))" 
    apply(subst SUP_UNION[symmetric]) 
    apply(rule SUP_cong)
    subgoal
      apply safe
      subgoal by (metis fstI sep_add_assoc sep_disj_addD1 sep_disj_addD2 sndI)
      by (auto simp: sep_add_ac dest: sep_disj_addD) 
    subgoal by auto
    done
  also have "\<dots> = (SUPR {(x, y). h = x + y \<and> x ## y}
                    (\<lambda>xa. SUPR {(h1,h2,snd xa)| h1 h2. fst xa = h1 + h2 \<and> h1 ## h2}
                       (\<lambda>i. (case i of (h1, h2, h3) \<Rightarrow> x h1 \<^bold>* y h2 \<^bold>* z h3))))"
    apply(subst SUP_UNION[symmetric]) 
    apply(rule SUP_cong)
    subgoal 
      by (auto simp: sep_add_ac dest: sep_disj_addD
               intro: sep_disj_addI1 sep_disj_addI3 sep_disj_commuteI )   
    subgoal
      by auto
    done
  also have "\<dots> = (SUPR {(h12, h3). h = h12 + h3 \<and> h12 ## h3} (\<lambda>xa.
                    case xa of (h12,h3) \<Rightarrow> SUPR {(x, y). h12 = x+y \<and> x ## y}
                          (\<lambda>h12. (case h12 of (h1, h2) \<Rightarrow> (x h1 \<^bold>* y h2 \<^bold>* z h3)))))"
    apply(rule SUP_cong)
     apply simp
    apply safe
    apply(rule l_Sup_cong) by force
  also have "\<dots> = ((x **q y) **q z) h"
    unfolding sep_conj_q_SUP apply(auto simp: SUP_mult_right_distrib) 
    apply(rule SUP_cong)
     apply simp
    apply safe
    apply(rule SUP_cong) by (auto simp: mult.assoc) 
  finally show "(x **q (y **q z)) h  = ((x **q y) **q z) h " .
qed

lemma star_comm:
  fixes X Y :: "_ \<Rightarrow> 'b"
  shows  "(X **q Y) = (Y **q X)"
  unfolding sep_conj_q_SUP
  apply(rule ext)
  apply(rule l_Sup_cong)
  by (auto simp add: commute sep_add_ac) 

lemma emp_neutral1:
  "(X **q sep_empty_q) = X"
  unfolding sep_conj_q_def sep_empty_q_def emb_def
  apply(rule ext)
  apply(rule antisym)
  subgoal
    by (auto intro!: Sup_least simp: mult_bot)
  subgoal
    by (auto intro: Sup_upper)
  done

lemma emp_neutral2 : 
  "(sep_empty_q **q X) = X"
  by (simp add: star_comm emp_neutral1) 

lemmas emp_neutral = emp_neutral1 emp_neutral2

lemma sep_conj_q_left_commute:
  fixes P Q R :: "'a \<Rightarrow> 'b"
  shows  "(P **q Q **q R) = (Q **q P **q R)"
  apply(subst star_assoc)
  apply(subst star_comm)
  apply(subst star_assoc) by simp


lemmas sep_conj_q_c = star_comm sep_conj_q_left_commute


subsubsection \<open>(Sub)distributivity Laws\<close>


abbreviation "fsup Q R \<equiv> (\<lambda>x. sup (Q x) (R x))"

lemma theorem_3_6_general1: 
  fixes
      P :: "'a \<Rightarrow> 'b"  
  shows
  "(P **q (fsup Q R)) = fsup (P **q Q) (P **q R)"
proof 
  fix h
  have "(P **q (fsup Q R)) h = Sup {P x \<^bold>* fsup Q R y |x y. h = x + y \<and> x ## y}"
    unfolding sep_conj_q_def by simp
  also have "\<dots> = Sup { sup (P x \<^bold>* Q y) (P x \<^bold>* R y) |x y. h = x + y \<and> x ## y}"
    apply(subst sup_times_distrib)  by simp
  also have "\<dots> = (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>x. case x of (x,y) \<Rightarrow> sup (P x \<^bold>* Q y) (P x \<^bold>* R y)))" 
    apply (rule arg_cong[where f=Sup]) by auto
  also have "\<dots> = (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>x. sup (P (fst x) \<^bold>* Q (snd x)) (P (fst x) \<^bold>* R (snd x))))"
    apply (rule arg_cong[where f=Sup])  
    by (meson prod.case_eq_if)    
  also have "\<dots> = sup (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>x. P (fst x) \<^bold>* Q (snd x)))
   (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>x. P (fst x) \<^bold>* R (snd x)))"
    apply(subst SUP_sup_distrib[symmetric]) ..
  also have "\<dots> = fsup (P **q Q) (P **q R) h"
    unfolding sep_conj_q_alt apply simp
    by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
  finally show "(P **q fsup Q R) h = fsup (P **q Q) (P **q R) h " . 
qed
 
lemma theorem_3_6_general3: 
  fixes 
      Q :: "_ \<Rightarrow> 'b"  
  shows 
  "( (emb \<phi>) **q (\<lambda>h. Q h \<^bold>* R h)) h \<le> ((emb \<phi>) **q Q) h \<^bold>* ((emb \<phi>) **q R) h"
  proof -
    have "( (emb \<phi>) **q (\<lambda>h. Q h \<^bold>* R h)) h  =  (SUPR {(h1, h2). h = h1 + h2 \<and> h1 ## h2} (\<lambda> (h1, h2). emb \<phi> h1 \<^bold>* (\<lambda>h. Q h \<^bold>* R h) h2))"
      unfolding sep_conj_q_alt by simp
    also have "... = (SUPR {(h1, h2). h = h1 + h2 \<and> h1 ## h2} (\<lambda>(h1, h2). emb \<phi> h1 \<^bold>* Q h2 \<^bold>* R h2))" apply (rule SUP_cong) 
      by (auto simp: assoc)    
    also have "... =   (SUPR {(h1, h2). h = h1 + h2 \<and> h1 ## h2} (\<lambda>(h1, h2). (emb \<phi> h1 \<^bold>* Q h2) \<^bold>* ( emb \<phi> h1  \<^bold>* R h2)))"
      apply (subst (1) emb_squared)
      by (simp add: ac_simps)
    also have "... \<le> (SUPR {(h1, h2). h = h1 + h2 \<and> h1 ## h2} (\<lambda>(h1, h2). (emb \<phi> h1  \<^bold>* Q h2)))
                 \<^bold>* (SUPR {(h1, h2). h = h1 + h2 \<and> h1 ## h2} (\<lambda>(h1, h2).  ( emb \<phi> h1  \<^bold>* R h2)))"
      by (rule SUP_times_distrib2_general)
    also have "... = ((emb \<phi>) **q Q) h \<^bold>* ((emb \<phi>) **q R) h"
      by (simp add: local.sep_conj_q_alt)
    finally show "( (emb \<phi>) **q (\<lambda>h. Q h \<^bold>* R h)) h \<le> ((emb \<phi>) **q Q) h \<^bold>* ((emb \<phi>) **q R) h".
  qed
 
lemma theorem_3_6: 
  fixes 
      Q :: "'a \<Rightarrow> 'b"  
  shows 
  "(P **q (fsup Q R)) = fsup (P **q Q) (P **q R)"
  "( (emb \<phi>) **q (\<lambda>h. Q h \<^bold>* R h)) h \<le> ((emb \<phi>) **q Q) h \<^bold>* ((emb \<phi>) **q R) h"
  using theorem_3_6_general1 theorem_3_6_general3 by auto

subsubsection \<open>Or\<close> 

lemma emb_or: "emb (X or Y) = (fsup (emb X) (emb Y))" 
  unfolding emb_def by auto 


subsubsection \<open>monotonicity of @{term "(**q)"}\<close>

text \<open>theorem 3.7\<close>
 

lemma sep_conj_q_mono:
  fixes X X' :: "_ \<Rightarrow> 'b"
  shows 
   "(\<And>x. X x \<le> X' x) \<Longrightarrow> (\<And>y. Y y  \<le> Y' y) \<Longrightarrow> (X **q Y) h \<le> (X' **q Y') h"  
  by (force intro: le_funI SUP_mono simp add: sep_conj_q_alt oper_mono le_funD)  
 
lemma sep_conj_q_right_mono:
  fixes P :: "_ \<Rightarrow> 'b"
  assumes P: "\<And>h. P h \<le> I h"
  shows "(P **q R) h \<le> (I **q R) h" 
  using sep_conj_q_mono assms by blast

lemma sep_conj_q_left_mono:
  fixes P :: "_ \<Rightarrow> 'b"
  assumes P: "\<And>h. P h \<le> I h"
  shows "(P **q R) h \<le> (I **q R) h" 
  using sep_conj_q_mono assms by blast

subsubsection \<open>monotonicity of @{term "(-*qq)"}\<close>


lemma sep_impl_q_left_mono: 
  fixes P :: "_\<Rightarrow>'b"
  shows "(\<And>y. Y y \<le> Y' y) \<Longrightarrow> (P -*qq Y) h \<le> (P -*qq Y') h"  
  unfolding sep_impl_qq_def 
  apply(rule INF_mono_strong) 
  subgoal for h'
    apply(rule bexI[where x=h'])
    subgoal by (auto intro!: divide_right_mono_general)
    subgoal using local.less_le_not_le local.top.not_eq_extremum divide_bot local.bot_less
      by (force intro!: divide_right_mono_general) 
    done
  done

lemma sep_impl_q_left_mono': 
  fixes P :: "_\<Rightarrow>'b"
  shows "(\<And>y. Y y \<le> Y' y) \<Longrightarrow> (P -*qq Y) h \<le> (P -*qq Y') h"  
  using sep_impl_q_left_mono by blast
  
lemma ennreal_inverse_antimono:
  "(a::ennreal) \<le> b \<Longrightarrow> inverse b \<le> inverse a"
  apply(cases a; cases b; cases "a=0"; cases "b=0") 
     apply simp_all
   apply(simp add: inverse_ennreal)     
  using ennreal_neq_top top.extremum_uniqueI  
  by (simp add: le_ennreal_iff)  



lemma sep_impl_q_right_antimono: 
  shows "(\<And>h. P' h \<le> P h) \<Longrightarrow> (P -*qq Y) h \<le> (P' -*qq Y) h"  
  unfolding sep_impl_qq_def
  apply(rule INF_mono_strong)
  subgoal for   h'  
    apply(rule bexI[where x=h'])
    by (auto intro!: divide_right_antimono_general  simp: nn top_divide local.less_le_trans ) 
  done


lemma sep_impl_q_mono: 
  shows "(\<And>x. P' x \<le> P x) \<Longrightarrow> (\<And>x. Y x \<le> Y' x) \<Longrightarrow> (P -*qq Y) h  \<le> (P' -*qq Y') h"  
  apply(rule order.trans)
  apply(rule sep_impl_q_left_mono[where Y'=Y']) apply simp  
  apply(rule sep_impl_q_right_antimono) by simp  
   

subsubsection \<open>adjointness of star and magicwand\<close>

text \<open>theorem 3.9\<close>

lemma adjoint_general:
  shows "(\<forall>h. (X **q P) h \<le> Y h) \<longleftrightarrow> (\<forall>h. X h \<le> (P -*qq Y) h)"
proof -    
  (* side condition *)
  let ?sc = "\<lambda>a b. (bot < a \<or> bot < b ) \<and> (a < top \<or> b < top)"

  have le_mult_sc: "\<And>a b c. (?sc a b \<longrightarrow> c \<^bold>* a \<le> b) \<longleftrightarrow> (c \<^bold>* a \<le> b)" 
    by (auto simp: nn nn_bot mult_bot botnottop intro: gt_botI)  

  have "(\<forall> h. X h \<le> (P -*qq Y) h)
       \<longleftrightarrow> (\<forall>h. X h \<le> (INFI {h'. h ## h' \<and> ?sc (P h') (Y (h+h')) } (\<lambda>h'. Y (h + h') \<^bold>div P h')))" 
    unfolding sep_impl_qq_def by simp  
  also have "... \<longleftrightarrow> (\<forall>h h'. h ## h' \<longrightarrow> ?sc (P h') (Y (h+h')) \<longrightarrow> X h \<le> Y (h + h') \<^bold>div P h')" 
    by (auto simp: le_INF_iff)
  also have "... \<longleftrightarrow>  (\<forall>h h'. h ## h' \<longrightarrow> ?sc (P h') (Y (h+h')) \<longrightarrow> X h \<^bold>* P h' \<le> Y (h + h'))"
    using div_mult_adjoint by auto 
  also have "... \<longleftrightarrow> (\<forall>a b. a ## b \<longrightarrow> X a \<^bold>* P b \<le> Y (a + b))" 
    by(auto simp: le_mult_sc)
  also have "... \<longleftrightarrow> (\<forall>h. ((\<lambda>h. SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda> (x, y). X x \<^bold>* P y)) h \<le> Y h))" 
    by (simp add: SUP_le_iff)
  also have "... \<longleftrightarrow> (\<forall>h. (X **q P) h \<le> Y h)"
    unfolding sep_conj_q_alt  by simp
  finally show ?thesis by simp
qed
  
lemma adjoint: "(\<forall>h. (X **q (emb P)) h \<le> Y h) \<longleftrightarrow> (\<forall>h. X h \<le> (P -*q Y) h)"
  using adjoint_general by blast

subsubsection \<open>quantitative modus ponens\<close>

text \<open>theorem 3.8\<close>

lemma quant_modus_ponens:
  "( (emb P) **q (P -*q X)) h \<le> X h"
proof -
  have " (P -*q X) h \<le> (P -*q X) h" by simp
  then have "(((P -*q X) **q emb P) h \<le> X h)"
    using adjoint[symmetric, where X="(P -*q X)" and Y=X] by auto
  then show ?thesis apply(subst star_comm) .
qed

lemma quant_modus_ponens_general:
  shows "( P **q (P -*qq X)) h \<le> X h"
proof -
  have " (P -*qq X) h \<le> (P -*qq X) h" by simp
  then have "(((P -*qq X) **q  P) h \<le> X h)"
    using adjoint_general[symmetric, where X="(P -*qq X)" and Y=X]  by auto
  then show ?thesis apply(subst star_comm) .
qed 

subsection \<open>Intuitionistic Expectations\<close>

text \<open>In SL, a predicate @{term \<phi>} is called @{term intuitionistic}, iff for all @{term h} and 
 @{term h'} with @{term "h \<preceq> h'"} , @{term "\<phi> h"} implies @{term "\<phi> h'"}.\<close>

term "intuitionistic"
term "sep_true"

definition intuitionistic_q :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "intuitionistic_q P = (\<forall>h h'. h \<preceq> h' \<longrightarrow> P h \<le> P h')"

lemma intuitionistic_q_emb_intuitionistic_iff: 
  "intuitionistic_q (emb P) \<longleftrightarrow> intuitionistic P"
  unfolding intuitionistic_q_def intuitionistic_def emb_def
  using bot_not_neutral less_le_not_le by fastforce     

lemma intuitionistic_qI:
  "(\<And>h h'. h \<preceq> h' \<Longrightarrow> P h \<le> P h') \<Longrightarrow> intuitionistic_q P"
  by (unfold intuitionistic_q_def, fast)

lemma intuitionistic_qI2:
  "(\<And>h h'. h ## h' \<Longrightarrow> P h \<le> P (h + h')) \<Longrightarrow> intuitionistic_q P"
  apply (unfold intuitionistic_q_def sep_substate_def)
  by auto 

lemma intuitionistic_qD:
  "intuitionistic_q X \<Longrightarrow>  h ## z \<Longrightarrow> h' = h + z \<Longrightarrow> X h \<le> X h' "
  by (unfold intuitionistic_q_def sep_substate_def, auto)

lemma intuitionistic_q_is_attained_at_h: 
  fixes
    X :: "_ \<Rightarrow> 'b"
  assumes "intuitionistic_q X"
  shows "(SUPR {(x, y) |x y. h = x + y \<and> x ## y} (\<lambda>(h1, h2). X h1)) = X h"
  apply(rule antisym)
  subgoal 
    apply(rule SUP_least) using assms by(auto dest: intuitionistic_qD)
  subgoal 
    apply(rule SUP_upper2[where i="(h,0)"]) by auto
  done

text \<open>Tightest intuitionistic expectations\<close>

abbreviation sep_true_q ("1\<^sub>q")  where "1\<^sub>q \<equiv> (emb sep_true)"

theorem tightest_intuitionistic_expectations_star:
  fixes X :: "'a \<Rightarrow> 'b"
  shows
    "intuitionistic_q (X **q 1\<^sub>q)"
    "\<And>h. X h \<le> (X **q 1\<^sub>q) h"
    "\<And>X' h. intuitionistic_q X' \<Longrightarrow> (\<And>h. X h \<le> X' h) \<Longrightarrow> (X **q 1\<^sub>q) h \<le> X' h"
proof -
  show "intuitionistic_q (X **q 1\<^sub>q)" 
  proof (rule intuitionistic_qI2)
    fix h h' :: 'a
    assume *: "h ## h'" 
    have "(X **q 1\<^sub>q) h = (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>(h1, h2). X h1 \<^bold>* 1\<^sub>q h2))" 
      unfolding sep_conj_q_alt by simp
    also have "\<dots> = (SUPR {(x, y). h = x + y \<and> x ## y} (\<lambda>(h1, h2). X h1 \<^bold>* 1\<^sub>q (h2+h')))"
      by (auto simp: emb_def)
    also have "\<dots> \<le> (SUPR {(x, y). h + h' = x + y \<and> x ## y} (\<lambda>(h1, h2). X h1 \<^bold>* 1\<^sub>q h2))"
      apply(rule SUP_mono) apply safe
      subgoal for h1 h2 apply(rule bexI[where x="(h1,h2 + h')"])  
        using * by (auto simp: sep_add_assoc dest: sep_add_disjD intro: sep_disj_addI3)
      done
    also have "\<dots> = (X **q 1\<^sub>q) (h + h')" 
      unfolding sep_conj_q_alt by simp
    finally show "(X **q 1\<^sub>q) h \<le> (X **q 1\<^sub>q) (h + h')" .
  qed
next
  fix h 
  have "X h \<le> (SUPR {(x, y) |x y. h = x + y \<and> x ## y} (\<lambda> (x, y). X x \<^bold>* emb (\<lambda>s. True) y))"
    by (rule Sup_upper) (auto intro!: image_eqI[where x="(h,0)"] simp: emb_def)   
  also have "\<dots> = (X **q 1\<^sub>q) h"
    unfolding sep_conj_q_SUP by simp
  finally show "X h \<le> (X **q 1\<^sub>q) h" . 
next
  fix X'
  assume "intuitionistic_q X'" and Xmono: "\<And>h. X h \<le> X' h" 
    fix h
    have "(X **q 1\<^sub>q) h \<le> (X' **q 1\<^sub>q) h"
      using sep_conj_q_mono[OF Xmono] by fast
    also have "\<dots> = (SUPR {(x, y) |x y. h = x + y \<and> x ## y} (\<lambda>(x, y). X' x \<^bold>*  1\<^sub>q y))"
      unfolding sep_conj_q_SUP by simp
    also have "\<dots> = (SUPR {(x, y) |x y. h = x + y \<and> x ## y} (\<lambda>(x, y). X' x))"
      by (auto simp add: emb_def)
    also have "\<dots> = X' h" 
      apply(rule intuitionistic_q_is_attained_at_h) by fact
    finally show "(X **q 1\<^sub>q) h \<le> X' h" . 
qed

lemma intuitionistic_q_is_attained_at_h_wand: 
  fixes
    X :: "_ \<Rightarrow> 'b"
  assumes "intuitionistic_q X"
  shows "X h = (INFI {h'. h ## h' \<and> (\<^bold>1 < top \<or> X (h + h') < top) } (\<lambda>h'. X (h + h')) )"
  apply(rule antisym)
  subgoal 
    apply(rule Inf_greatest) using assms by(auto dest: intuitionistic_qD)
  subgoal 
    apply(cases "X h<top")
    subgoal apply(rule INF_lower2[where i=0])  by auto
    subgoal by(auto simp: nn)
    done
  done

lemma tightest_intuitionistic_expectations_wand_general:
  fixes X :: "'a \<Rightarrow> 'b"
  shows
    "intuitionistic_q (1\<^sub>q -*qq X)" 
    "\<And>h. (1\<^sub>q -*qq X) h \<le> X h"
    "\<And>X' h. intuitionistic_q X' \<Longrightarrow> (\<And>h. X' h \<le> X h) \<Longrightarrow>  X' h \<le> (1\<^sub>q -*qq X) h"
proof -
  (* side condition *)
  let ?sc = "\<lambda>a b. (bot < a \<or> bot < b ) \<and> (a < top \<or> b < top)"
  show 1: "intuitionistic_q (1\<^sub>q -*qq X)"
  proof (rule intuitionistic_qI2)
    fix h h' :: 'a
    assume *: "h ## h'"
    have "(1\<^sub>q -*qq X) h = (INFI {h'. h ## h' \<and> ?sc (emb (\<lambda>s. True) h') (X (h + h')) }
                                (\<lambda>h'. X (h + h') \<^bold>div emb (\<lambda>s. True) h'))" 
      unfolding sep_impl_qq_def  by simp
    also have "\<dots> \<le> (INFI {h'a. h + h' ## h'a \<and> ?sc (emb (\<lambda>s. True) h'a) (X (h + h'+ h'a))}
                          (\<lambda>h'a. X (h + h' + h'a) \<^bold>div emb (\<lambda>s. True) h'a))" 
      apply(rule INF_mono)
      subgoal for h'' apply(rule bexI[where x="h' + h''"])
        using * bot_not_neutral
        by (auto simp: sep_disj_addI3 emb_def sep_add_assoc dest: sep_add_disjD)
      done
    also have "\<dots> = (1\<^sub>q -*qq X) (h + h')" 
      unfolding sep_impl_qq_def  by simp
    finally show "(1\<^sub>q -*qq X) h \<le> (1\<^sub>q -*qq X) (h + h')" .
  qed
next
  fix h 
  have "(1\<^sub>q -*qq X) h = (INFI {h'. h ## h' \<and> (bot < emb (\<lambda>s. True) h' \<or> bot < X (h + h'))
                                 \<and> (emb (\<lambda>s. True) h' < top \<or> X (h + h') < top)}
                              (\<lambda>h'. X (h + h') \<^bold>div emb (\<lambda>s. True) h'))"
    unfolding sep_impl_qq_def by simp   
  also have "\<dots> \<le> X h"
    apply(cases "X h<top")
    subgoal by (rule INF_lower2[where i=0]) (auto simp: bot_not_neutral emb_def divide_neutral)
    subgoal by (auto simp: nn)
    done
  finally show "(1\<^sub>q -*qq X) h \<le> X h" . 
next
  fix X'
  assume "intuitionistic_q X'" and Xmono: "\<And>h. X' h \<le> X h" 
  fix h (* for arbitrary but fixed h *)
  have "X' h = (INFI {h'. h ## h' \<and> (\<^bold>1 < top \<or> X' (h + h') < top) } (\<lambda>h'. X' (h + h')) )"
    apply(rule intuitionistic_q_is_attained_at_h_wand) by fact
  also have "\<dots> = (INFI {h'. h ## h' \<and> (bot < emb (\<lambda>s. True) h' \<or> bot < X' (h + h'))
                         \<and> (emb (\<lambda>s. True) h' < top \<or> X' (h + h') < top)}
                        (\<lambda>h'. X' (h + h') \<^bold>div emb (\<lambda>s. True) h'))"
    using bot_not_neutral by (auto simp: emb_def divide_neutral ) 
  also have "\<dots> = (1\<^sub>q -*qq X') h"
    unfolding sep_impl_qq_def by simp
  also have "\<dots> \<le> (1\<^sub>q -*qq X) h" 
    apply(rule sep_impl_q_left_mono') by fact
  finally show "X' h \<le> (1\<^sub>q -*qq X) h" . 
qed




lemma tightest_intuitionistic_expectations_wand:
  fixes X :: "'a \<Rightarrow> 'b"
  shows
    "intuitionistic_q (sep_true -*q X)" 
    "\<And>h. (sep_true -*q X) h \<le> X h"
    "\<And>X' h. intuitionistic_q X' \<Longrightarrow> (\<And>h. X' h \<le> X h) \<Longrightarrow>  X' h \<le> (sep_true -*q X) h"
  using tightest_intuitionistic_expectations_wand_general by auto

abbreviation (input)
  pred_ex_q :: "('b \<Rightarrow> 'a \<Rightarrow> ennreal) \<Rightarrow> 'a \<Rightarrow> ennreal" (binder "EXSq " 10) where
  "EXSq x. P x \<equiv> \<lambda>h. SUP x. P x h"


end
end

section \<open>Showing that quantitative separating connectives
   instantiated for bool yield the boolean separating connectives\<close>

instantiation "bool" :: one
begin
definition "one_bool == True"
instance by standard
end 

interpretation BOOL: quant_sep_con Inf Sup inf "(\<le>)" "(<)" sup bot top
      "(\<and>)" "True" "\<lambda>x y. y \<longrightarrow> x"
  unfolding quant_sep_con_def comm_quantale_def apply safe
  subgoal by standard  
  subgoal apply standard by auto 
  subgoal apply standard by auto
  subgoal apply standard by auto 
  done

thm BOOL.oper_left_mono

lemma "BOOL.sep_conj_q = sep_conj"
  apply(rule ext) apply (rule ext)
  unfolding sep_conj_def BOOL.sep_conj_q_def
  by auto

lemma "BOOL.sep_impl_qq = sep_impl"
  apply(rule ext) apply (rule ext)
  unfolding sep_impl_def BOOL.sep_impl_qq_def
  by auto

lemma "BOOL.intuitionistic_q = intuitionistic"
  apply(rule ext)  
  unfolding intuitionistic_def BOOL.intuitionistic_q_def
  by auto

lemma "BOOL.sep_impl_qq = BOOL.sep_impl_q"
  unfolding BOOL.sep_impl_qq_def BOOL.emb_def by auto



section \<open>Extensions\<close>




subsection \<open>The Locale quant_sep_con_one\<close>

text \<open>A locale assuming, that the neutral element is also the top element.
      (Bool,<=,and), ([0;1],<=,*) and (ennreal,>=,+) are three examples.
      (ennreal,<=,*) isn't.  \<close>

locale quant_sep_con_one = quant_sep_con Inf Sup inf le less sup bot top oper neutr divide
  for Inf :: "'b set \<Rightarrow> 'b"
    and Sup inf
    and le (infix "\<le>" 50)
    and less (infix "<" 50)
    and sup top bot
    and oper :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>*" 64)
    and divide :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>div" 64)
    and neutr :: "'b" ("\<^bold>1")
    +
  assumes neutral_is_top: "\<^bold>1 = top"
    and CC: "bot < (top::'b)"  
begin 

context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin

lemma sep_impl_q_alt_general'':
  fixes  Q :: "'a \<Rightarrow> 'b" 
  shows "(P -*q Q) = (\<lambda>h. INFI { h'. h ## h' \<and> P h'} (\<lambda> h'. Q (h + h')))"
  using sep_impl_q_alt_general neutral_is_top by auto

lemma sep_impl_q_alt_general''':
  fixes  Q :: "'a \<Rightarrow> 'b" 
  shows "(P -*q Q) = (\<lambda>h. INFI { h'. h ## h' \<and> P h'} (\<lambda>h'. Q (h + h')))"
proof  (rule ext)
  fix h
  let ?A ="{h'. h ## h' \<and> (bot::'b) < emb P h' \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}"
  let ?C = " {h'. h ## h' \<and>(bot::'b) = emb P h' \<and> (bot::'b) < Q (h + h')
                   \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}"
  let ?B ="{h'.  h ## h'   \<and> Q (h + h') < top \<and> P h'}"
  have T: "{h'. h ## h' \<and> ((bot::'b) < emb P h' \<or> (bot::'b) < Q (h + h'))
               \<and> (emb P h' < (top::'b) \<or> Q (h + h') < (top::'b))}
            = ?A \<union> ?C" 
    using bot.not_eq_extremum by fastforce    

  have 1: "(INFI ?A (\<lambda>h'. Q (h + h') \<^bold>div emb P h')) = (INFI ?B (\<lambda>x. Q (h + x)))"
    apply(rule INF_cong)
    subgoal
      apply rule 
      subgoal (* ?A \<subseteq> ?B *)
        by (auto simp: divide_neutral emb_def CC bot_not_neutral neutral_is_top[symmetric]) 
      subgoal (* ?B \<subseteq> ?A *)
        by (auto simp: divide_neutral emb_def CC bot_not_neutral)
      done
    subgoal by (simp add: divide_neutral emb_def)  
    done 

  have 2: "(INFI ?C (\<lambda>h'. Q (h + h') \<^bold>div emb P h')) = top" 
    unfolding emb_def apply auto 
    using divide_bot by simp_all    

  have F: "{ h'. h ## h' \<and> P h'}
     = { h'. h ## h' \<and> P h' \<and> Q (h + h') = top} \<union> { h'. h ## h' \<and> P h' \<and> Q (h + h') < top}"
    using top.not_eq_extremum by blast

  have 3: "(INFI {h'. h ## h' \<and> P h' \<and> Q (h + h') = top} (\<lambda>h'. Q (h + h'))) = top"
    by auto

  have "(P -*q Q) h = inf (INFI ?A (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))
                        (INFI ?C (\<lambda>h'. Q (h + h') \<^bold>div emb P h'))"
    unfolding sep_impl_qq_def T INF_union
    by simp
  also have "\<dots>  = (INFI ?B (\<lambda>x. Q (h + x)))"
    unfolding 1 2 by simp
  also have "\<dots> = (INFI { h'. h ## h' \<and> P h'} (\<lambda>h'. Q (h + h')))"
    unfolding F INF_union 3
    by (auto intro: INF_cong)
  finally show "(P -*q Q) h = (INFI {h'. h ## h' \<and> P h'} (\<lambda>h'. Q (h + h')))" .
qed

end
end
  
  (*

subsection \<open>The Locale quant_sep_con_oper2\<close>

text \<open>Allowing a second operation on the measuring type.\<close>

locale quant_sep_con_oper2 =  quant_sep_con oper neutr divide
  for  
    oper :: "'b::{complete_lattice} \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>*" 70)
    and neutr :: "'b" ("\<^bold>1") 
    and divide :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixl "\<^bold>div" 70) +
  fixes
    oper2 :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<^bold>+" 65)
  assumes
    plusmal_distrib[algebra_simps]: "\<And>a b c. a \<^bold>* (b \<^bold>+ c) = a \<^bold>* b \<^bold>+ a \<^bold>* c"
    and oper2_mono: "\<And>a b c d. a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a \<^bold>+ c \<le> b \<^bold>+ d"
begin


lemma SUP_plus_subdistrib: "\<And>S. \<And>f g::_\<Rightarrow>'b. (SUP x:S. f x \<^bold>+ g x) \<le> (SUP x:S. f x) \<^bold>+ (SUP x:S. g x)"
  by (simp add: SUP_least SUP_upper oper2_mono)

context
  assumes "SORT_CONSTRAINT ('a::{sep_algebra})" 
begin

lemma theorem_3_6_general2: 
  fixes
    P :: "_ \<Rightarrow> 'b"  
  shows
    "((P **q (\<lambda>h. Q h \<^bold>+ R h)) h) \<le> ((P **q Q) h) \<^bold>+ ((P **q R) h)"
proof -
  have "(P **q (\<lambda>h. Q h \<^bold>+ R h)) h = (SUP (x,y):{(x,y)|x y. h = x + y \<and> x ## y}. (P x \<^bold>* Q y) \<^bold>+ (P x \<^bold>* R y) )"
    unfolding sep_conj_q_alt  by (simp add: plusmal_distrib) 
  also have "\<dots> = (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. (P (fst x) \<^bold>* Q (snd x))  \<^bold>+ (P (fst x) \<^bold>* R (snd x)) )"
    apply(rule Sup_cong) by force    
  also have "\<dots> \<le> (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x)  \<^bold>* Q (snd x) )
                   \<^bold>+ (SUP x:{(x,y)|x y. h = x + y \<and> x ## y}. P (fst x)  \<^bold>* R (snd x) )" 
    by (rule SUP_plus_subdistrib)
  also have "\<dots> = ((P **q Q) h)  \<^bold>+ ((P **q R) h)"
    unfolding sep_conj_q_alt apply simp     
    by (metis (mono_tags, lifting) SUP_cong prod.case_eq_if)  
  finally show "((P **q (\<lambda>h. Q h \<^bold>+ R h)) h) \<le> ((P **q Q) h) \<^bold>+ ((P **q R) h)" .
qed

end
end*)



end