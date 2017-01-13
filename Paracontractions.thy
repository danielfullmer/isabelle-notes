theory Paracontractions
imports
  Main Limits
  "~~/src/HOL/Library/Convex"
  "~~/src/HOL/Multivariate_Analysis/Topology_Euclidean_Space"
begin

abbreviation F :: "('a::real_vector \<Rightarrow> 'a::real_vector) \<Rightarrow> 'a::real_vector set" where
"F(f) \<equiv> {x. f(x) = x}"

definition "qne f \<longleftrightarrow>
((\<exists> x. f x = x) \<and> (\<forall>x y. (f y = y) \<longrightarrow> (norm (f x - y) \<le> norm (x - y))))"

definition "paracontraction f \<longleftrightarrow>
((\<exists>x. f x = x) \<and> (\<forall>x y. (f x \<noteq> x \<and> f y = y) \<longrightarrow> (norm (f x - y) < norm (x - y))))"

lemma paracontractionI:
  assumes "\<exists>x. f x = x"
  assumes "\<And>x y. f x \<noteq> x \<Longrightarrow> f y = y \<Longrightarrow> (norm (f x - y) < norm (x - y))"
  shows "paracontraction f"
by (simp add: assms paracontraction_def)

lemma paracontractionE:
  assumes "paracontraction f"
  shows "\<exists>z. f z = z" and "\<And>x y. f x \<noteq> x \<Longrightarrow> f y = y \<Longrightarrow> (norm (f x - y) < norm (x - y))"
using assms paracontraction_def apply auto[1]
using assms paracontraction_def by blast

lemma pc_qne:
  assumes "paracontraction f"
  shows "f y = y \<Longrightarrow> norm (f x - y) \<le> norm (x - y)"
by (metis assms le_less_linear less_imp_le paracontraction_def)

lemma pc_norm_eq_impl_fp:
  assumes "paracontraction f"
  assumes "f y = y"
  assumes n: "norm (f x - y) = norm (x - y)"
  shows "f x = x"
proof (rule ccontr)
  assume "f x \<noteq> x"
  hence "norm (f x - y) < norm (x - y)" using assms paracontractionE by blast
  thus "False" using assms by auto
qed

(* Composition of pc intersects fixed points *)
lemma pc_comp_intersect_fp:
  assumes f_g_pc: "paracontraction f" "paracontraction g"
  assumes ex_cfp: "\<exists> x. f x = x \<and> g x = x"
  shows "F(f o g) = F(f) \<inter> F(g)"
proof
  show "F (f) \<inter> F(g) \<subseteq> F(f o g)" using comp_def by auto
(*
proof
  assume "f x = x \<and> g x = x"
  hence "(f o g) x = x" by simp
  then have "?thesis" by auto
  qed
*)
next
  show "F(f o g) \<subseteq> F(f) \<inter> F(g)"
  proof
    fix x
    assume x_fp: "x \<in> F(f o g)"
    obtain y where y_cfp: "f y = y \<and> g y = y" using ex_cfp by auto
  
    have x_fp_g: "g x = x \<and> f (g x) = g x"
    proof (rule ccontr)
      assume "\<not> (g x = x \<and> f (g x) = g x)"
      hence "g x \<noteq> x \<or> f (g x) \<noteq> g x" by simp
      hence "norm (f (g x) - y) < norm (x - y)"
      proof
        assume "g x \<noteq> x"
        from this f_g_pc y_cfp have "norm (g x - y) < norm (x - y)"
          by (simp add: paracontraction_def)
        moreover have "norm (f (g x) - y) \<le> norm (g x - y)" using f_g_pc y_cfp pc_qne by auto
        ultimately show "?thesis" by simp
      next
        assume "f (g x) \<noteq> g x"
        from this f_g_pc y_cfp have "norm (f (g x) - y) < norm (g x - y)"
          by (simp add: paracontraction_def)
        moreover have "norm ((g x) - y) \<le> norm (x - y)" using f_g_pc y_cfp pc_qne by auto
        ultimately show "?thesis" by simp
      qed
      moreover have "x = f (g x)" using x_fp by simp
      ultimately have "norm x < norm x" by simp
      thus "False" by simp
    qed
    hence x_fp_f: "f x = x" by auto
    from x_fp_f x_fp_g show "x \<in> F(f) \<inter> F(g)" by simp
  qed
qed

(* Unsure if this is necessary to have.
 * Maybe the original theorem should be stated this way *)
(*
lemma pc_comp_intersect_fp2:
  assumes f_g_pc: "paracontraction f" "paracontraction g"
  assumes ex_cfp: "\<exists> x. f x = x \<and> g x = x"
  shows "(f o g) x = x \<longleftrightarrow> f x = x \<and> g x = x"
using assms pc_comp_intersect_fp by auto
*)

(* Composition of pc is pc *)
lemma pc_closed_comp:
  assumes f_g_pc: "paracontraction f" "paracontraction g"
  assumes ex_cfp: "\<exists> x. f x = x \<and> g x = x"
  shows "paracontraction (f o g)"
  unfolding paracontraction_def
proof (* Figure out an initial proof method for paracontractions. e.g.6 Introduction rules. *)
  show "\<exists>x. (f o g) x = x"
    using ex_cfp by (metis comp_apply)
    (* NOTE: We don't even need pc_comp_intersect_fp *)
next
  show  "\<forall>x y. ((f o g) x \<noteq> x) \<and> ((f o g) y = y) \<longrightarrow> norm ((f o g) x - y) < norm (x - y)"
  apply (auto) (* Make goals be correct. TODO: Look up the right way to do this in isar.
                * See isar-ref, Sec 2.3.6 *)
  proof -
    fix x y
    assume x_nfp: "f (g x) \<noteq> x"
    assume y_fp: "f (g y) = y"

    have y_cfp: "f y = y \<and> g y = y"
      using assms y_fp pc_comp_intersect_fp by auto
    moreover have x_or_nfp: "f x \<noteq> x \<or> g x \<noteq> x"
      using x_nfp f_g_pc pc_comp_intersect_fp by auto
    ultimately have "norm (f (g x) - y) < norm (g x - y) \<or> norm (g x - y) < norm (x - y)"
      using paracontraction_def f_g_pc  by metis
    thus "norm (f (g x) - y) < norm (x - y)" using f_g_pc y_cfp pc_qne by smt
  qed
qed

(* Fixed points of pc is convex *)
lemma pc_fp_convex:
  assumes "paracontraction f"
  shows "convex (F(f))"
unfolding convex_alt
apply(auto) (* TODO: Figure out how to do this in isar *)
proof -
  fix x y
  fix u :: real
  assume x_y_fp: "f x = x" "f y = y"
  assume u_bound: "0 \<le> u" "u \<le> 1"
  def z \<equiv> "(1 - u) *\<^sub>R x + u *\<^sub>R y"
  have "z \<in> F f" (* This is the meat of it *)
  proof (rule ccontr)
    assume z_not_fp: "z \<notin> F f"
    have "norm (x - y) \<le> norm(f z - x) + norm(f z - y)"
      using norm_diff_triangle_le norm_imp_pos_and_ge norm_minus_commute by blast
    moreover have "norm(f z - x) < norm(z - x)" "norm(f z - y) < norm(z - y)"
      using assms paracontractionE x_y_fp z_not_fp mem_Collect_eq by auto
    hence "norm (x - y) < norm(z - x) + norm(z - y)"
      using paracontraction_def x_y_fp using calculation by linarith
    moreover have "norm(z-x) = u * norm(x-y)"
      apply (simp add: z_def algebra_simps)
      apply (smt norm_minus_commute norm_scaleR real_vector.scale_right_diff_distrib u_bound(1))
      done
    moreover have "norm(z-y) = (1-u) * norm(x-y)"
      proof -
        have "norm(z-y) = norm((1-u) *\<^sub>R (x-y))"
          by (simp add: z_def algebra_simps)
        thus "?thesis" using norm_scaleR u_bound(2) by auto
      qed
    ultimately have "norm (x - y) < norm(x-y)"
      by (metis add.commute diff_add_cancel distrib_right mult.left_neutral)
    thus "False" by simp
  qed
  thus "f ((1 - u) *\<^sub>R x + u *\<^sub>R y) = (1 - u) *\<^sub>R x + u *\<^sub>R y" using z_def by simp
qed

lemma pc_fejer_monotone:
  assumes "paracontraction f"
  assumes "f y = y"
  shows "norm ((f^^n) x - y) \<le> norm (x-y)"
apply(induction n)
apply(auto)
by (metis (full_types) assms le_less_trans linear not_le paracontractionE(2))

lemma pc_fejer_monotone2:
  assumes "paracontraction f"
  assumes "f y = y"
  shows "norm ((f^^(m+n)) x - y) \<le> norm ((f^^m) x - y)"
proof (induction n)
  show "norm ((f^^(m + 0)) x - y) \<le> norm ((f ^^ m) x - y)" by auto
next
  fix n
  assume induct_hyp: "norm ((f^^(m + n)) x - y) \<le> norm ((f^^m) x - y)"
  have "norm ((f ^^ (m + Suc n)) x - y) \<le> norm ((f^^(m + n)) x - y)" using assms pc_qne by simp
  thus "norm ((f ^^ (m + Suc n)) x - y) \<le> norm ((f ^^ m) x - y)" using le_trans induct_hyp by simp
qed

lemma pc_fejer_monotone3:
  assumes "paracontraction f"
  assumes "f y = y"
  assumes "m\<le>n"
  shows "norm ((f^^n) x - y) \<le> norm ((f^^m) x - y)"
using assms pc_fejer_monotone2 le_iff_add by auto

(* Replace this using facts about fejer monotone sequences *)
theorem pc_convergent:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes f_pc: "paracontraction f"
  (* assumes "continuous f" *)
  shows "\<exists>z\<in>F(f). ((\<lambda>n. (f^^n) x) \<longlonglongrightarrow> z)"
proof
fix x
have "\<exists>y. f y = y" using f_pc paracontractionE by auto
from this obtain y where y_fp: "f y = y"  by auto

def ns \<equiv> "\<lambda>n. (norm ((f^^n) x - y))"
def xs \<equiv> "\<lambda>n. (f^^n) x"

(* norm sequence converges *)
have "decseq ns"
  by (simp add: decseq_def ns_def f_pc y_fp pc_fejer_monotone3)
then obtain d where ns_to_d: "ns \<longlonglongrightarrow> d"
  by (metis decseq_convergent norm_ge_zero ns_def)

(* xs has convergent subsequence *)
have "Bseq xs" (* Interestingly, *)
proof -
  have  "\<And>n. norm((f^^n) x) \<le> norm y + norm ((f^^n) x - y)" using norm_triangle_sub by auto
  moreover have "\<And>n. norm((f^^n) x - y) \<le> norm (x - y)" using f_pc y_fp pc_fejer_monotone by auto
  finally have  "\<And>n. norm((f^^n) x) \<le> norm y + norm (x - y)" using le_trans by auto
  thus "?thesis" using BseqI' xs_def by metis
qed
hence "seq_compact (range xs)" 
hence "bounded (range xs)"
using Bseq_def bounded_def
Bseq_eq_bounded
sledgehammer
(*bounded_closed_imp_seq_compact*)
hence "seq_compact {(f^^n) x | n \<ge> 0}"
from this obtain r z where "subseq r" "(xs o r) \<longlonglongrightarrow> z"
  by (metis bounded_seq_has_conv_subseq)

(* z is a limit point *)
moreover have "f z = z"
proof -
  have "(\<lambda>n. norm (f ((xs o r) n) - y)) \<longlonglongrightarrow> d"

thus "\<exists>z. (comp_power f x) \<longlonglongrightarrow> z"


(* Bounded sequence has convergent subsequence *)
theorem bounded_seq_has_conv_subseq:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space"
  assumes "Bseq f"
  obtains l r where "l \<in> S" "subseq r" "((f \<circ> r) \<longlongrightarrow> l) sequentially"
proof -
  have "compact {f^^n x. n \<ge> 0}"
  apply compact_def

lemma compact_def:
  "compact (S :: 'a::metric_space set) \<longleftrightarrow>
   (\<forall>f. (\<forall>n. f n \<in> S) \<longrightarrow> (\<exists>l\<in>S. \<exists>r. subseq r \<and> (f \<circ> r) \<longlonglongrightarrow> l))"
  unfolding compact_eq_seq_compact_metric seq_compact_def by auto

lemma seq_compactE:
  assumes "seq_compact S" "\<forall>n. f n \<in> S"
  obtains l r where "l \<in> S" "subseq r" "((f \<circ> r) \<longlongrightarrow> l) sequentially"

end