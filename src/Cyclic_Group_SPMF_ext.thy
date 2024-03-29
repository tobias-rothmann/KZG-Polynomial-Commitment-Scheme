theory Cyclic_Group_SPMF_ext

imports CryptHOL.Cyclic_Group_SPMF "HOL-Computational_Algebra.Polynomial" 
  Berlekamp_Zassenhaus.Finite_Field Polynomial_Interpolation.Lagrange_Interpolation

begin

hide_const order

subsection \<open>sample_uniform mod ring\<close>

definition sample_uniform_modr :: "'a mod_ring spmf" where
  "sample_uniform_modr = spmf_of_set UNIV"

subsection \<open>sample uniform set\<close>

definition sample_uniform_set :: "nat \<Rightarrow> nat \<Rightarrow> nat set spmf"
  where "sample_uniform_set k n = spmf_of_set {x. x \<subseteq> {..<n} \<and> card x = k}"

lemma spmf_sample_uniform_set: "spmf (sample_uniform_set k n) x 
  = indicator {x. x \<subseteq> {..<n} \<and> card x = k} x / (n choose k)"
  by (simp add: n_subsets sample_uniform_set_def spmf_of_set)

lemma weight_sample_uniform_set: "weight_spmf (sample_uniform_set k n) = of_bool (k\<le>n)"
  apply (auto simp add: sample_uniform_set_def weight_spmf_of_set split: if_splits)
   apply (metis card_lessThan card_mono finite_lessThan)
  using card_lessThan by blast

lemma weight_sample_uniform_set_k_0 [simp]: "weight_spmf (sample_uniform_set 0 n) = 1"
  by (auto simp add: weight_sample_uniform_set)

lemma weight_sample_uniform_set_n_0 [simp]: "weight_spmf (sample_uniform_set k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_uniform_set)

lemma weight_sample_uniform_set_k_le_n [simp]: "k\<le>n \<Longrightarrow> weight_spmf (sample_uniform_set k n) = 1"
  by (auto simp add: weight_sample_uniform_set indicator_def gr0_conv_Suc)

lemma lossless_sample_uniform_set [simp]: "lossless_spmf (sample_uniform_set k n) \<longleftrightarrow> k \<le> n"
  by (auto simp add: lossless_spmf_def weight_sample_uniform_set intro: ccontr)

lemma set_spmf_sample_uniform_set [simp]: "set_spmf (sample_uniform_set k n) = {x. x \<subseteq> {..<n} \<and> card x = k}"
  by(simp add: sample_uniform_set_def)


subsection \<open>sample uniform list\<close>

definition sample_uniform_list :: "nat \<Rightarrow> nat \<Rightarrow> nat list spmf"
  where "sample_uniform_list k n = spmf_of_set {x. set x \<subseteq> {..<n} \<and> length x = k}"

lemma spmf_sample_uniform_list: "spmf (sample_uniform_list k n) x 
  = indicator {x. set x \<subseteq> {..<n} \<and> length x = k} x / (n^k)"
  by (simp add: card_lists_length_eq sample_uniform_list_def spmf_of_set)

lemma weight_sample_uniform_list: "weight_spmf (sample_uniform_list k n) = of_bool (k=0 \<or> 0<n)"
proof -
  have "0 < n \<longrightarrow> (\<exists>x. set x \<subseteq> {..<n} \<and> length x = k)"
  proof
    assume zero_l_n: "0 < n"
    show "\<exists>x. set x \<subseteq> {..<n} \<and> length x = k"
    proof 
      let ?x = "replicate k 0"
      show "set ?x \<subseteq> {..<n} \<and> length ?x = k"
        using zero_l_n by fastforce
    qed
  qed
  then show ?thesis 
    by (simp add: finite_lists_length_eq sample_uniform_list_def weight_spmf_of_set)
qed
  
lemma weight_sample_uniform_list_k_0 [simp]: "weight_spmf (sample_uniform_list 0 n) = 1"
  by (auto simp add: weight_sample_uniform_list)

lemma weight_sample_uniform_list_n_0 [simp]: "weight_spmf (sample_uniform_list k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_uniform_list)

lemma weight_sample_uniform_list_k_le_n [simp]: "k<n \<Longrightarrow> weight_spmf (sample_uniform_list k n) = 1"
  by (auto simp add: weight_sample_uniform_list less_iff_Suc_add)

lemma lossless_sample_uniform_list [simp]: "lossless_spmf (sample_uniform_list k n) \<longleftrightarrow> (k=0 \<or> 0<n)"
  by (auto simp add: lossless_spmf_def weight_sample_uniform_list intro: ccontr)

lemma set_spmf_sample_uniform_list [simp]: "set_spmf (sample_uniform_list k n) = {x. set x \<subseteq> {..<n} \<and> length x = k}"
  by (simp add: finite_lists_length_eq sample_uniform_list_def)

lemma "bind_spmf (spmf_of_set {X}) spmf_of_set = spmf_of_set X"
  by (simp add: spmf_of_set_singleton)

text \<open>the two following lemmas are helping lemmas for Cons_random_list_split\<close>

lemma set_spmf_lhs: "set_spmf (map_spmf ((#) x) (sample_uniform_list k p)) 
             = {xs. set (tl xs) \<subseteq> {..<p} \<and> length xs = k+1 \<and> hd xs = x}"
proof -
  fix x
  have "set_spmf (map_spmf ((#) x) (sample_uniform_list k p)) 
    = ((#) x) ` {xs. set xs \<subseteq> {..<p} \<and> length xs = k}" 
    unfolding sample_uniform_list_def
    by (simp add: finite_lists_length_eq)
  also have "\<dots> = {xs. set (tl xs) \<subseteq> {..<p} \<and> length xs = k+1 \<and> hd xs = x}"
    (* TODO cleanup in case*)
    apply auto
    by (smt (verit) Suc_length_conv image_Collect list.sel(1) list.sel(3) mem_Collect_eq)
  finally show "set_spmf (map_spmf ((#) x) (sample_uniform_list k p)) 
      = {xs. set (tl xs) \<subseteq> {..<p} \<and> length xs = k + 1 \<and> hd xs = x}"
    .
qed

lemma set_spmf_lhs_imp_length_gr_0: "xs \<in> set_spmf (map_spmf ((#) x) (sample_uniform_list k p)) 
  \<Longrightarrow> length xs > 0"
  unfolding set_spmf_lhs by force

lemma Cons_random_list_split: 
  assumes "p>1"
  shows "do {x \<leftarrow> sample_uniform p;
            map_spmf ((#) x) (sample_uniform_list k p)} = sample_uniform_list (k+1) p"
  (is "?lhs = ?rhs")
proof -
  have "\<forall>s. spmf ?lhs s = spmf ?rhs s"
  proof 
    fix s
    have spmf_rhs: "spmf ?rhs s = indicator {x. set x \<subseteq> {..<p} \<and> length x = k+1} s / real p^(k+1)"
      unfolding spmf_sample_uniform_list ..
    have spmf_lhs: "spmf ?lhs s 
        = (\<Sum>x<p. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) 
        / of_nat (card {..<p})"
        unfolding ennreal_spmf_bind
        unfolding sample_uniform_def
        unfolding nn_integral_spmf_of_set
        ..
    show "spmf ?lhs s = spmf ?rhs s"
    proof (cases s)
      case Nil
      have "spmf ?lhs s = 0"
      proof -
        have "\<And>x. spmf (map_spmf ((#) x) (sample_uniform_list k p)) s = 0"
          using set_spmf_lhs set_spmf_lhs_imp_length_gr_0 spmf_eq_0_set_spmf
          unfolding Nil 
          by fast
        then show ?thesis 
         using spmf_lhs by force
      qed
      moreover have "spmf ?rhs s = 0"
        using spmf_rhs 
        unfolding Nil
        by force
      ultimately show ?thesis by presburger
    next
      case (Cons s_hd s_tl)
      then show ?thesis
      proof (cases "s_hd<p")
        case True
        have "spmf ?lhs s
          = (indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^(k+1)))"
        proof - 
          have spmf_is_sum: "spmf ?lhs s = 
              sum (\<lambda>x. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) {..<p} 
              / real (card {..<p})"
                unfolding spmf_lhs
                using ennreal_of_nat_eq_real_of_nat by presburger
          also have "sum (\<lambda>x. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) {..<p}
          = sum (\<lambda>x. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) (({..<p}-{s_hd}) \<union> {s_hd})"
            by (simp add: True insert_absorb)
          also have "\<dots> = sum (\<lambda>x. ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s)) ({..<p}-{s_hd})
            + ennreal (spmf (map_spmf ((#) s_hd) (sample_uniform_list k p)) s)"
            by (metis (no_types, lifting) Un_insert_right add.commute dual_order.refl finite_nat_iff_bounded insert_Diff_single sum.insert_remove sup_bot.right_neutral)
          also have "\<dots> = ennreal (spmf (map_spmf ((#) s_hd) (sample_uniform_list k p)) s)"
          proof -
            have "\<And>x. x \<in> {..<p}-{s_hd} \<longrightarrow> ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s) = 0"
            proof 
              fix x 
              assume "x \<in> {..<p} - {s_hd}"
              then have "x \<noteq> s_hd" by blast
              then show "ennreal (spmf (map_spmf ((#) x) (sample_uniform_list k p)) s) = 0"
                using set_spmf_lhs 
                unfolding Cons 
                by (simp add: spmf_eq_0_set_spmf)
            qed
            then show ?thesis by force
          qed
          also have "\<dots> = ennreal (spmf (sample_uniform_list k p) s_tl)"
            unfolding Cons
            using spmf_map_inj
            by (simp add: spmf_map_inj')
          also have "\<dots> = indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^k)"
            unfolding spmf_sample_uniform_list ..
          finally have "ennreal (spmf ?lhs s) = ennreal ((indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^k))) /  ennreal (real (card {..<p}))"
            by argo
          then have "spmf ?lhs s = (indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^k)) / (real (card {..<p}))"
            using assms(1) divide_ennreal by auto
          also have "\<dots> = (indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^(k+1)))"
            by auto
          finally show ?thesis .
        qed

        moreover have "spmf ?rhs s
          = (indicator {x. set x \<subseteq> {..<p} \<and> length x = k} s_tl / (real p^(k+1)))"
        proof -
          have "(s_hd # s_tl) \<in> {x. set x \<subseteq> {..<p} \<and> length x = k + 1} 
          \<longleftrightarrow> s_tl \<in> {x. set x \<subseteq> {..<p} \<and> length x = k}"
            by (simp add: True)
          then show ?thesis
            unfolding spmf_sample_uniform_list Cons
            by (metis (no_types, lifting) indicator_simps(1) indicator_simps(2))
        qed
        ultimately show ?thesis by presburger
      next
        case False
        have "spmf ?lhs s = 0"
      proof -
        have "\<And>x. x<p \<longrightarrow> spmf (map_spmf ((#) x) (sample_uniform_list k p)) s = 0"
          unfolding Cons 
          using set_spmf_lhs spmf_eq_0_set_spmf False
          by fastforce
        then show ?thesis
         using spmf_lhs by force
      qed
      moreover have "spmf ?rhs s = 0"
        using spmf_rhs 
        unfolding Cons
        using False
        by fastforce
      ultimately show ?thesis by presburger
      qed
    qed
  qed
  then show ?thesis
    using spmf_eqI by blast
qed

corollary pretty_Cons_random_list_split: 
  assumes "p>1"
  shows "sample_uniform_list (k+1) p =
    do {x \<leftarrow> sample_uniform p;
        xs \<leftarrow> (sample_uniform_list k p);
        return_spmf (x#xs)}"
  (is "?lhs = ?rhs")
proof -
  have "?rhs = do {x \<leftarrow> sample_uniform p;
          map_spmf ((#) x) (sample_uniform_list k p)}"
    by (simp add: map_spmf_conv_bind_spmf)
  then show ?thesis 
    using Cons_random_list_split[symmetric, OF assms]
    by presburger
qed

subsection \<open>sample uniform polynomial\<close>

definition sample_uniform_poly :: "nat \<Rightarrow> 'a::zero poly spmf" 
  where "sample_uniform_poly t = spmf_of_set {p. degree p = t}"

lemma sample_uniform_evals_is_sample_poly:
  assumes "distinct I"
  shows "(sample_uniform_poly t::'e mod_ring poly spmf) = do {
      evals::('e::prime_card) mod_ring list \<leftarrow> map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list (t+1) (CARD ('e)));
      return_spmf (lagrange_interpolation_poly (zip I evals))}"
  (is "?lhs = ?rhs")
proof -
  have "?rhs = do {
      evals \<leftarrow> spmf_of_set {x::'e mod_ring list. length x = t + 1};
      return_spmf (lagrange_interpolation_poly (zip I evals))}"
  proof - 
    have "map_spmf (map (of_int_mod_ring \<circ> int)) (sample_uniform_list (t + 1) CARD('e))
    = spmf_of_set {x::'e mod_ring list. length x = t + 1}"
    (is "?map = ?set")
    proof (rule spmf_eqI)
      fix i :: "'e mod_ring list"
      obtain nat_i where "i = map (of_int_mod_ring \<circ> int) nat_i" sorry
      show "spmf ?map i = spmf ?set i"
        unfolding sample_uniform_list_def
        
        sorry
    qed
    then show ?thesis by metis
  qed
  also have "\<dots> =  do {
      evals \<leftarrow> spmf_of_set {x::'e mod_ring list. length x = t + 1};
      let \<phi> = lagrange_interpolation_poly (zip I evals);
      return_spmf \<phi>}" unfolding Let_def ..
  also have "\<dots> = map_spmf (\<lambda>evals. lagrange_interpolation_poly (zip I evals)) 
                         (spmf_of_set {x::'e mod_ring list. length x = t + 1})"
    by (simp add: map_spmf_conv_bind_spmf)
  also have "\<dots> = spmf_of_set {}"
    (is "?map = ?set")
  proof (rule spmf_eqI)
    fix i 
    show "spmf ?map i = spmf ?set i"
    
      sorry
  qed
    
  show ?thesis
    sorry
qed



subsection \<open>sample distinct uniform list\<close>  

definition sample_distinct_uniform_list :: "nat \<Rightarrow> nat \<Rightarrow> nat list spmf"
  where "sample_distinct_uniform_list k n 
          = spmf_of_set {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}}" 
  
lemma spmf_sample_distinct_uniform_list: 
"spmf (sample_distinct_uniform_list k n) x
  = indicator {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} x / real (\<Prod>{n - k + 1..n})"
proof -
  have "spmf (sample_distinct_uniform_list k n) x 
  = indicat_real {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} x /
    real (card {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}})"
    unfolding sample_distinct_uniform_list_def spmf_of_set ..
  also have "\<dots> = indicat_real {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} x /
    real (\<Prod>{card {..<n} - k + 1..card {..<n}})"
  proof (cases "k \<le> card {..<n}")
    case True
    then show ?thesis
      using card_lists_distinct_length_eq[of "{..<n}" k]
      by fastforce
  next
    case False
    then have "{xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} = {}"
      by (smt (verit, del_insts) card_mono distinct_card empty_Collect_eq finite_lessThan)
    then show ?thesis
      by fastforce
  qed
  also have "\<dots> = indicator {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} x 
                  / real (\<Prod>{n - k + 1..n})"
    by simp
  finally show ?thesis .
qed

lemma weight_sample_distinct_uniform_list: "weight_spmf (sample_distinct_uniform_list k n) = of_bool (k\<le>n)"
  apply (auto simp add: sample_distinct_uniform_list_def weight_spmf_of_set split: split_indicator)
   apply (metis atLeast0LessThan distinct_card subset_eq_atLeast0_lessThan_card)
  apply (metis atLeast0LessThan card_atLeastLessThan diff_zero distinct_card distinct_upt lessThan_subset_iff set_upt)
  done

lemma weight_sample_distinct_uniform_list_k_0 [simp]: "weight_spmf (sample_distinct_uniform_list 0 n) = 1"
  by (auto simp add: weight_sample_distinct_uniform_list)

lemma weight_sample_distinct_uniform_list_n_0 [simp]: "weight_spmf (sample_distinct_uniform_list k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_distinct_uniform_list)

lemma weight_sample_distinct_uniform_list_k_le_n [simp]: "k<n \<Longrightarrow> weight_spmf (sample_distinct_uniform_list k n) = 1"
  by (auto simp add: weight_sample_distinct_uniform_list less_iff_Suc_add)

lemma lossless_sample_distinct_uniform_list [simp]: "lossless_spmf (sample_distinct_uniform_list k n) \<longleftrightarrow> k\<le>n"
  by (auto simp add: lossless_spmf_def weight_sample_distinct_uniform_list intro: ccontr)

lemma set_spmf_sample_distinct_uniform_list [simp]: "set_spmf (sample_distinct_uniform_list k n) 
  = {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}}"
  by (simp add: finite_lists_distinct_length_eq sample_distinct_uniform_list_def)

subsection \<open>sample distinct cooridinates\<close>

fun pair_lists :: "(nat list \<times> nat list) \<Rightarrow> (nat * nat) list" where 
  "pair_lists ([],[]) = []" |
  "pair_lists ((x#xs), (y#ys)) = (x,y)#pair_lists (xs,ys)"

text \<open>function to reverse the list pairing, used in the spmf proof.\<close>
fun unpair_lists :: "(nat * nat) list \<Rightarrow> (nat list \<times> nat list)" where
  "unpair_lists [] = ([],[])" |
  "unpair_lists ((x,y)#xs) = (x#fst (unpair_lists xs), y#snd (unpair_lists xs))"

definition sample_distinct_coordinates_uniform :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list spmf"
  where "sample_distinct_coordinates_uniform k n 
          = map_spmf pair_lists (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"

lemma unpair_pair_set: "unpair_lists ` pair_lists `
        set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n)) 
      = set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
proof -
  have simplif: "set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n)) 
    =  {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}"
    unfolding  set_pair_spmf set_spmf_sample_distinct_uniform_list set_spmf_sample_uniform_list ..
  have "(unpair_lists \<circ>
    pair_lists)`
    ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times>
     {x. set x \<subseteq> {..<n} \<and> length x = k}) =
    id ` ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k})"
  proof(rule image_cong)
    fix x 
    assume asm: " x \<in> {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times>
             {x. set x \<subseteq> {..<n} \<and> length x = k}"
    then have "unpair_lists (pair_lists x) = id x"
      by (induction "x" arbitrary: k rule: pair_lists.induct)simp+
    then show "(unpair_lists \<circ> pair_lists) x = id x" 
      by fastforce
  qed simp
  then show ?thesis
    by (simp add: image_comp simplif)
qed

lemma spmf_sample_distinct_coordinates_uniform: 
  "spmf (sample_distinct_coordinates_uniform k n) pairs 
 = indicator ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}) (unpair_lists pairs) 
   / (real (\<Prod>{n - k + 1..n}) * (n^k))"
proof -
   have unfold_pairing: "pair_lists (unpair_lists pairs) = pairs"
     by (induction pairs rule: unpair_lists.induct) simp+
   have "spmf (sample_distinct_coordinates_uniform k n) pairs =  spmf
     (map_spmf pair_lists
       ( pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n) )
     )
    (pair_lists (unpair_lists pairs))"
     unfolding sample_distinct_coordinates_uniform_def unfold_pairing ..
   also have "\<dots> = indicator ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}) (unpair_lists pairs) 
   / (real (\<Prod>{n - k + 1..n}) * (n^k))"
   proof (cases "(pair_lists (unpair_lists pairs)) \<notin> pair_lists ` set_spmf ( pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n) )")
     case True
     then show ?thesis
       by (auto simp add: image_eqI spmf_map_outside  indicator_def)
   next
     case False
     have "spmf
           (map_spmf pair_lists
             (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n)))
           (pair_lists (unpair_lists pairs)) 
         = spmf ( pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n) ) 
              (unpair_lists pairs)"
     proof (rule spmf_map_inj)
       show "inj_on pair_lists (set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n)))"
       proof 
          fix x y
          assume "x \<in> set_spmf
                  (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
          then have x_in_pair_set: 
            "x \<in> {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}"
            by simp
          then have unpair_x: "unpair_lists (pair_lists x) = x"
            by (induction x arbitrary: k rule: pair_lists.induct) auto
          assume "y \<in> set_spmf
                   (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
           then have y_in_pair_set: 
            "y \<in> {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}"
             by simp
           then have unpair_y: "unpair_lists (pair_lists y) = y"
            by (induction y arbitrary: k rule: pair_lists.induct) auto
           assume pair_lists_eq: "pair_lists x = pair_lists y"
           then show "x=y" using unpair_x unpair_y by argo
       qed

       from False have "pair_lists (unpair_lists pairs) \<in> pair_lists `
        set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
         by blast
       then have "unpair_lists (pair_lists (unpair_lists pairs)) \<in> unpair_lists ` pair_lists `
          set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
         by fast
       then show " (unpair_lists pairs) \<in>
          set_spmf (pair_spmf (sample_distinct_uniform_list k n) (sample_uniform_list k n))"
         using unpair_pair_set unfold_pairing by simp
     qed
     also have "\<dots> = (spmf (sample_distinct_uniform_list k n) (fst (unpair_lists pairs) )) * (spmf (sample_uniform_list k n) (snd (unpair_lists pairs)))"
       by (metis spmf_pair surjective_pairing)
     also have "\<dots> = indicator {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} (fst (unpair_lists pairs)) / real (\<Prod>{n - k + 1..n})
      * indicator {x. set x \<subseteq> {..<n} \<and> length x = k} (snd (unpair_lists pairs)) / (n^k)"
      by (simp add: spmf_sample_distinct_uniform_list spmf_sample_uniform_list)
    also have "\<dots> = indicator ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times> {x. set x \<subseteq> {..<n} \<and> length x = k}) (unpair_lists pairs) 
          / (real (\<Prod>{n - k + 1..n}) * (n^k))"
      by (smt (verit) div_by_1 divide_divide_eq_left indicator_simps(1) indicator_simps(2) mem_Sigma_iff mult_eq_0_iff nonzero_mult_div_cancel_left prod.collapse times_divide_eq_left)
    finally  show ?thesis
      by fastforce 
   qed
   finally show ?thesis .
 qed

lemma weight_sample_distinct_coordinates_uniform_list: "weight_spmf (sample_distinct_coordinates_uniform k n) = of_bool (k\<le>n \<and> (k=0 \<or> 0<n))"
  by (auto simp add: sample_distinct_coordinates_uniform_def weight_spmf_of_set lossless_weight_spmfD weight_sample_distinct_uniform_list split: split_indicator)

lemma weight_sample_distinct_coordinates_uniform_list_k_0 [simp]: "weight_spmf (sample_distinct_coordinates_uniform 0 n) = 1"
  by (auto simp add: weight_sample_distinct_coordinates_uniform_list)

lemma weight_sample_distinct_coordinates_uniform_list_n_0 [simp]: "weight_spmf (sample_distinct_coordinates_uniform k 0) = of_bool (k=0)"
  by (auto simp add: weight_sample_distinct_coordinates_uniform_list)

lemma weight_sample_distinct_coordinates_uniform_list_k_le_n [simp]: "k<n \<Longrightarrow> weight_spmf (sample_distinct_coordinates_uniform k n) = 1"
  by (auto simp add: weight_sample_distinct_coordinates_uniform_list less_iff_Suc_add)

lemma lossless_sample_sample_distinct_coordinates_uniform_list [simp]: "lossless_spmf (sample_distinct_coordinates_uniform k n) \<longleftrightarrow> k\<le>n"
  by (auto simp add: lossless_spmf_def weight_sample_distinct_coordinates_uniform_list intro: ccontr)

lemma set_spmf_sample_distinct_coordinates_uniform_list [simp]: 
  "set_spmf (sample_distinct_coordinates_uniform k n) 
  = pair_lists `
    ({xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> {..<n}} \<times>
     {xs. set xs \<subseteq> {..<n} \<and> length xs = k})"
  by (simp add: sample_distinct_coordinates_uniform_def)

end