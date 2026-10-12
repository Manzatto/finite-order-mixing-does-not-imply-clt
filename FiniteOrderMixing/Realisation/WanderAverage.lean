import FiniteOrderMixing.Realisation.WanderOrbit

/-!
# Time averages along the wandering box

Every point of the initial box follows the orbit of `pcod ω`: at time `t`, in position `j` of
block `k`, the distance is at most `3^{-(nb k - j)} + 3^{-(j - hd k)} + 2ε 5^{-k}`, up to a factor
`3`.  Summing over a block gives `O(1 + hd k)`, the blocks up to time `T` number `O(√T)` and
`hd k = O(√k + log k)`, so the Cesàro averages of the distances tend to `0`.

The main result is `plane_wandering`, the planar form of strong pluripotency used for Theorem B.
-/

open Set Filter Topology

namespace FiniteOrderMixing

namespace Itin

variable (A : Itin)

/-! ### The distance bound -/

/-- The bound `b_t` (from the digits). -/
noncomputable def bseq (t : ℕ) : ℝ :=
  3 * (1 / 3) ^ (A.nb (A.blk t) - A.pos t) + 3 * (1 / 3) ^ (A.pos t - A.hd (A.blk t))

/-- The bound `c_t` (from the size of the box). -/
noncomputable def cseq (t : ℕ) : ℝ := 2 / 1000 * (1 / 5) ^ A.blk t

lemma bseq_nonneg (t : ℕ) : 0 ≤ A.bseq t := by unfold bseq; positivity

lemma iterate_pcod (T : P2 → P2) (h : ∀ ω, T (pcod ω) = pcod (shift ω)) (ω : Config) (t : ℕ) :
    T^[t] (pcod ω) = pcod (shift^[t] ω) := by
  induction t generalizing ω with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, h, ih, Function.iterate_succ_apply]

lemma abs_xc_sub_le {k j : ℕ} (hj0 : A.hd k ≤ j) :
    |A.xc k j - codX (shift^[A.tt k + j] A.ω)| ≤ (1 / 3) ^ (A.nb k - j) := by
  rw [codX_eq_phis _ (A.nb k - j)]
  apply abs_phis_sub_phis_le _ le_rfl le_rfl
    ⟨by linarith [(half_add_ζw_mem k).1], by linarith [(half_add_ζw_mem k).2]⟩ (codX_mem _)
  intro i _
  rw [A.word_of_ge (by omega), shift_iterate_apply]
  congr 1; push_cast; ring

lemma abs_yc_sub_le {k j : ℕ} (hj0 : A.hd k ≤ j) :
    |A.yc k j - codY (shift^[A.tt k + j] A.ω)| ≤ (1 / 3) ^ (j - A.hd k) := by
  rw [codY_iterate, yc, psis_eq_phis]
  apply abs_phis_sub_phis_le _ (by omega) (by omega) (A.υ_mem k) (codY_mem _)
  intro i hi
  rw [A.word_of_ge (by omega)]
  congr 1
  rw [show A.tt k + (j - 1 - i) = A.tt k + j - (1 + i) by omega,
    Nat.cast_sub (by omega : 1 + i ≤ A.tt k + j)]
  push_cast; ring

variable (hr : 1 ≤ A.r) (hH : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀)

lemma dist_le {z : P2} (hz : z ∈ A.Box 0 0) (t : ℕ) :
    dist ((A.T hr hH)^[t] z) ((A.T hr hH)^[t] (pcod A.ω)) ≤ A.bseq t + A.cseq t := by
  set k := A.blk t
  set j := A.pos t
  have htj : t = A.tt k + j := (A.tt_add_pos t).symm
  have hj : j ≤ A.nb k := A.pos_le t
  have hbox := A.orbit_box hr hH hz k j hj
  rw [← htj] at hbox
  rw [iterate_pcod _ (A.T_pcod hr hH)]
  obtain ⟨h1, h2⟩ := hbox
  have hw := A.width_le hj
  have hh := A.height_le k j
  set p := (A.T hr hH)^[t] z
  have hx1 : |p.1 - codX (shift^[t] A.ω)| ≤
      |A.xc k j - codX (shift^[t] A.ω)| + 1 / 1000 * (1 / 5) ^ k := by
    have := abs_sub_le p.1 (A.xc k j) (codX (shift^[t] A.ω)); linarith
  have hy1 : |p.2 - codY (shift^[t] A.ω)| ≤
      |A.yc k j - codY (shift^[t] A.ω)| + 1 / 1000 * (1 / 5) ^ k := by
    have := abs_sub_le p.2 (A.yc k j) (codY (shift^[t] A.ω)); linarith
  have hxc := A.xc_mem k j
  have hyc := A.yc_mem k j
  have hX := codX_mem (shift^[t] A.ω)
  have hY := codY_mem (shift^[t] A.ω)
  have hx2 : |A.xc k j - codX (shift^[t] A.ω)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hxc.1, hxc.2, hX.1, hX.2]
  have hy2 : |A.yc k j - codY (shift^[t] A.ω)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hyc.1, hyc.2, hY.1, hY.2]
  have hpx : (0 : ℝ) ≤ 3 * (1 / 3) ^ (A.nb k - j) := by positivity
  have hpy : (0 : ℝ) ≤ 3 * (1 / 3) ^ (j - A.hd k) := by positivity
  have key : |A.xc k j - codX (shift^[t] A.ω)| + |A.yc k j - codY (shift^[t] A.ω)| ≤
      3 * (1 / 3) ^ (A.nb k - j) + 3 * (1 / 3) ^ (j - A.hd k) := by
    by_cases hj0 : A.hd k ≤ j
    · have a1 := A.abs_xc_sub_le hj0
      have a2 := A.abs_yc_sub_le hj0
      rw [← htj] at a1 a2
      have : (0 : ℝ) ≤ (1 / 3) ^ (A.nb k - j) := by positivity
      have : (0 : ℝ) ≤ (1 / 3) ^ (j - A.hd k) := by positivity
      linarith
    · rw [show j - A.hd k = 0 by omega, pow_zero]
      linarith
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  show max |p.1 - codX (shift^[t] A.ω)| |p.2 - codY (shift^[t] A.ω)| ≤
    3 * (1 / 3) ^ (A.nb k - j) + 3 * (1 / 3) ^ (j - A.hd k) + 2 / 1000 * (1 / 5) ^ k
  have h5 : (0 : ℝ) ≤ (1 / 5) ^ k := by positivity
  apply max_le <;> linarith [abs_nonneg (A.xc k j - codX (shift^[t] A.ω)),
    abs_nonneg (A.yc k j - codY (shift^[t] A.ω))]

/-! ### Cesàro averages -/

lemma geom_third_le (N : ℕ) : ∑ i ∈ Finset.range N, (1 / 3 : ℝ) ^ i ≤ 3 / 2 := by
  rw [geom_sum_eq (by norm_num)]
  have : (0 : ℝ) ≤ (1 / 3) ^ N := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

lemma sum_pow_sub_le (h N : ℕ) : ∑ j ∈ Finset.range N, (1 / 3 : ℝ) ^ (j - h) ≤ h + 3 / 2 := by
  by_cases hN : N ≤ h
  · calc ∑ j ∈ Finset.range N, (1 / 3 : ℝ) ^ (j - h) = ∑ j ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_congr rfl fun j hj => by
            rw [Finset.mem_range] at hj; rw [show j - h = 0 by omega, pow_zero]
      _ = N := by simp
      _ ≤ h + 3 / 2 := by have : (N : ℝ) ≤ h := by exact_mod_cast hN
                          linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show h ≤ N by omega)
    rw [Finset.sum_range_add]
    have e1 : ∑ x ∈ Finset.range h, (1 / 3 : ℝ) ^ (x - h) = h := by
      have : ∀ x ∈ Finset.range h, (1 / 3 : ℝ) ^ (x - h) = 1 := fun x hx => by
        rw [Finset.mem_range] at hx; rw [show x - h = 0 by omega, pow_zero]
      rw [Finset.sum_congr rfl this]; simp
    have e2 : ∑ x ∈ Finset.range m, (1 / 3 : ℝ) ^ (h + x - h) =
        ∑ x ∈ Finset.range m, (1 / 3 : ℝ) ^ x :=
      Finset.sum_congr rfl fun x _ => by rw [show h + x - h = x by omega]
    rw [e1, e2]
    linarith [geom_third_le m]

lemma block_sum_le (k : ℕ) :
    ∑ j ∈ Finset.range (A.nb k + 1), A.bseq (A.tt k + j) ≤ 9 + 3 * A.hd k := by
  have e : ∀ j ∈ Finset.range (A.nb k + 1), A.bseq (A.tt k + j) =
      3 * (1 / 3) ^ (A.nb k + 1 - 1 - j) + 3 * (1 / 3) ^ (j - A.hd k) := by
    intro j hj
    rw [Finset.mem_range] at hj
    unfold bseq
    rw [A.blk_tt_add (by omega), A.pos_tt_add (by omega)]
    congr 3
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_range_reflect (fun i => (1 / 3 : ℝ) ^ i)]
  have := geom_third_le (A.nb k + 1)
  have := sum_pow_sub_le (A.hd k) (A.nb k + 1)
  linarith

lemma sum_tt_le (K : ℕ) :
    ∑ t ∈ Finset.range (A.tt K), A.bseq t ≤ ∑ k ∈ Finset.range K, (9 + 3 * (A.hd k : ℝ)) := by
  induction K with
  | zero => simp [tt]
  | succ K ih =>
    rw [tt_succ, add_assoc, Finset.sum_range_add,
      Finset.sum_range_succ (fun k => 9 + 3 * (A.hd k : ℝ)) K]
    linarith [A.block_sum_le K]

lemma sum_le_blk (T : ℕ) :
    ∑ t ∈ Finset.range T, A.bseq t ≤ (A.blk T + 1) * (9 + 3 * (A.hd (A.blk T) : ℝ)) := by
  set K := A.blk T
  have hT : T ≤ A.tt (K + 1) := (A.lt_tt_blk T).le
  calc ∑ t ∈ Finset.range T, A.bseq t ≤ ∑ t ∈ Finset.range (A.tt (K + 1)), A.bseq t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hT)
          fun t _ _ => A.bseq_nonneg t
    _ ≤ ∑ k ∈ Finset.range (K + 1), (9 + 3 * (A.hd k : ℝ)) := A.sum_tt_le (K + 1)
    _ ≤ ∑ k ∈ Finset.range (K + 1), (9 + 3 * (A.hd K : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_range] at hk
        have : (A.hd k : ℝ) ≤ A.hd K := by exact_mod_cast A.hd_mono (by omega)
        linarith
    _ = (K + 1) * (9 + 3 * (A.hd K : ℝ)) := by simp; ring

lemma hd_le_log (K : ℕ) :
    (A.hd K : ℝ) ≤ (2 * A.r + 2) * (Real.log ((K : ℝ) + 1) / Real.log 2 + 1) + A.H₀ +
      Nat.sqrt (K + 1) := by
  rcases K with _ | K
  · simp only [hd, Nat.cast_zero, zero_add, Real.log_one, zero_div]; positivity
  · have hlog : (Nat.log 2 (K + 2) : ℝ) ≤ Real.log ((K : ℝ) + 1 + 1) / Real.log 2 := by
      rw [le_div_iff₀ (Real.log_pos (by norm_num)), ← Real.log_pow]
      apply Real.log_le_log (by positivity)
      have := Nat.pow_log_le_self 2 (show K + 2 ≠ 0 by omega)
      have h2 : ((2 ^ Nat.log 2 (K + 2) : ℕ) : ℝ) ≤ ((K + 2 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h2 ⊢; linarith
    simp only [hd]
    push_cast
    gcongr

/-- The bound `g(K) = 2 (K + 1) (9 + 3 hd K) / K²` tends to `0`. -/
lemma tendsto_g : Tendsto (fun K : ℕ => 2 * ((K : ℝ) + 1) * (9 + 3 * (A.hd K : ℝ)) / (K : ℝ) ^ 2)
    atTop (𝓝 0) := by
  set c₁ : ℝ := (2 * A.r + 2)
  have hlog : Tendsto (fun K : ℕ => Real.log ((K : ℝ) + 1) / K) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    refine this.congr fun K => ?_
    simp
  have hinv : Tendsto (fun K : ℕ => (1 : ℝ) / K) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hsqrt := tendsto_nat_sqrt_div
  -- the majorant
  set h : ℕ → ℝ := fun K => 2 * (1 + 1 / K) * ((9 + 3 * c₁ + 3 * A.H₀) * (1 / K) +
    3 * c₁ / Real.log 2 * (Real.log ((K : ℝ) + 1) / K) +
    3 * ((Nat.sqrt (K + 1) : ℝ) / K))
  have hh : Tendsto h atTop (𝓝 0) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).add hinv).const_mul 2).mul
      (((hinv.const_mul (9 + 3 * c₁ + 3 * A.H₀)).add (hlog.const_mul (3 * c₁ / Real.log 2))).add
        (hsqrt.const_mul 3))
    simpa [h] using this
  apply squeeze_zero' (Eventually.of_forall fun K => by positivity)
  · filter_upwards [eventually_ge_atTop 1] with K hK
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hKp : (0 : ℝ) < K := by linarith
    have hd := A.hd_le_log K
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    show 2 * ((K : ℝ) + 1) * (9 + 3 * (A.hd K : ℝ)) / (K : ℝ) ^ 2 ≤
      2 * (1 + 1 / (K : ℝ)) * ((9 + 3 * c₁ + 3 * A.H₀) * (1 / K) +
        3 * c₁ / Real.log 2 * (Real.log ((K : ℝ) + 1) / K) +
        3 * ((Nat.sqrt (K + 1) : ℝ) / K))
    rw [div_le_iff₀ (by positivity)]
    have e : 2 * (1 + 1 / (K : ℝ)) * ((9 + 3 * c₁ + 3 * A.H₀) * (1 / K) +
        3 * c₁ / Real.log 2 * (Real.log ((K : ℝ) + 1) / K) +
        3 * ((Nat.sqrt (K + 1) : ℝ) / K)) * (K : ℝ) ^ 2 =
        2 * ((K : ℝ) + 1) * (9 + 3 * c₁ + 3 * A.H₀ +
          3 * c₁ * (Real.log ((K : ℝ) + 1) / Real.log 2) + 3 * Nat.sqrt (K + 1)) := by
      field_simp
    rw [e]
    have hpos : (0 : ℝ) ≤ 2 * ((K : ℝ) + 1) := by positivity
    apply mul_le_mul_of_nonneg_left _ hpos
    simp only [c₁] at hd ⊢
    nlinarith
  · exact hh

lemma tendsto_cesaro_bseq :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A.bseq t) atTop (𝓝 0) := by
  have hg := A.tendsto_g.comp A.tendsto_blk
  apply squeeze_zero' (Eventually.of_forall fun T => by
    have := Finset.sum_nonneg fun t (_ : t ∈ Finset.range T) => A.bseq_nonneg t
    positivity) _ hg
  filter_upwards [eventually_ge_atTop (A.tt 1)] with T hT
  have hK : 1 ≤ A.blk T := by
    by_contra h
    have h0 : A.blk T = 0 := by omega
    have := A.lt_tt_blk T
    rw [h0, zero_add] at this
    omega
  have hTK : (A.blk T : ℝ) * A.blk T ≤ 2 * T := by
    have := A.sq_le_tt (A.blk T)
    have := A.tt_blk_le T
    exact_mod_cast (show A.blk T * A.blk T ≤ 2 * T by omega)
  have hKpos : (0 : ℝ) < A.blk T := by exact_mod_cast hK
  have hTpos : (0 : ℝ) < T := by nlinarith
  have hs := A.sum_le_blk T
  simp only [Function.comp]
  rw [inv_mul_eq_div, div_le_div_iff₀ hTpos (by positivity)]
  have h0 : (0 : ℝ) ≤ (A.blk T + 1) * (9 + 3 * (A.hd (A.blk T) : ℝ)) := by positivity
  nlinarith

lemma tendsto_cesaro_cseq :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, A.cseq t) atTop (𝓝 0) := by
  apply Filter.Tendsto.cesaro
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 5)
    (by norm_num)).comp A.tendsto_blk
  have h2 := this.const_mul (2 / 1000)
  rw [mul_zero] at h2
  exact h2

end Itin

/-! ### The planar form of strong pluripotency -/

/-- **Planar strong pluripotency.**  For every `r ≥ 1` and every `ω ∈ Σ` there is a `C^r`
diffeomorphism `T` of the plane, equal to the identity outside `(-5, 5)²`, with a two-symbol
horseshoe coded by `pcod`, and a nonempty open set `W` whose orbits follow the orbit of
`pcod ω` in Cesàro mean. -/
theorem plane_wandering (r : ℕ) (hr : 1 ≤ r) (ω : Config) :
    ∃ T : PlaneDiffeo r, HorseshoeCoding T pcod ∧ (∀ p, PlaneDiffeo.Far p → T p = p) ∧
      ∃ W : Set P2, IsOpen W ∧ W.Nonempty ∧ (∀ y ∈ W, ¬ PlaneDiffeo.Far y) ∧ ∃ a : ℕ → ℝ,
        (∀ i : ℕ, ∀ y ∈ W, dist (T^[i] y) (T^[i] (pcod ω)) ≤ a i) ∧
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 0) := by
  obtain ⟨H₀, hH₀⟩ := pow_unbounded_of_one_lt (4 * bumpBound r * 100 ^ r) (by norm_num : (1 : ℝ) < 2)
  set A : Itin := ⟨r, H₀, ω⟩
  have hr' : 1 ≤ A.r := hr
  have hH : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀ := hH₀.le
  refine ⟨A.T hr' hH, A.horseshoeCoding hr' hH, fun p hp => A.T_far hr' hH hp, ?_⟩
  have hp0 : 0 < A.pp 0 := by simp only [Itin.pp, Itin.sz]; positivity
  have hq0 : 0 < A.qq 0 := by simp only [Itin.qq, Itin.sz, Itin.ε']; positivity
  set W : Set P2 := {z | |z.1 - A.xc 0 0| < A.pp 0} ∩ {z | |z.2 - A.yc 0 0| < A.qq 0}
  have hWbox : W ⊆ A.Box 0 0 := fun z hz => ⟨by simpa using hz.1.le, by simpa using hz.2.le⟩
  refine ⟨W, ?_, ⟨(A.xc 0 0, A.yc 0 0), by simpa [W] using ⟨hp0, hq0⟩⟩, ?_, ?_⟩
  · exact (isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const))
      continuous_const).inter
      (isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const)) continuous_const)
  · intro y hy hfar
    have h1 := A.xc_mem 0 0
    have h2 := A.yc_mem 0 0
    have hw : A.pp 0 ≤ 1 / 1000 := by simpa using A.width_le (k := 0) (j := 0) (Nat.zero_le _)
    have hh : A.qq 0 ≤ 1 / 1000 := by simpa using A.height_le 0 0
    obtain ⟨hy1, hy2⟩ := hy
    rw [Set.mem_ofPred_eq, abs_lt] at hy1 hy2
    rcases hfar with h | h
    · rw [le_abs] at h; rcases h with h | h <;> linarith [h1.1, h1.2]
    · rw [le_abs] at h; rcases h with h | h <;> linarith [h2.1, h2.2]
  · refine ⟨fun t => A.bseq t + A.cseq t, fun i y hy => A.dist_le hr' hH (hWbox hy) i, ?_⟩
    have := A.tendsto_cesaro_bseq.add A.tendsto_cesaro_cseq
    simpa [Finset.sum_add_distrib, mul_add] using this

end FiniteOrderMixing
