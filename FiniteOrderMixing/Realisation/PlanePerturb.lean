import FiniteOrderMixing.Realisation.PlaneDiffeo

/-!
# Infinitely many small bump perturbations

For sequences `e_k`, `ρ_k ∈ (0, 1]`, `c_k ∈ ℝ²`, the function
`F(z) = Σ_k e_k β(ρ_k⁻¹ (z - c_k))`, with `β` a fixed bump equal to `1` on the sup-ball of radius
`1/2` and to `0` outside the sup-ball of radius `1`, is `C^r` as soon as
`Σ_k |e_k| ρ_k^{-r} < ∞`, and `(x, y) ↦ (x, y + F(x, y))` is then a `C^r` diffeomorphism when this
sum is small.  On the inner ball of the `k`-th bump the map is the translation by `(0, e_k)`.
-/

open Set Filter Topology

namespace FiniteOrderMixing

/-- The product bump `β(w) = κ(w₁) κ(w₂)`. -/
noncomputable def bump2 (w : P2) : ℝ := bump (1 / 2) 1 w.1 * bump (1 / 2) 1 w.2

lemma contDiff_bump2 {n : ℕ∞} : ContDiff ℝ n bump2 :=
  (contDiff_bump.comp contDiff_fst).mul (contDiff_bump.comp contDiff_snd)

lemma bump2_eq_zero {w : P2} (h : 1 ≤ |w.1| ∨ 1 ≤ |w.2|) : bump2 w = 0 := by
  rcases h with h | h
  · rw [bump2, bump_eq_zero (by norm_num) (by norm_num) h, zero_mul]
  · rw [bump2, bump_eq_zero (by norm_num) (by norm_num) h, mul_zero]

lemma bump2_eq_one {w : P2} (h1 : |w.1| ≤ 1 / 2) (h2 : |w.2| ≤ 1 / 2) : bump2 w = 1 := by
  rw [bump2, bump_eq_one (by norm_num) (by norm_num) h1, bump_eq_one (by norm_num) (by norm_num) h2,
    one_mul]

lemma hasCompactSupport_bump2 : HasCompactSupport bump2 := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : P2) 1)
  intro w hw
  apply bump2_eq_zero
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, not_and_or, not_le,
    not_le, Real.norm_eq_abs, Real.norm_eq_abs] at hw
  rcases hw with h | h
  · exact Or.inl h.le
  · exact Or.inr h.le

lemma exists_bound_bump2 (r : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ i ≤ r, ∀ w, ‖iteratedFDeriv ℝ i bump2 w‖ ≤ M := by
  have : ∀ i : ℕ, ∃ C, ∀ w, ‖iteratedFDeriv ℝ i bump2 w‖ ≤ C := fun i =>
    ((contDiff_bump2 (n := ⊤)).continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_bump2.iteratedFDeriv i)
  choose C hC using this
  refine ⟨1 + ∑ i ∈ Finset.range (r + 1), |C i|, by positivity, fun i hi w => ?_⟩
  calc ‖iteratedFDeriv ℝ i bump2 w‖ ≤ C i := hC i w
    _ ≤ |C i| := le_abs_self _
    _ ≤ ∑ i ∈ Finset.range (r + 1), |C i| :=
        Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg (C j))
          (Finset.mem_range.2 (by omega))
    _ ≤ _ := by linarith

/-- A bound for the first `r` derivatives of `β`. -/
noncomputable def bumpBound (r : ℕ) : ℝ := Classical.choose (exists_bound_bump2 r)

lemma bumpBound_pos (r : ℕ) : 0 < bumpBound r := (Classical.choose_spec (exists_bound_bump2 r)).1

lemma norm_iteratedFDeriv_bump2_le {r i : ℕ} (hi : i ≤ r) (w : P2) :
    ‖iteratedFDeriv ℝ i bump2 w‖ ≤ bumpBound r :=
  (Classical.choose_spec (exists_bound_bump2 r)).2 i hi w

/-- The `k`-th term `e β(ρ⁻¹ (z - c))`. -/
noncomputable def pterm (e ρ : ℝ) (c z : P2) : ℝ := e * bump2 (ρ⁻¹ • (z - c))

lemma contDiff_pterm {n : ℕ∞} (e ρ : ℝ) (c : P2) : ContDiff ℝ n (pterm e ρ c) :=
  contDiff_const.mul (contDiff_bump2.comp ((contDiff_id.sub contDiff_const).const_smul _))

lemma norm_iteratedFDeriv_pterm (e : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (c : P2) (i : ℕ) (z : P2) :
    ‖iteratedFDeriv ℝ i (pterm e ρ c) z‖ ≤
      |e| * (ρ⁻¹ ^ i * ‖iteratedFDeriv ℝ i bump2 (ρ⁻¹ • (z - c))‖) := by
  set L : P2 →L[ℝ] P2 := ρ⁻¹ • ContinuousLinearMap.id ℝ P2
  have hfun : pterm e ρ c = e • fun z => (bump2 ∘ L) (z - c) := by
    funext z; simp [pterm, L, smul_eq_mul]
  have h1 : ContDiffAt ℝ i (fun z => (bump2 ∘ L) (z - c)) z :=
    ((contDiff_bump2.comp L.contDiff).comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [hfun, iteratedFDeriv_const_smul_apply h1, norm_smul, Real.norm_eq_abs,
    iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right (contDiff_bump2 (n := ⊤)) _
      (by exact_mod_cast le_top)]
  gcongr
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hL : ‖L‖ ≤ ρ⁻¹ := by
    refine (norm_smul_le (ρ⁻¹) (ContinuousLinearMap.id ℝ P2)).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hρ)]
    exact mul_le_of_le_one_right (inv_pos.2 hρ).le (ContinuousLinearMap.norm_id_le)
  have hLz : L (z - c) = ρ⁻¹ • (z - c) := by simp [L]
  rw [hLz]
  gcongr

lemma pterm_eq_zero (e : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {c z : P2}
    (h : ρ ≤ |z.1 - c.1| ∨ ρ ≤ |z.2 - c.2|) : pterm e ρ c z = 0 := by
  rw [pterm, bump2_eq_zero, mul_zero]
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul, abs_mul,
    abs_inv, abs_of_pos hρ]
  rcases h with h | h
  · left; rw [inv_mul_eq_div, le_div_iff₀ hρ, one_mul]; exact h
  · right; rw [inv_mul_eq_div, le_div_iff₀ hρ, one_mul]; exact h

lemma pterm_eq (e : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {c z : P2} (h1 : |z.1 - c.1| ≤ ρ / 2)
    (h2 : |z.2 - c.2| ≤ ρ / 2) : pterm e ρ c z = e := by
  rw [pterm, bump2_eq_one, mul_one]
  · simp only [Prod.smul_fst, Prod.fst_sub, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hρ]
    rw [inv_mul_eq_div, div_le_iff₀ hρ]; linarith
  · simp only [Prod.smul_snd, Prod.snd_sub, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hρ]
    rw [inv_mul_eq_div, div_le_iff₀ hρ]; linarith

/-- Hypotheses on the perturbation data, for smoothness `C^r`. -/
structure PertHyp (r : ℕ) (e ρ : ℕ → ℝ) (c : ℕ → P2) (u : ℕ → ℝ) : Prop where
  ρ_pos : ∀ k, 0 < ρ k
  ρ_le : ∀ k, ρ k ≤ 1
  c_snd : ∀ k, |(c k).2| ≤ 1
  summable : Summable u
  le_u : ∀ k, |e k| * (ρ k)⁻¹ ^ r ≤ u k
  small : bumpBound r * ∑' k, u k ≤ 1 / 2

/-- The perturbation `F(z) = Σ_k e_k β(ρ_k⁻¹ (z - c_k))`. -/
noncomputable def pertF (e ρ : ℕ → ℝ) (c : ℕ → P2) (z : P2) : ℝ :=
  ∑' k, pterm (e k) (ρ k) (c k) z

section Pert

variable {r : ℕ} {e ρ : ℕ → ℝ} {c : ℕ → P2} {u : ℕ → ℝ}

lemma PertHyp.bound (h : PertHyp r e ρ c u) {i : ℕ} (hi : i ≤ r) (k : ℕ) (z : P2) :
    ‖iteratedFDeriv ℝ i (pterm (e k) (ρ k) (c k)) z‖ ≤ bumpBound r * u k := by
  refine (norm_iteratedFDeriv_pterm _ (h.ρ_pos k) _ i z).trans ?_
  have hρ1 : 1 ≤ (ρ k)⁻¹ := (one_le_inv₀ (h.ρ_pos k)).2 (h.ρ_le k)
  have hpow : (ρ k)⁻¹ ^ i ≤ (ρ k)⁻¹ ^ r := pow_le_pow_right₀ hρ1 hi
  have hb := norm_iteratedFDeriv_bump2_le hi ((ρ k)⁻¹ • (z - c k))
  have hu := h.le_u k
  calc |e k| * ((ρ k)⁻¹ ^ i * ‖iteratedFDeriv ℝ i bump2 ((ρ k)⁻¹ • (z - c k))‖)
      ≤ |e k| * ((ρ k)⁻¹ ^ r * bumpBound r) := by gcongr
    _ = bumpBound r * (|e k| * (ρ k)⁻¹ ^ r) := by ring
    _ ≤ bumpBound r * u k := by gcongr; exact (bumpBound_pos r).le

lemma PertHyp.u_nonneg (h : PertHyp r e ρ c u) (k : ℕ) : 0 ≤ u k :=
  (mul_nonneg (abs_nonneg _) (pow_nonneg (inv_pos.2 (h.ρ_pos k)).le _)).trans (h.le_u k)

lemma PertHyp.contDiff (h : PertHyp r e ρ c u) : ContDiff ℝ r (pertF e ρ c) :=
  contDiff_tsum (v := fun _ k => bumpBound r * u k) (fun k => contDiff_pterm _ _ _)
    (fun _ _ => h.summable.mul_left _)
    (fun i k z hi => h.bound (by exact_mod_cast hi) k z)

lemma PertHyp.norm_fderiv_le (h : PertHyp r e ρ c u) (hr : 1 ≤ r) (z : P2) :
    ‖fderiv ℝ (pertF e ρ c) z‖ ≤ 1 / 2 := by
  have hs : Summable fun k => bumpBound r * u k := h.summable.mul_left _
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
  unfold pertF
  rw [iteratedFDeriv_tsum_apply (N := r) (v := fun _ k => bumpBound r * u k)
      (fun k => contDiff_pterm _ _ _) (fun _ _ => hs)
      (fun i k z hi => h.bound (by exact_mod_cast hi) k z) (by exact_mod_cast hr)]
  have hn : Summable fun k => ‖iteratedFDeriv ℝ 1 (pterm (e k) (ρ k) (c k)) z‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => h.bound hr k z) hs
  refine (norm_tsum_le_tsum_norm hn).trans ?_
  refine (hn.tsum_le_tsum (fun k => h.bound hr k z) hs).trans ?_
  rw [tsum_mul_left]; exact h.small

lemma PertHyp.one_add_deriv_pos (h : PertHyp r e ρ c u) (hr : 1 ≤ r) (x y : ℝ) :
    0 < 1 + deriv (fun y => pertF e ρ c (x, y)) y := by
  have hd : Differentiable ℝ (pertF e ρ c) :=
    h.contDiff.differentiable (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hr))
  rw [(PlaneDiffeo.hasDerivAt_slice hd x y).deriv]
  have h1 : |fderiv ℝ (pertF e ρ c) (x, y) (0, 1)| ≤ 1 / 2 := by
    have := (fderiv ℝ (pertF e ρ c) (x, y)).le_opNorm ((0 : ℝ), (1 : ℝ))
    rw [Real.norm_eq_abs] at this
    have hn : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    rw [hn, mul_one] at this
    exact this.trans (h.norm_fderiv_le hr _)
  linarith [neg_abs_le (fderiv ℝ (pertF e ρ c) (x, y) (0, 1))]

lemma pertF_eq_zero (h : PertHyp r e ρ c u) {z : P2}
    (hz : ∀ k, ρ k ≤ |z.1 - (c k).1| ∨ ρ k ≤ |z.2 - (c k).2|) : pertF e ρ c z = 0 := by
  rw [pertF]
  rw [show (fun k => pterm (e k) (ρ k) (c k) z) = fun _ => (0 : ℝ) from
    funext fun k => pterm_eq_zero _ (h.ρ_pos k) (hz k), tsum_zero]

lemma pertF_eq (h : PertHyp r e ρ c u) {z : P2} {k : ℕ} (h1 : |z.1 - (c k).1| ≤ ρ k / 2)
    (h2 : |z.2 - (c k).2| ≤ ρ k / 2)
    (hz : ∀ j ≠ k, ρ j ≤ |z.1 - (c j).1| ∨ ρ j ≤ |z.2 - (c j).2|) : pertF e ρ c z = e k := by
  rw [pertF, tsum_eq_single k (fun j hj => pterm_eq_zero _ (h.ρ_pos j) (hz j hj)),
    pterm_eq _ (h.ρ_pos k) h1 h2]

lemma pertF_far (h : PertHyp r e ρ c u) {z : P2} (hz : 2 ≤ |z.2|) : pertF e ρ c z = 0 :=
  pertF_eq_zero h fun k => Or.inr (by
    have := h.c_snd k; have := h.ρ_le k
    have := abs_sub_abs_le_abs_sub z.2 (c k).2; linarith)

/-- The perturbation diffeomorphism `(x, y) ↦ (x, y + F(x, y))`. -/
noncomputable def PertHyp.diffeo (h : PertHyp r e ρ c u) (hr : 1 ≤ r) : PlaneDiffeo r :=
  PlaneDiffeo.vert (pertF e ρ c) h.contDiff (by exact_mod_cast hr) 2
    (fun _ hz => pertF_far h hz) (h.one_add_deriv_pos hr)

lemma PertHyp.diffeo_apply (h : PertHyp r e ρ c u) (hr : 1 ≤ r) (z : P2) :
    h.diffeo hr z = (z.1, z.2 + pertF e ρ c z) := rfl

end Pert

end FiniteOrderMixing
