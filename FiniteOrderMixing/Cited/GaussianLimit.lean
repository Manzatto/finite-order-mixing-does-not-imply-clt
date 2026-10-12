import FiniteOrderMixing.Basic

/-!
# Moments of a Gaussian weak limit

If `Y_k ⇒ N(0,v)` with `E Y_k^2 = 1` and `E Y_k^4 ≤ 3`, then `v = 1`, and every uniform bound
`E Y_k^{2p} ≤ b` passes to the limit.

* A continuous `g ≥ 0` with `E g(Y_k) ≤ b` has `∫ g dλ ≤ b` for the weak limit `λ`: the bounded
  truncations `min(g, M)` pass to the limit, and dominated convergence lets `M → ∞`.
* `y^2 - y^4/M ≤ min(y^2, M)` gives `E min(Y_k^2, M) ≥ 1 - 3/M`, hence `v ≥ 1 - 3/M` in the limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal BoundedContinuousFunction

namespace FiniteOrderMixing

/-- The truncation `min(g, M)` of a continuous `g ≥ 0`, as a bounded continuous function. -/
noncomputable def truncBCF (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (M : ℝ)
    (hM : 0 ≤ M) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => min (g x) M, hg.min continuous_const⟩ M
    fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := min_le_right (g x) M
      have h2 := min_le_right (g y) M
      have h3 : 0 ≤ min (g x) M := le_min (hg0 x) hM
      have h4 : 0 ≤ min (g y) M := le_min (hg0 y) hM
      rw [abs_le]; constructor <;> linarith

@[simp] lemma truncBCF_apply (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (M : ℝ)
    (hM : 0 ≤ M) (x : ℝ) : truncBCF g hg hg0 M hM x = min (g x) M := rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : ℕ → Ω → ℝ}

lemma integrable_bcf_comp (hY : ∀ k, Measurable (Y k)) (u : ℝ →ᵇ ℝ) (k : ℕ) :
    Integrable (fun ω => u (Y k ω)) μ :=
  Integrable.of_bound (u.continuous.measurable.comp (hY k)).aestronglyMeasurable ‖u‖
    (Eventually.of_forall fun _ => u.norm_coe_le_norm _)

/-- Fatou's lemma for weak convergence, for a continuous `g ≥ 0` integrable for the limit. -/
lemma integral_le_of_converges {lam : Measure ℝ} [IsProbabilityMeasure lam]
    (hY : ∀ k, Measurable (Y k)) (hconv : ConvergesInDistribution μ Y lam)
    {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgl : Integrable g lam) {b : ℝ}
    (hint : ∀ k, Integrable (fun ω => g (Y k ω)) μ) (hb : ∀ k, ∫ ω, g (Y k ω) ∂μ ≤ b) :
    ∫ x, g x ∂lam ≤ b := by
  set u : ℕ → ℝ →ᵇ ℝ := fun M => truncBCF g hg hg0 M (Nat.cast_nonneg M)
  have h1 : ∀ M, ∫ x, u M x ∂lam ≤ b := fun M =>
    le_of_tendsto' (hconv (u M)) fun k =>
      (integral_mono (integrable_bcf_comp hY (u M) k) (hint k)
        fun ω => min_le_left _ _).trans (hb k)
  have h2 : Tendsto (fun M => ∫ x, u M x ∂lam) atTop (𝓝 (∫ x, g x ∂lam)) := by
    refine tendsto_integral_of_dominated_convergence g
      (fun M => (u M).continuous.aestronglyMeasurable) hgl (fun M => Eventually.of_forall
        fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simp only [u, truncBCF_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_min (hg0 x) (Nat.cast_nonneg M))]
      exact min_le_left _ _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈g x⌉₊] with M hM
      simp only [u, truncBCF_apply]
      exact (min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hM))).symm
  exact le_of_tendsto' h2 h1

lemma integrable_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ (2 * n)) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := v) ((2 * n : ℕ) : ENNReal)
    (ENNReal.natCast_ne_top _)).integrable_norm_pow'
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [id, Real.norm_eq_abs, pow_mul, sq_abs]

lemma integral_sq_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_eq_integral (μ := gaussianReal 0 v) (X := fun x : ℝ => x)
    measurable_id.aemeasurable
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  simpa using h.symm

/-- **[Billingsley, Thm 3.4–3.5]** Moments of a Gaussian weak limit. -/
theorem gaussian_limit_moments (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, Measurable (Y k)) (v : ℝ≥0)
    (hconv : ConvergesInDistribution μ Y (gaussianReal 0 v))
    (h2 : ∀ k, ∫ ω, Y k ω ^ 2 ∂μ = 1) (h4 : ∀ k, ∫ ω, Y k ω ^ 4 ∂μ ≤ 3)
    (h4_int : ∀ k, Integrable (fun ω => Y k ω ^ 4) μ)
    (p : ℕ) (b : ℝ) (hb : ∀ k, ∫ ω, Y k ω ^ (2 * p) ∂μ ≤ b)
    (hp_int : ∀ k, Integrable (fun ω => Y k ω ^ (2 * p)) μ) :
    v = 1 ∧ ∫ x, x ^ (2 * p) ∂(gaussianReal 0 1) ≤ b := by
  have h2_int : ∀ k, Integrable (fun ω => Y k ω ^ 2) μ := fun k =>
    Integrable.of_integral_ne_zero (by rw [h2 k]; exact one_ne_zero)
  have hsq : ∀ x : ℝ, 0 ≤ x ^ 2 := fun x => sq_nonneg x
  -- `v ≤ 1`
  have hle : (v : ℝ) ≤ 1 := by
    rw [← integral_sq_gaussianReal v]
    exact integral_le_of_converges hY hconv (continuous_pow 2) hsq
      (by simpa using integrable_pow_gaussianReal v 1) h2_int fun k => (h2 k).le
  -- `v ≥ 1 - 3/M`
  have hge : ∀ n : ℕ, 1 - 3 * (1 / ((n : ℝ) + 1)) ≤ v := by
    intro n
    set M : ℝ := n + 1
    have hM : 0 < M := by positivity
    set u := truncBCF (fun x => x ^ 2) (continuous_pow 2) hsq M hM.le
    have hlow : ∀ k, 1 - 3 * (1 / M) ≤ ∫ ω, u (Y k ω) ∂μ := fun k => by
      have hpt : ∀ ω, Y k ω ^ 2 - Y k ω ^ 4 / M ≤ u (Y k ω) := fun ω => by
        simp only [u, truncBCF_apply]
        refine le_min ?_ ?_
        · have : 0 ≤ Y k ω ^ 4 / M := by positivity
          linarith
        · rw [sub_le_iff_le_add, ← sub_le_iff_le_add', div_eq_mul_inv]
          rw [show Y k ω ^ 4 = (Y k ω ^ 2) ^ 2 by ring]
          have hMi : M * M⁻¹ = 1 := mul_inv_cancel₀ hM.ne'
          nlinarith [sq_nonneg (Y k ω ^ 2 - M), inv_pos.2 hM]
      calc 1 - 3 * (1 / M) ≤ ∫ ω, Y k ω ^ 2 ∂μ - (∫ ω, Y k ω ^ 4 ∂μ) / M := by
            rw [h2 k]
            have := div_le_div_of_nonneg_right (h4 k) hM.le
            rw [mul_one_div]; linarith
        _ = ∫ ω, (Y k ω ^ 2 - Y k ω ^ 4 / M) ∂μ := by
            rw [integral_sub (h2_int k) ((h4_int k).div_const M), integral_div]
        _ ≤ ∫ ω, u (Y k ω) ∂μ :=
            integral_mono ((h2_int k).sub ((h4_int k).div_const M))
              (integrable_bcf_comp hY u k) hpt
    have hlim := ge_of_tendsto' (hconv u) hlow
    calc 1 - 3 * (1 / M) ≤ ∫ x, u x ∂(gaussianReal 0 v) := hlim
      _ ≤ ∫ x, x ^ 2 ∂(gaussianReal 0 v) :=
          integral_mono (BoundedContinuousFunction.integrable (gaussianReal 0 v) u) (by simpa using integrable_pow_gaussianReal v 1)
            fun x => min_le_left _ _
      _ = v := integral_sq_gaussianReal v
  have hv1 : (1 : ℝ) ≤ v := by
    have ht : Tendsto (fun n : ℕ => 1 - 3 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (1 - 3 * 0)) :=
      tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 3)
    simp only [mul_zero, sub_zero] at ht
    exact le_of_tendsto' ht hge
  have hv : v = 1 := by
    have : (v : ℝ) = 1 := le_antisymm hle hv1
    exact_mod_cast this
  refine ⟨hv, ?_⟩
  subst hv
  exact integral_le_of_converges hY hconv (continuous_pow (2 * p))
    (fun x => by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) p)
    (integrable_pow_gaussianReal 1 p) hp_int hb

end FiniteOrderMixing
