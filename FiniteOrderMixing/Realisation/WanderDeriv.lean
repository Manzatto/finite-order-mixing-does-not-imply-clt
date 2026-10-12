import FiniteOrderMixing.Realisation.WanderAverage

/-!
# The derivative of the planar horseshoe

Near every point of the horseshoe, the perturbed map `T` is affine with derivative
`diag(3, 1/3)`.  Hence `D_{pcod ω} T^n = diag(3^n, 3^{-n})`.  The main result is
`plane_wandering_deriv`, which adds this to `plane_wandering`.
-/

open Set Filter Topology

namespace FiniteOrderMixing

/-- The derivative `diag(3, 1/3)` of the horseshoe. -/
noncomputable def diagL : P2 →L[ℝ] P2 :=
  ((3 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((3 : ℝ)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma diagL_apply (w : P2) : diagL w = (3 * w.1, 3⁻¹ * w.2) := rfl

lemma diagL_pow_apply (n : ℕ) (w : P2) : (diagL ^ n) w = (3 ^ n * w.1, w.2 / 3 ^ n) := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    show (diagL ^ n) (diagL w) = _
    rw [ih, diagL_apply]
    ext <;> simp only <;> field_simp <;> ring

namespace Itin

variable (A : Itin) (hr : 1 ≤ A.r) (hH : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀)

/-- Near `pcod ω`, `T` is the affine map of the symbol `ω₀`. -/
lemma T_eventuallyEq (ω : Config) : (A.T hr hH : P2 → P2) =ᶠ[𝓝 (pcod ω)]
    fun z => (3 * z.1 - 2 * bit (ω 0), (z.2 + 2 * bit (ω 0)) / 3) := by
  have hx := codX_eq ω
  have hX := codX_mem (shift ω)
  have hY := codY_mem ω
  have hs := phi_strip (ω 0) (δ := 0) (z := codX (shift ω)) (by linarith [hX.1])
    (by linarith [hX.2])
  rw [← hx] at hs
  have hbit0 := bit_nonneg (ω 0); have hbit1 := bit_le_one (ω 0)
  filter_upwards [Metric.ball_mem_nhds (pcod ω) (by norm_num : (0 : ℝ) < 1 / 100)] with z hz
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hz
  obtain ⟨h1, h2⟩ := hz
  rw [abs_lt] at h1 h2
  simp only [pcod] at h1 h2
  have hfar : 1 / 8 ≤ |z.1 - 1 / 2| := by
    rcases hb : ω 0 with _ | _
    · rw [hb] at hs; simp only [bit, Bool.false_eq_true, ↓reduceIte] at hs
      rw [abs_sub_comm, le_abs]; left; linarith [hs.2]
    · rw [hb] at hs; simp only [bit, ↓reduceIte] at hs
      rw [le_abs]; left; linarith [hs.1]
  rw [A.T_eq_model hr hH hfar, T₀]
  exact PlaneDiffeo.model_strip _ _ _ (ω 0) (by linarith [hs.1]) (by linarith [hs.2])
    (by linarith [hY.1]) (by linarith [hY.2])

lemma hasFDerivAt_T (ω : Config) : HasFDerivAt (A.T hr hH : P2 → P2) diagL (pcod ω) := by
  have h1 : HasFDerivAt (fun z : P2 => 3 * z.1 - 2 * bit (ω 0))
      ((3 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) (pcod ω) :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := pcod ω)).const_mul (3 : ℝ)).sub_const (2 * bit (ω 0))
  have h2a : HasFDerivAt (fun z : P2 => z.2 + 2 * bit (ω 0)) (ContinuousLinearMap.snd ℝ ℝ ℝ)
      (pcod ω) := (hasFDerivAt_snd (𝕜 := ℝ) (p := pcod ω)).add_const (2 * bit (ω 0))
  have h2 : HasFDerivAt (fun z : P2 => (3 : ℝ)⁻¹ * (z.2 + 2 * bit (ω 0)))
      ((3 : ℝ)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) (pcod ω) := HasFDerivAt.const_mul h2a _
  have h := HasFDerivAt.prodMk h1 h2
  refine h.congr_of_eventuallyEq ((A.T_eventuallyEq hr hH ω).trans
    (Eventually.of_forall fun z => ?_))
  ext
  · rfl
  · simp only; ring

lemma hasFDerivAt_T_iterate (n : ℕ) (ω : Config) :
    HasFDerivAt ((A.T hr hH : P2 → P2)^[n]) (diagL ^ n) (pcod ω) := by
  induction n generalizing ω with
  | zero =>
    rw [pow_zero, Function.iterate_zero]
    exact hasFDerivAt_id (𝕜 := ℝ) (pcod ω)
  | succ n ih =>
    rw [Function.iterate_succ, pow_succ, ContinuousLinearMap.mul_def]
    have h := ih (shift ω)
    rw [← A.T_pcod hr hH ω] at h
    exact h.comp (pcod ω) (A.hasFDerivAt_T hr hH ω)

end Itin

/-- **Planar strong pluripotency, with the derivative.**  As `plane_wandering`, and moreover the
horseshoe is hyperbolic: `D_{pcod ω} T^n = diag(3^n, 3^{-n})`. -/
theorem plane_wandering_deriv (r : ℕ) (hr : 1 ≤ r) (ω : Config) :
    ∃ T : PlaneDiffeo r, HorseshoeCoding T pcod ∧ (∀ p, PlaneDiffeo.Far p → T p = p) ∧
      (∀ (n : ℕ) (ω' : Config), HasFDerivAt ((T : P2 → P2)^[n]) (diagL ^ n) (pcod ω')) ∧
      ∃ W : Set P2, IsOpen W ∧ W.Nonempty ∧ (∀ y ∈ W, ¬ PlaneDiffeo.Far y) ∧ ∃ a : ℕ → ℝ,
        (∀ i : ℕ, ∀ y ∈ W, dist (T^[i] y) (T^[i] (pcod ω)) ≤ a i) ∧
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 0) := by
  obtain ⟨H₀, hH₀⟩ := pow_unbounded_of_one_lt (4 * bumpBound r * 100 ^ r) (by norm_num : (1 : ℝ) < 2)
  set A : Itin := ⟨r, H₀, ω⟩
  have hr' : 1 ≤ A.r := hr
  have hH : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀ := hH₀.le
  refine ⟨A.T hr' hH, A.horseshoeCoding hr' hH, fun p hp => A.T_far hr' hH hp,
    fun n ω' => A.hasFDerivAt_T_iterate hr' hH n ω', ?_⟩
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
