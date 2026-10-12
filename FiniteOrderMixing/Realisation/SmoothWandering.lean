import FiniteOrderMixing.Realisation.WanderDeriv

/-!
# A smooth physical realisation

The square-root heads make the perturbation of one fixed planar map summable in every
finite derivative order. Thus the orbit-following construction is `C^∞`, with the same
coding, hyperbolic derivatives and open wandering box as the finite-order construction.
-/

open Set Filter Topology
open scoped ContDiff

namespace FiniteOrderMixing

/-- Summability of the derivative bounds in every order makes the same perturbation smooth.
Only first-order bounds need to be small to obtain a diffeomorphism. -/
lemma contDiff_pertF_infty {e ρ : ℕ → ℝ} {c : ℕ → P2}
    (hρ : ∀ k, 0 < ρ k) (hρ1 : ∀ k, ρ k ≤ 1)
    (hs : ∀ m : ℕ, Summable (fun k => |e k| * (ρ k)⁻¹ ^ m)) :
    ContDiff ℝ ∞ (pertF e ρ c) := by
  rw [contDiff_infty]
  intro m
  apply contDiff_tsum (v := fun _ k => bumpBound m * (|e k| * (ρ k)⁻¹ ^ m))
    (fun k => contDiff_pterm _ _ _) (fun _ _ => (hs m).mul_left _)
  intro i k z hi
  have him : i ≤ m := by exact_mod_cast hi
  have hpow : (ρ k)⁻¹ ^ i ≤ (ρ k)⁻¹ ^ m :=
    pow_le_pow_right₀ ((one_le_inv₀ (hρ k)).2 (hρ1 k)) him
  have hb := norm_iteratedFDeriv_bump2_le him ((ρ k)⁻¹ • (z - c k))
  refine (norm_iteratedFDeriv_pterm _ (hρ k) _ i z).trans ?_
  calc |e k| * ((ρ k)⁻¹ ^ i * ‖iteratedFDeriv ℝ i bump2 ((ρ k)⁻¹ • (z - c k))‖)
      ≤ |e k| * ((ρ k)⁻¹ ^ m * bumpBound m) := by
        gcongr
        exact pow_nonneg (inv_pos.2 (hρ k)).le _
    _ = bumpBound m * (|e k| * (ρ k)⁻¹ ^ m) := by ring

namespace Itin

variable (A : Itin)

lemma summable_corrections (m : ℕ) :
    Summable (fun k => |A.e k| * (ρw k)⁻¹ ^ m) := by
  have hs := (summable_pow_mul_third_sqrt (2 * m)).mul_left (100 ^ m : ℝ)
  apply hs.of_nonneg_of_le (fun k =>
    mul_nonneg (abs_nonneg _) (pow_nonneg (inv_pos.2 (ρw_pos k)).le _))
  intro k
  have he : |A.e k| ≤ (1 / 3 : ℝ) ^ Nat.sqrt (k + 2) :=
    (A.abs_e_le k).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by simp only [hd]; omega))
  have hρ : (ρw k)⁻¹ = 100 * ((k : ℝ) + 2) ^ 2 := by
    unfold ρw; rw [one_div, inv_inv]
  rw [hρ]
  calc |A.e k| * (100 * ((k : ℝ) + 2) ^ 2) ^ m ≤
      (1 / 3 : ℝ) ^ Nat.sqrt (k + 2) * (100 * ((k : ℝ) + 2) ^ 2) ^ m := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

lemma contDiff_pertF : ContDiff ℝ ∞ (pertF A.e ρw A.ctr) :=
  contDiff_pertF_infty ρw_pos (fun k => (ρw_le k).trans (by norm_num)) A.summable_corrections

/-- The same perturbed map, with its smoothness in all orders recorded. -/
noncomputable def TInfty (hr : 1 ≤ A.r)
    (hH : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀) : PlaneDiffeo ⊤ :=
  (PlaneDiffeo.vert (pertF A.e ρw A.ctr) A.contDiff_pertF (by norm_num) 2
    (fun _ hz => pertF_far (A.pertHyp hH) hz)
    ((A.pertHyp hH).one_add_deriv_pos hr)).trans
    (PlaneDiffeo.model (n := ⊤) (by norm_num) A.γ A.γ_pos A.γ_le_one)

lemma TInfty_coe (hr : 1 ≤ A.r)
    (hH : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀) :
    (A.TInfty hr hH : P2 → P2) = A.T hr hH := rfl

end Itin

/-- A single `C^∞` planar diffeomorphism realises any prescribed symbolic orbit on average,
with a uniformly hyperbolic two-symbol horseshoe and a nonempty open wandering box. -/
theorem plane_wandering_deriv_smooth (w : Config) :
    ∃ T : PlaneDiffeo ⊤, HorseshoeCoding T pcod ∧ (∀ p, PlaneDiffeo.Far p → T p = p) ∧
      (∀ (n : ℕ) (w' : Config), HasFDerivAt ((T : P2 → P2)^[n]) (diagL ^ n) (pcod w')) ∧
      ∃ W : Set P2, IsOpen W ∧ W.Nonempty ∧ (∀ y ∈ W, ¬ PlaneDiffeo.Far y) ∧ ∃ a : ℕ → ℝ,
        (∀ i : ℕ, ∀ y ∈ W, dist (T^[i] y) (T^[i] (pcod w)) ≤ a i) ∧
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 0) := by
  let r : ℕ := 1
  have hr : 1 ≤ r := by norm_num [r]
  obtain ⟨H₀, hH₀⟩ := pow_unbounded_of_one_lt (4 * bumpBound r * 100 ^ r) (by norm_num : (1 : ℝ) < 2)
  set A : Itin := ⟨r, H₀, w⟩
  have hr' : 1 ≤ A.r := hr
  have hH : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀ := hH₀.le
  refine ⟨A.TInfty hr' hH, ?_⟩
  rw [A.TInfty_coe hr' hH]
  refine ⟨ A.horseshoeCoding hr' hH, fun p hp => A.T_far hr' hH hp,
    fun n w' => A.hasFDerivAt_T_iterate hr' hH n w', ?_⟩
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

/-- The smooth construction also supplies every finite regularity index. -/
theorem plane_wandering_deriv_all (r : ℕ∞) (w : Config) :
    ∃ T : PlaneDiffeo r, HorseshoeCoding T pcod ∧ (∀ p, PlaneDiffeo.Far p → T p = p) ∧
      (∀ (n : ℕ) (w' : Config), HasFDerivAt ((T : P2 → P2)^[n]) (diagL ^ n) (pcod w')) ∧
      ∃ W : Set P2, IsOpen W ∧ W.Nonempty ∧ (∀ y ∈ W, ¬ PlaneDiffeo.Far y) ∧ ∃ a : ℕ → ℝ,
        (∀ i : ℕ, ∀ y ∈ W, dist (T^[i] y) (T^[i] (pcod w)) ≤ a i) ∧
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 0) := by
  obtain ⟨T, hT⟩ := plane_wandering_deriv_smooth w
  exact ⟨T.of_le le_top, hT⟩

end FiniteOrderMixing
