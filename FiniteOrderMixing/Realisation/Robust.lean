import FiniteOrderMixing.Realisation.Variance
import FiniteOrderMixing.Cited.GaussianLimit
import FiniteOrderMixing.Cited.GaussianMoment

/-!
# Stability of the failure of the CLT (Proposition `prop:robustness`)

The paper proves Proposition `prop:robustness` by compactness (Prokhorov's theorem and closedness
of the Gaussian laws).  For the observable of Theorem C a direct quantitative argument is
available, which we use instead:

* `no_gaussian_of_close` — if `E Y_n² = 1`, `E Y_n^{2p} ≤ (2p-1)!! - δ` for large `n`, and
  `‖Y_n - Y'_n‖_{L²} ≤ η` with `η` small (depending only on `p` and `δ`), then `Y'_n` has no
  Gaussian weak subsequential limit.  Bounded Lipschitz truncations `min(|t|, B)^q` transfer the
  second and `2p`-th moments to a hypothetical limit `N(0, v)`: the second moment forces `v` to be
  close to `1`, and then the `2p`-th moment is too small.
* `robust_of_moments` — **Proposition `prop:robustness`**: with Lemma `lem:variance`, a whole
  Lipschitz neighbourhood of `f₀` has no Gaussian weak subsequential limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Nat BoundedContinuousFunction

namespace FiniteOrderMixing

/-! ## Truncated powers -/

/-- `ψ_{q,B}(t) = min(|t|, B)^q`. -/
def truncPow (q : ℕ) (B t : ℝ) : ℝ := (min |t| B) ^ q

section TruncPow

variable {q : ℕ} {B : ℝ}

lemma truncPow_nonneg (hB : 0 ≤ B) (t : ℝ) : 0 ≤ truncPow q B t :=
  pow_nonneg (le_min (abs_nonneg _) hB) _

lemma truncPow_le_bound (hB : 0 ≤ B) (t : ℝ) : truncPow q B t ≤ B ^ q :=
  pow_le_pow_left₀ (le_min (abs_nonneg _) hB) (min_le_right _ _) q

lemma truncPow_le_abs_pow (hB : 0 ≤ B) (t : ℝ) : truncPow q B t ≤ |t| ^ q :=
  pow_le_pow_left₀ (le_min (abs_nonneg _) hB) (min_le_left _ _) q

lemma continuous_truncPow : Continuous (truncPow q B) :=
  (continuous_abs.min continuous_const).pow q

lemma abs_truncPow_sub_le (hB : 0 ≤ B) (s t : ℝ) :
    |truncPow q B s - truncPow q B t| ≤ q * B ^ (q - 1) * |s - t| := by
  unfold truncPow
  have ha : 0 ≤ min |s| B := le_min (abs_nonneg _) hB
  have hb : 0 ≤ min |t| B := le_min (abs_nonneg _) hB
  have hab : |min |s| B - min |t| B| ≤ |s - t| := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    simp only [sub_self, abs_zero]
    exact max_le (abs_abs_sub_abs_le_abs_sub s t) (abs_nonneg _)
  have hmax : max |min |s| B| |min |t| B| ≤ B := by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact max_le (min_le_right _ _) (min_le_right _ _)
  calc |min |s| B ^ q - min |t| B ^ q|
      ≤ |min |s| B - min |t| B| * q * max |min |s| B| |min |t| B| ^ (q - 1) :=
        abs_pow_sub_pow_le _ _ _
    _ ≤ |s - t| * q * B ^ (q - 1) := by gcongr
    _ = q * B ^ (q - 1) * |s - t| := by ring

lemma sq_sub_le_truncPow {A : ℝ} (hA : 0 < A) (m : ℕ) (t : ℝ) :
    t ^ 2 - t ^ (2 * (m + 1)) / A ^ (2 * m) ≤ truncPow 2 A t := by
  have hApow : 0 < A ^ (2 * m) := by positivity
  have hdiv : 0 ≤ t ^ (2 * (m + 1)) / A ^ (2 * m) :=
    div_nonneg (by rw [pow_mul]; positivity) hApow.le
  unfold truncPow
  rcases le_or_gt |t| A with h | h
  · rw [min_eq_left h, sq_abs]; linarith
  · rw [min_eq_right h.le]
    have ht2 : A ^ 2 ≤ t ^ 2 := by rw [← sq_abs t]; exact pow_le_pow_left₀ hA.le h.le 2
    have hpow : (A ^ 2) ^ m ≤ (t ^ 2) ^ m := pow_le_pow_left₀ (sq_nonneg _) ht2 m
    have : t ^ 2 ≤ t ^ (2 * (m + 1)) / A ^ (2 * m) := by
      rw [le_div_iff₀ hApow, show t ^ (2 * (m + 1)) = t ^ 2 * (t ^ 2) ^ m by ring,
        show A ^ (2 * m) = (A ^ 2) ^ m by ring]
      exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    nlinarith [sq_nonneg A]

/-- `ψ_{q,B}` as a bounded continuous function. -/
noncomputable def truncPowBCF (q : ℕ) (B : ℝ) (hB : 0 ≤ B) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨truncPow q B, continuous_truncPow⟩ (B ^ q) fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    have h1 := truncPow_nonneg (q := q) hB x
    have h2 := truncPow_nonneg (q := q) hB y
    have h3 := truncPow_le_bound (q := q) hB x
    have h4 := truncPow_le_bound (q := q) hB y
    rw [abs_le]; constructor <;> linarith

@[simp] lemma truncPowBCF_apply (hB : 0 ≤ B) (t : ℝ) : truncPowBCF q B hB t = truncPow q B t :=
  rfl

lemma integrable_truncPow_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (hB : 0 ≤ B) {g : α → ℝ} (hg : Measurable g) :
    Integrable (fun a => truncPow q B (g a)) μ :=
  integrable_of_abs_le (continuous_truncPow.measurable.comp hg) fun a => by
    rw [abs_of_nonneg (truncPow_nonneg hB _)]; exact truncPow_le_bound hB _

end TruncPow

/-! ## Gaussian integrals -/

lemma integral_gaussianReal_eq_scale (v : ℝ≥0) {F : ℝ → ℝ} (hF : Continuous F) :
    ∫ x, F x ∂(gaussianReal 0 v) = ∫ x, F (Real.sqrt v * x) ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp
  rw [← hmap, integral_map (measurable_const_mul _).aemeasurable hF.aestronglyMeasurable]

lemma tendsto_integral_truncPow_gaussian (p : ℕ) (c : ℝ) :
    Tendsto (fun B : ℕ => ∫ x, truncPow (2 * p) B (c * x) ∂(gaussianReal 0 1)) atTop
      (𝓝 (c ^ (2 * p) * ((2 * p - 1)‼ : ℝ))) := by
  have hlim : ∫ x, (c * x) ^ (2 * p) ∂(gaussianReal 0 1) = c ^ (2 * p) * ((2 * p - 1)‼ : ℝ) := by
    simp_rw [mul_pow]
    rw [integral_const_mul, gaussian_even_moment]
  rw [← hlim]
  have hev : Even (2 * p) := even_two_mul p
  refine tendsto_integral_of_dominated_convergence (fun x => (c * x) ^ (2 * p))
    (fun B => (continuous_truncPow.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (by simpa [mul_pow] using (integrable_pow_gaussianReal 1 p).const_mul (c ^ (2 * p)))
    (fun B => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (truncPow_nonneg (Nat.cast_nonneg B) _), ← hev.pow_abs]
    exact truncPow_le_abs_pow (Nat.cast_nonneg B) _
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|c * x|⌉₊] with B hB
    rw [truncPow, min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hB)), hev.pow_abs]

/-! ## The quantitative argument -/

lemma integral_abs_le_of_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ ω, |f ω| ≤ B)
    {η : ℝ} (hη : 0 < η) (h : ∫ ω, f ω ^ 2 ∂μ ≤ η ^ 2) : ∫ ω, |f ω| ∂μ ≤ η := by
  have hi1 : Integrable (fun ω => |f ω|) μ :=
    integrable_of_abs_le hf.abs fun ω => by rw [abs_abs]; exact hB ω
  have hi2 : Integrable (fun ω => f ω ^ 2) μ :=
    integrable_of_abs_le (hf.pow_const 2) fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB ω) 2
  have hpt : ∀ ω, |f ω| ≤ f ω ^ 2 / (2 * η) + η / 2 := fun ω => by
    have key : 2 * η * |f ω| ≤ f ω ^ 2 + η ^ 2 := by nlinarith [sq_nonneg (|f ω| - η), sq_abs (f ω)]
    rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    nlinarith
  calc ∫ ω, |f ω| ∂μ ≤ ∫ ω, (f ω ^ 2 / (2 * η) + η / 2) ∂μ :=
        integral_mono hi1 ((hi2.div_const _).add (integrable_const _)) hpt
    _ = (∫ ω, f ω ^ 2 ∂μ) / (2 * η) + η / 2 := by
        rw [integral_add (hi2.div_const _) (integrable_const _), integral_div, integral_const]
        simp
    _ ≤ η ^ 2 / (2 * η) + η / 2 := by gcongr
    _ = η := by field_simp; ring

/-- If `‖Y_n - Y'_n‖_{L²} ≤ η` for a small `η`, the moment deficit of `Y_n` excludes Gaussian weak
subsequential limits of `Y'_n`. -/
theorem no_gaussian_of_close {p : ℕ} (hp : 2 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > (0 : ℝ), ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Y Y' : ℕ → Ω → ℝ), (∀ n, Measurable (Y n)) → (∀ n, Measurable (Y' n)) →
      (∀ n, ∃ B, ∀ ω, |Y n ω| ≤ B) → (∀ n, ∃ B, ∀ ω, |Y' n ω| ≤ B) →
      (∀ n, 1 ≤ n → ∫ ω, Y n ω ^ 2 ∂μ = 1) →
      (∃ n₀ : ℕ, ∀ n ≥ n₀, ∫ ω, Y n ω ^ (2 * p) ∂μ ≤ ((2 * p - 1)‼ : ℝ) - δ) →
      (∀ n, ∫ ω, (Y n ω - Y' n ω) ^ 2 ∂μ ≤ η ^ 2) →
      ∀ nk : ℕ → ℕ, StrictMono nk → ∀ v : ℝ≥0,
        ¬ ConvergesInDistribution μ (fun k => Y' (nk k)) (gaussianReal 0 v) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  set D : ℝ := ((2 * (m + 1) - 1)‼ : ℝ)
  have hD1 : 1 ≤ D := Nat.one_le_cast.2 (Nat.doubleFactorial_pos _)
  -- the constants
  set x0 : ℝ := min (1 / 2) (δ / (4 * D * (m + 1)))
  have hx0 : 0 < x0 := lt_min (by norm_num) (by positivity)
  have hx0h : x0 ≤ 1 / 2 := min_le_left _ _
  have hx0δ : D * (m + 1) * x0 ≤ δ / 4 := by
    have := min_le_right (1 / 2) (δ / (4 * D * (m + 1)))
    calc D * (m + 1) * x0 ≤ D * (m + 1) * (δ / (4 * D * (m + 1))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = δ / 4 := by field_simp
  set vm : ℝ := 1 - x0
  have hvm0 : 0 < vm := by simp only [vm]; linarith
  have hvmD : D - δ / 4 ≤ D * vm ^ (m + 1) := by
    have hb := one_add_mul_le_pow (a := -x0) (by linarith) (m + 1)
    have : D * (1 + ((m + 1 : ℕ) : ℝ) * -x0) ≤ D * vm ^ (m + 1) := by
      simp only [vm, sub_eq_add_neg]
      exact mul_le_mul_of_nonneg_left (by simpa [add_comm] using hb) (by linarith)
    push_cast at this
    nlinarith
  -- the Gaussian truncation level
  have hGt := tendsto_integral_truncPow_gaussian (m + 1) (Real.sqrt vm)
  have hcv : Real.sqrt vm ^ (2 * (m + 1)) = vm ^ (m + 1) := by
    rw [pow_mul, Real.sq_sqrt hvm0.le]
  rw [hcv] at hGt
  obtain ⟨B, hB1, hB⟩ : ∃ B : ℕ, 1 ≤ B ∧
      D - δ / 2 ≤ ∫ x, truncPow (2 * (m + 1)) B (Real.sqrt vm * x) ∂(gaussianReal 0 1) := by
    have hev := hGt.eventually (lt_mem_nhds (show vm ^ (m + 1) * D - δ / 4 < vm ^ (m + 1) * D by
      linarith))
    obtain ⟨B, hB⟩ := (hev.and (eventually_ge_atTop 1)).exists
    exact ⟨B, hB.2, by linarith [hB.1]⟩
  set Bℝ : ℝ := (B : ℝ)
  have hBℝ : 1 ≤ Bℝ := Nat.one_le_cast.2 hB1
  -- the second-moment truncation level
  set A : ℝ := max 1 (2 * D / x0)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := by linarith
  have hAtail : D / A ^ (2 * m) ≤ x0 / 2 := by
    have h1 : 2 * D / x0 ≤ A ^ (2 * m) := (le_max_right _ _).trans (le_self_pow₀ hA1 (by omega))
    rw [div_le_iff₀ (by positivity)]
    calc D = x0 / 2 * (2 * D / x0) := by field_simp
      _ ≤ x0 / 2 * A ^ (2 * m) := mul_le_mul_of_nonneg_left h1 (by positivity)
  -- the closeness threshold
  set Lip : ℝ := ((2 * (m + 1) : ℕ) : ℝ) * Bℝ ^ (2 * (m + 1) - 1)
  have hLip : 0 < Lip := by positivity
  set η : ℝ := min (x0 / (4 * A)) (δ / (4 * Lip))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  refine ⟨η, hη, ?_⟩
  intro Ω _ μ _ Y Y' hY hY' hYb hY'b h2 hL hclose nk hnk v hconv
  obtain ⟨n₀, hn₀⟩ := hL
  have hev : ∀ N, ∀ᶠ k in atTop, N ≤ nk k := fun N =>
    (eventually_ge_atTop N).mono fun k hk => hk.trans (hnk.id_le k)
  have hYpow : ∀ n (q : ℕ), Integrable (fun ω => Y n ω ^ q) μ := fun n q => by
    obtain ⟨B1, hB1⟩ := hYb n
    exact integrable_of_abs_le ((hY n).pow_const q) fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB1 ω) q
  have habs : ∀ n, ∫ ω, |Y n ω - Y' n ω| ∂μ ≤ η := fun n => by
    obtain ⟨B1, hB1⟩ := hYb n
    obtain ⟨B2, hB2⟩ := hY'b n
    exact integral_abs_le_of_sq ((hY n).sub (hY' n)) (B := B1 + B2)
      (fun ω => (abs_sub _ _).trans (add_le_add (hB1 ω) (hB2 ω))) hη (hclose n)
  have hlipdiff : ∀ (q : ℕ) (Bq : ℝ), 0 ≤ Bq → ∀ n,
      |∫ ω, truncPow q Bq (Y n ω) ∂μ - ∫ ω, truncPow q Bq (Y' n ω) ∂μ| ≤ q * Bq ^ (q - 1) * η := by
    intro q Bq hBq n
    obtain ⟨B1, hB1⟩ := hYb n
    obtain ⟨B2, hB2⟩ := hY'b n
    have i1 := integrable_truncPow_comp (μ := μ) (q := q) hBq (hY n)
    have i2 := integrable_truncPow_comp (μ := μ) (q := q) hBq (hY' n)
    have i3 : Integrable (fun ω => |Y n ω - Y' n ω|) μ :=
      integrable_of_abs_le ((hY n).sub (hY' n)).abs fun ω => by
        rw [abs_abs]; exact (abs_sub _ _).trans (add_le_add (hB1 ω) (hB2 ω))
    rw [← integral_sub i1 i2]
    calc |∫ ω, (truncPow q Bq (Y n ω) - truncPow q Bq (Y' n ω)) ∂μ|
        ≤ ∫ ω, |truncPow q Bq (Y n ω) - truncPow q Bq (Y' n ω)| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, q * Bq ^ (q - 1) * |Y n ω - Y' n ω| ∂μ :=
          integral_mono (i1.sub i2).abs (i3.const_mul _) fun ω => abs_truncPow_sub_le hBq _ _
      _ = q * Bq ^ (q - 1) * ∫ ω, |Y n ω - Y' n ω| ∂μ := integral_const_mul _ _
      _ ≤ q * Bq ^ (q - 1) * η := mul_le_mul_of_nonneg_left (habs n) (by positivity)
  -- `v ≥ vm`
  set u1 := truncPowBCF 2 A hA0.le
  have hv : vm ≤ v := by
    have hlow : ∀ᶠ k in atTop, vm ≤ ∫ ω, u1 (Y' (nk k) ω) ∂μ := by
      filter_upwards [hev (max n₀ 1)] with k hk
      set n := nk k
      have hn1 : 1 ≤ n := le_of_max_le_right hk
      have hn0 : n₀ ≤ n := le_of_max_le_left hk
      have hYL := hn₀ n hn0
      have h1 : 1 - x0 / 2 ≤ ∫ ω, truncPow 2 A (Y n ω) ∂μ := by
        have hApos : 0 < A ^ (2 * m) := by positivity
        calc 1 - x0 / 2 ≤ 1 - D / A ^ (2 * m) := by linarith
          _ ≤ ∫ ω, Y n ω ^ 2 ∂μ - (∫ ω, Y n ω ^ (2 * (m + 1)) ∂μ) / A ^ (2 * m) := by
              rw [h2 n hn1]
              have : (∫ ω, Y n ω ^ (2 * (m + 1)) ∂μ) / A ^ (2 * m) ≤ D / A ^ (2 * m) :=
                div_le_div_of_nonneg_right (by linarith) hApos.le
              linarith
          _ = ∫ ω, (Y n ω ^ 2 - Y n ω ^ (2 * (m + 1)) / A ^ (2 * m)) ∂μ := by
              rw [integral_sub (hYpow n 2) ((hYpow n _).div_const _), integral_div]
          _ ≤ ∫ ω, truncPow 2 A (Y n ω) ∂μ :=
              integral_mono ((hYpow n 2).sub ((hYpow n _).div_const _))
                (integrable_truncPow_comp hA0.le (hY n)) fun ω => sq_sub_le_truncPow hA0 m _
      have h2' := hlipdiff 2 A hA0.le n
      have hηA : 2 * A * η ≤ x0 / 2 := by
        have := min_le_left (x0 / (4 * A)) (δ / (4 * Lip))
        calc 2 * A * η ≤ 2 * A * (x0 / (4 * A)) := mul_le_mul_of_nonneg_left this (by positivity)
          _ = x0 / 2 := by field_simp; ring
      simp only [u1, truncPowBCF_apply]
      norm_num at h2'
      have := (abs_le.1 h2').2
      simp only [vm]
      linarith
    have hlim := ge_of_tendsto (hconv u1) hlow
    calc vm ≤ ∫ x, u1 x ∂(gaussianReal 0 v) := hlim
      _ ≤ ∫ x, x ^ 2 ∂(gaussianReal 0 v) :=
          integral_mono (u1.integrable _) (by simpa using integrable_pow_gaussianReal v 1)
            fun x => by
              simp only [u1, truncPowBCF_apply]
              exact (truncPow_le_abs_pow hA0.le x).trans (by rw [sq_abs])
      _ = v := integral_sq_gaussianReal v
  -- upper bound for the `2p`-th truncated moment of the limit
  set u2 := truncPowBCF (2 * (m + 1)) Bℝ (by linarith)
  have hup : ∫ x, u2 x ∂(gaussianReal 0 v) ≤ D - δ + δ / 4 := by
    have hev2 : ∀ᶠ k in atTop, ∫ ω, u2 (Y' (nk k) ω) ∂μ ≤ D - δ + δ / 4 := by
      filter_upwards [hev n₀] with k hk
      set n := nk k
      have h1 : ∫ ω, truncPow (2 * (m + 1)) Bℝ (Y n ω) ∂μ ≤ D - δ := by
        refine (integral_mono (integrable_truncPow_comp (by linarith) (hY n)) (hYpow n _)
          fun ω => ?_).trans (hn₀ n hk)
        rw [← (even_two_mul (m + 1)).pow_abs]
        exact truncPow_le_abs_pow (by linarith) _
      have h2' := hlipdiff (2 * (m + 1)) Bℝ (by linarith) n
      have hηL : ((2 * (m + 1) : ℕ) : ℝ) * Bℝ ^ (2 * (m + 1) - 1) * η ≤ δ / 4 := by
        have := min_le_right (x0 / (4 * A)) (δ / (4 * Lip))
        calc Lip * η ≤ Lip * (δ / (4 * Lip)) := mul_le_mul_of_nonneg_left this hLip.le
          _ = δ / 4 := by field_simp
      simp only [u2, truncPowBCF_apply]
      have := (abs_le.1 h2').1
      linarith
    exact le_of_tendsto (hconv u2) hev2
  -- lower bound for the `2p`-th truncated moment of `N(0, v)`, `v ≥ vm`
  have hlowG : D - δ / 2 ≤ ∫ x, u2 x ∂(gaussianReal 0 v) := by
    rw [integral_gaussianReal_eq_scale v u2.continuous]
    refine hB.trans (integral_mono
      (integrable_truncPow_comp (by linarith) (measurable_const_mul _))
      (integrable_truncPow_comp (by linarith) (measurable_const_mul _)) fun x => ?_)
    simp only [u2, truncPowBCF_apply, truncPow]
    refine pow_le_pow_left₀ (le_min (abs_nonneg _) (by linarith)) (min_le_min_right _ ?_) _
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hv) (abs_nonneg _)
  linarith

/-! ## Proposition `prop:robustness` -/

lemma abs_div_sqrt_le (a : ℝ) (n : ℕ) : |a / Real.sqrt n| ≤ |a| := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by exact_mod_cast h))]
    exact div_le_self (abs_nonneg _) (Real.one_le_sqrt.2 (by exact_mod_cast h))

/-- **Proposition `prop:robustness`**: under exponential two-point mixing for Lipschitz
observables, the moment deficit of `S_n f₀ / √n` persists for every `g` in a Lipschitz
neighbourhood of `f₀`. -/
theorem robust_of_moments {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasurePreserving T μ μ) (hmix : ExpMixingOrder μ T LipBound 2) {f₀ : X → ℝ}
    (hf₀ : Measurable f₀) {B₀ : ℝ} (hf₀b : ∀ x, |f₀ x| ≤ B₀) (hcent : ∫ x, f₀ x ∂μ = 0)
    {p : ℕ} (hp : 2 ≤ p)
    (h2 : ∀ n, 1 ≤ n → ∫ x, (birkhoffSum T f₀ n x / Real.sqrt n) ^ 2 ∂μ = 1)
    (hL : ∃ δ > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∫ x, (birkhoffSum T f₀ n x / Real.sqrt n) ^ (2 * p) ∂μ ≤ ((2 * p - 1)‼ : ℝ) - δ) :
    ∃ δ > (0 : ℝ), ∀ g : X → ℝ, LipBound (g - f₀) δ →
      NoGaussianSubseqLimit μ (birkhoffSum T fun x => g x - ∫ y, g y ∂μ) := by
  obtain ⟨δL, hδL, hn0⟩ := hL
  obtain ⟨η, hη, hmain⟩ := no_gaussian_of_close hp hδL
  obtain ⟨C, c, hc, hmix2⟩ := hmix
  set C' := max C 0
  set r := Real.exp (-c)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set K0 : ℝ := 1 + 2 * (C' * (r / (1 - r)))
  have hK0 : 1 ≤ K0 := by
    have : 0 ≤ C' * (r / (1 - r)) :=
      mul_nonneg (le_max_right _ _) (div_nonneg hr0 (by linarith))
    simp only [K0]; linarith
  set δ' : ℝ := η / (2 * (K0 + 1))
  have hδ' : 0 < δ' := by positivity
  have hB₀ : 0 ≤ B₀ := (abs_nonneg _).trans (hf₀b (Classical.choice
    (nonempty_of_isProbabilityMeasure μ)))
  refine ⟨δ', hδ', fun g hg => ?_⟩
  set e : X → ℝ := g - f₀
  have hem : Measurable e := hg.continuous.measurable
  have hge : g = fun x => e x + f₀ x := funext fun x => by simp [e]
  have hgm : Measurable g := by rw [hge]; exact hem.add hf₀
  have hei : Integrable e μ := integrable_of_abs_le hem hg.1
  have hf₀i : Integrable f₀ μ := integrable_of_abs_le hf₀ hf₀b
  set me : ℝ := ∫ x, e x ∂μ
  have hme : |me| ≤ δ' := by
    calc |me| ≤ ∫ x, |e x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _x, δ' ∂μ := integral_mono hei.abs (integrable_const _) hg.1
      _ = δ' := by simp
  set h : X → ℝ := fun x => e x - me
  have hh : LipBound h (2 * δ') := by
    refine ⟨fun x => (abs_sub _ _).trans (by linarith [hg.1 x]), fun x y => ?_⟩
    have : h x - h y = e x - e y := by simp only [h]; ring
    rw [this]
    exact (hg.2 x y).trans (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
  have hhm : Measurable h := hem.sub measurable_const
  have hh0 : ∫ x, h x ∂μ = 0 := by
    simp only [h]; rw [integral_sub hei (integrable_const _)]; simp [me]
  have hcorr : ∀ k : ℕ, 1 ≤ k →
      |∫ x, h x * h (T^[k] x) ∂μ| ≤ C' * Real.exp (-c * k) * (2 * δ') ^ 2 := by
    intro k hk
    have hmono : StrictMono ![0, k] :=
      Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; simp; omega
    have hgap : Gapped ![0, k] (k : ℝ) := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd hij (lt_irrefl _)
      · simp
      · exact absurd hij (by decide)
      · exact absurd hij (lt_irrefl _)
    have := hmix2 ![h, h] ![2 * δ', 2 * δ'] (fun i => by fin_cases i <;> exact hh) ![0, k]
      hmono k hgap
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Function.iterate_zero, id, hh0, mul_zero, sub_zero] at this
    refine this.trans ?_
    rw [show 2 * δ' * (2 * δ') = (2 * δ') ^ 2 by ring]
    gcongr
    exact le_max_left _ _
  have hvar := integral_birkhoffSum_sq_le hT hhm hh.1 hc (le_max_right C 0) hcorr
  -- the two normalised sequences
  have hsum : ∀ n x, birkhoffSum T (fun x => g x - ∫ y, g y ∂μ) n x =
      birkhoffSum T f₀ n x + birkhoffSum T h n x := by
    have hint : ∫ y, g y ∂μ = me := by
      rw [hge, integral_add hei hf₀i, hcent, add_zero]
    have hfun : (fun x => g x - ∫ y, g y ∂μ) = f₀ + h := by
      funext x; rw [hint, hge]; simp only [h, Pi.add_apply]; ring
    intro n x
    rw [hfun, birkhoffSum_add]
    rfl
  set Y : ℕ → X → ℝ := fun n x => birkhoffSum T f₀ n x / Real.sqrt n
  set Y' : ℕ → X → ℝ := fun n x => birkhoffSum T (fun x => g x - ∫ y, g y ∂μ) n x / Real.sqrt n
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    (measurable_birkhoffSum hT.measurable hf₀ n).div_const _
  have hY'm : ∀ n, Measurable (Y' n) := fun n =>
    (measurable_birkhoffSum hT.measurable (hgm.sub measurable_const) n).div_const _
  have hYb : ∀ n, ∃ B, ∀ x, |Y n x| ≤ B := fun n =>
    ⟨n * B₀, fun x => (abs_div_sqrt_le _ _).trans (abs_birkhoffSum_le hf₀b n x)⟩
  have hY'b : ∀ n, ∃ B, ∀ x, |Y' n x| ≤ B := fun n =>
    ⟨n * B₀ + n * (2 * δ'), fun x => by
      refine (abs_div_sqrt_le _ _).trans ?_
      rw [hsum]
      exact (abs_add_le _ _).trans (add_le_add (abs_birkhoffSum_le hf₀b n x)
        (abs_birkhoffSum_le hh.1 n x))⟩
  have hclose : ∀ n, ∫ x, (Y n x - Y' n x) ^ 2 ∂μ ≤ η ^ 2 := by
    intro n
    have hdiff : ∀ x, (Y n x - Y' n x) ^ 2 = birkhoffSum T h n x ^ 2 / n := fun x => by
      simp only [Y, Y', hsum]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · rw [div_sub_div_same, sub_add_cancel_left, neg_div, neg_sq, div_pow,
          Real.sq_sqrt (Nat.cast_nonneg _)]
    simp_rw [hdiff]
    rw [integral_div]
    have hK : (2 * δ') ^ 2 * K0 ≤ η ^ 2 := by
      have : (2 * δ') ^ 2 = η ^ 2 / (K0 + 1) ^ 2 := by simp only [δ']; field_simp
      rw [this, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [Nat.cast_zero, div_zero]; positivity
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_iff₀ hnpos]
      refine (hvar n).trans ?_
      have : (2 * δ') ^ 2 + 2 * (C' * (2 * δ') ^ 2 * (r / (1 - r))) = (2 * δ') ^ 2 * K0 := by
        simp only [K0]; ring
      rw [this]
      nlinarith
  exact fun nk hnk v => hmain μ Y Y' hYm hY'm hYb hY'b h2 hn0 hclose nk hnk v

/-! ## Robustness through a horseshoe coding -/

/-- Proposition `prop:robustness` for the realisation `μ = cod_* ν` of Theorem C: some Lipschitz
neighbourhood of `f₀` has no Gaussian weak subsequential limit. -/
theorem robust_of_coding {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {R : ℕ}
    (hR : 2 ≤ R) {ν : Measure Config} (hν : SymbolicProperties R ν) {T : X → X}
    (hT : Measurable T) {cod : Config → X} (hc : HorseshoeCoding T cod) {f₀ : X → ℝ}
    (hf₀c : Continuous f₀) (hf₀ : ∀ ω, f₀ (cod ω) = Z 0 ω) {B₀ : ℝ} (hf₀b : ∀ x, |f₀ x| ≤ B₀) :
    ∃ δ > (0 : ℝ), ∀ g : X → ℝ, LipBound (g - f₀) δ →
      NoGaussianSubseqLimit (ν.map cod) (birkhoffSum T fun x => g x - ∫ y, g y ∂(ν.map cod)) := by
  have := hν.isProb
  have hm := hc.continuous.measurable
  have hf₀m := hf₀c.measurable
  obtain ⟨θ, hθ0, hθ1, κ, -, hhold⟩ := hc.exists_holder
  have hmix := expMixing_map hT hc hhold (hν.mixing θ hθ0 hθ1 2 le_rfl hR)
  have hcent : ∫ x, f₀ x ∂(ν.map cod) = 0 := by
    rw [integral_map_cod hm ν hf₀m]; simp_rw [hf₀]; exact integral_Z_eq_zero hν.signs 0
  have hmom : ∀ (q n : ℕ), ∫ x, (birkhoffSum T f₀ n x / Real.sqrt n) ^ q ∂(ν.map cod) =
      ∫ ω, (S n ω / Real.sqrt n) ^ q ∂ν := fun q n => by
    rw [integral_map_cod (F := fun x => (birkhoffSum T f₀ n x / Real.sqrt n) ^ q) hm ν
      (((measurable_birkhoffSum hT hf₀m n).div_const _).pow_const q)]
    simp_rw [birkhoffSum_cod hc hf₀]
  refine robust_of_moments (measurePreserving_map hν.invariant hT hc) hmix hf₀m hf₀b hcent
    (p := R + 1) (by omega) (fun n hn => ?_) ?_
  · rw [hmom]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp_rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [integral_div, integral_S_sq_of_props (by omega) hν n, div_self hn'.ne']
  · obtain ⟨δ, hδ, n₀, h⟩ := hν.moment
    refine ⟨δ, hδ, n₀, fun n hn => ?_⟩
    rw [hmom, show 2 * (R + 1) = 2 * R + 2 by ring, show 2 * R + 2 - 1 = 2 * R + 1 by omega]
    exact h n hn

end FiniteOrderMixing
