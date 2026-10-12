import FiniteOrderMixing.Realisation.Transfer

/-!
# Second moments of Birkhoff sums (Lemma `lem:variance`) and a law of large numbers

* `integral_birkhoffSum_sq_le` — **Lemma `lem:variance`**: if `h` is centred, bounded by `A` and
  `|μ(h · h∘T^k)| ≤ C e^{-ck} A²` for `k ≥ 1`, then `‖S_n h‖²_{L²} ≤ n K A²`;
* `ae_tendsto_birkhoffSum_div` — under such a variance bound, `S_n h / n → 0` almost surely
  (Chebyshev and Borel–Cantelli along the squares, then interpolation).  This replaces the use of
  Birkhoff's ergodic theorem in Proposition `prop:physical-transfer`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace FiniteOrderMixing

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {T : Y → Y}

lemma integrable_of_abs_le [IsFiniteMeasure μ] {f : Y → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall fun x => hB x)

omit [MeasurableSpace Y] in
lemma abs_birkhoffSum_le {h : Y → ℝ} {A : ℝ} (hA : ∀ x, |h x| ≤ A) (n : ℕ) (x : Y) :
    |birkhoffSum T h n x| ≤ n * A := by
  unfold birkhoffSum
  calc |∑ k ∈ Finset.range n, h (T^[k] x)| ≤ ∑ k ∈ Finset.range n, |h (T^[k] x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, A := Finset.sum_le_sum fun k _ => hA _
    _ = n * A := by simp

lemma integral_comp_iterate (hT : MeasurePreserving T μ μ) {F : Y → ℝ} (hF : Measurable F)
    (i : ℕ) : ∫ x, F (T^[i] x) ∂μ = ∫ x, F x ∂μ := by
  conv_rhs => rw [← (hT.iterate i).map_eq]
  rw [integral_map (hT.iterate i).measurable.aemeasurable hF.aestronglyMeasurable]

omit [MeasurableSpace Y] in
lemma sum_pow_sub_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ (n - i) ≤ r / (1 - r) := by
  induction n with
  | zero => simp; positivity
  | succ n ih =>
    rw [Finset.sum_range_succ, show n + 1 - n = 1 by omega, pow_one]
    have : ∑ i ∈ Finset.range n, r ^ (n + 1 - i) = r * ∑ i ∈ Finset.range n, r ^ (n - i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        rw [show n + 1 - i = (n - i) + 1 by have := Finset.mem_range.1 hi; omega, pow_succ,
          mul_comm]
    rw [this]
    have h1r : 0 < 1 - r := by linarith
    calc r * ∑ i ∈ Finset.range n, r ^ (n - i) + r ≤ r * (r / (1 - r)) + r := by
          gcongr
      _ = r / (1 - r) := by field_simp; ring

/-- **Lemma `lem:variance`.** -/
theorem integral_birkhoffSum_sq_le [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {h : Y → ℝ} (hh : Measurable h) {A C c : ℝ} (hA : ∀ x, |h x| ≤ A) (hc : 0 < c) (hC : 0 ≤ C)
    (hcorr : ∀ k : ℕ, 1 ≤ k → |∫ x, h x * h (T^[k] x) ∂μ| ≤ C * Real.exp (-c * k) * A ^ 2)
    (n : ℕ) :
    ∫ x, birkhoffSum T h n x ^ 2 ∂μ ≤
      n * (A ^ 2 + 2 * (C * A ^ 2 * (Real.exp (-c) / (1 - Real.exp (-c))))) := by
  set r := Real.exp (-c)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hTm := hT.measurable
  have hhi : ∀ k, Measurable fun x => h (T^[k] x) := fun k => hh.comp (hTm.iterate k)
  have hSm : ∀ m, Measurable (birkhoffSum T h m) := measurable_birkhoffSum hTm hh
  have hA0 : 0 ≤ A := by
    have := hA (Classical.choice (nonempty_of_isProbabilityMeasure μ))
    exact (abs_nonneg _).trans this
  induction n with
  | zero => simp [birkhoffSum_zero_apply]
  | succ n ih =>
    have hsucc : ∀ x, birkhoffSum T h (n + 1) x ^ 2 = birkhoffSum T h n x ^ 2 +
        2 * (birkhoffSum T h n x * h (T^[n] x)) + h (T^[n] x) ^ 2 := fun x => by
      rw [birkhoffSum_succ_apply]; ring
    have hb : ∀ m x, |birkhoffSum T h m x| ≤ m * A := fun m x => abs_birkhoffSum_le hA m x
    have i1 : Integrable (fun x => birkhoffSum T h n x ^ 2) μ :=
      integrable_of_abs_le ((hSm n).pow_const 2) fun x => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb n x) 2
    have i2 : Integrable (fun x => birkhoffSum T h n x * h (T^[n] x)) μ :=
      integrable_of_abs_le ((hSm n).mul (hhi n)) fun x => by
        rw [abs_mul]; exact mul_le_mul (hb n x) (hA _) (abs_nonneg _) (by positivity)
    have i3 : Integrable (fun x => h (T^[n] x) ^ 2) μ :=
      integrable_of_abs_le ((hhi n).pow_const 2) fun x => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hA _) 2
    -- the cross term
    have hcross : ∫ x, birkhoffSum T h n x * h (T^[n] x) ∂μ ≤ C * A ^ 2 * (r / (1 - r)) := by
      have hsplit : ∀ x, birkhoffSum T h n x * h (T^[n] x) =
          ∑ i ∈ Finset.range n, h (T^[i] x) * h (T^[n] x) := fun x => by
        rw [birkhoffSum, Finset.sum_mul]
      simp_rw [hsplit]
      rw [integral_finsetSum _ fun i _ => integrable_of_abs_le
        (f := fun x => h (T^[i] x) * h (T^[n] x)) ((hhi i).mul (hhi n)) fun x => by
          rw [abs_mul]; exact mul_le_mul (hA _) (hA _) (abs_nonneg _) hA0]
      have hterm : ∀ i ∈ Finset.range n, ∫ x, h (T^[i] x) * h (T^[n] x) ∂μ ≤
          C * A ^ 2 * r ^ (n - i) := by
        intro i hi
        have hin := Finset.mem_range.1 hi
        have heq : ∫ x, h (T^[i] x) * h (T^[n] x) ∂μ = ∫ x, h x * h (T^[n - i] x) ∂μ := by
          rw [← integral_comp_iterate hT (F := fun x => h x * h (T^[n - i] x))
            (hh.mul (hhi (n - i))) i]
          congr 1; funext x
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hin.le]
        rw [heq]
        refine (le_abs_self _).trans ((hcorr (n - i) (by omega)).trans (le_of_eq ?_))
        rw [show -c * ((n - i : ℕ) : ℝ) = ((n - i : ℕ) : ℝ) * (-c) by ring, Real.exp_nat_mul]
        ring
      calc ∑ i ∈ Finset.range n, ∫ x, h (T^[i] x) * h (T^[n] x) ∂μ
          ≤ ∑ i ∈ Finset.range n, C * A ^ 2 * r ^ (n - i) := Finset.sum_le_sum hterm
        _ = C * A ^ 2 * ∑ i ∈ Finset.range n, r ^ (n - i) := by rw [Finset.mul_sum]
        _ ≤ C * A ^ 2 * (r / (1 - r)) :=
          mul_le_mul_of_nonneg_left (sum_pow_sub_le hr0 hr1 n) (by positivity)
    have hdiag : ∫ x, h (T^[n] x) ^ 2 ∂μ ≤ A ^ 2 := by
      refine (integral_mono i3 (integrable_const (A ^ 2)) fun x => ?_).trans (by simp)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA _) 2
    simp_rw [hsucc]
    rw [integral_add (f := fun x => birkhoffSum T h n x ^ 2 +
        2 * (birkhoffSum T h n x * h (T^[n] x))) (i1.add (i2.const_mul 2)) i3,
      integral_add (f := fun x => birkhoffSum T h n x ^ 2) i1 (i2.const_mul 2),
      integral_const_mul]
    push_cast
    linarith

/-! ## A law of large numbers from the variance bound -/

lemma tendsto_sqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b * b, fun _ hn => Nat.le_sqrt.2 hn⟩

/-- If `‖S_n h‖²_{L²} ≤ n K`, then `S_n h / n → 0` almost surely. -/
theorem ae_tendsto_birkhoffSum_div [IsProbabilityMeasure μ] (hT : Measurable T) {h : Y → ℝ}
    (hh : Measurable h) {A K : ℝ} (hA0 : 0 ≤ A) (hA : ∀ x, |h x| ≤ A)
    (hK : ∀ n : ℕ, ∫ x, birkhoffSum T h n x ^ 2 ∂μ ≤ n * K) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T h n x / n) atTop (𝓝 0) := by
  have hSm : ∀ m, Measurable (birkhoffSum T h m) := measurable_birkhoffSum hT hh
  have hK0 : 0 ≤ K := by
    have := hK 1
    simp only [Nat.cast_one, one_mul] at this
    exact (integral_nonneg fun x => sq_nonneg _).trans this
  -- Step 1: along the squares
  have hsq : ∀ m : ℕ, ∀ᵐ x ∂μ, ∀ᶠ k in atTop,
      x ∉ {x | 1 / ((m : ℝ) + 1) ≤ |birkhoffSum T h (k ^ 2) x| / ((k : ℝ) ^ 2)} := by
    intro m
    set ε : ℝ := 1 / ((m : ℝ) + 1)
    have hε : 0 < ε := by positivity
    set b : ℕ → ℝ := fun k => K / ε ^ 2 * (1 / (k : ℝ) ^ 2)
    have hb0 : ∀ k, 0 ≤ b k := fun k => by positivity
    have hbs : Summable b :=
      (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2)).mul_left _
    refine ae_eventually_notMem (ne_top_of_le_ne_top (b := ENNReal.ofReal (∑' k, b k)) ?_ ?_)
    · exact ENNReal.ofReal_ne_top
    rw [ENNReal.ofReal_tsum_of_nonneg hb0 hbs]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have : {x | ε ≤ |birkhoffSum T h (0 ^ 2) x| / ((0 : ℕ) : ℝ) ^ 2} = (∅ : Set Y) :=
        Set.eq_empty_of_forall_notMem fun x hx => by norm_num at hx; linarith
      rw [this, measure_empty]; simp
    · have hkpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      set t : ℝ := ε ^ 2 * ((k : ℝ) ^ 2) ^ 2
      have ht : 0 < t := by positivity
      have hsub : {x | ε ≤ |birkhoffSum T h (k ^ 2) x| / ((k : ℝ) ^ 2)} ⊆
          {x | t ≤ birkhoffSum T h (k ^ 2) x ^ 2} := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [le_div_iff₀ hkpos] at hx
        have h0 : 0 ≤ ε * (k : ℝ) ^ 2 := by positivity
        calc t = (ε * (k : ℝ) ^ 2) ^ 2 := by ring
          _ ≤ |birkhoffSum T h (k ^ 2) x| ^ 2 := pow_le_pow_left₀ h0 hx 2
          _ = _ := sq_abs _
      have hint : Integrable (fun x => birkhoffSum T h (k ^ 2) x ^ 2) μ :=
        integrable_of_abs_le ((hSm _).pow_const 2) fun x => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_birkhoffSum_le hA _ x) 2
      have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
        hint t
      have hreal : μ.real {x | t ≤ birkhoffSum T h (k ^ 2) x ^ 2} ≤ b k := by
        rw [← mul_le_mul_iff_of_pos_left ht]
        refine hmk.trans ((hK _).trans (le_of_eq ?_))
        simp only [b, t]
        push_cast
        field_simp
      calc μ {x | ε ≤ |birkhoffSum T h (k ^ 2) x| / ((k : ℝ) ^ 2)}
          ≤ μ {x | t ≤ birkhoffSum T h (k ^ 2) x ^ 2} := measure_mono hsub
        _ = ENNReal.ofReal (μ.real {x | t ≤ birkhoffSum T h (k ^ 2) x ^ 2}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal (b k) := ENNReal.ofReal_le_ofReal hreal
  rw [← ae_all_iff] at hsq
  filter_upwards [hsq] with x hx
  -- along the squares
  have hsqk : Tendsto (fun k : ℕ => |birkhoffSum T h (k ^ 2) x| / ((k : ℝ) ^ 2)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := (hx m).exists_forall_of_atTop
    refine ⟨N, fun k hk => ?_⟩
    have := hN k hk
    simp only [not_le] at this
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    exact this.trans hm
  -- interpolation
  have hg : Tendsto (fun k : ℕ => |birkhoffSum T h (k ^ 2) x| / ((k : ℝ) ^ 2) + 2 * A / k)
      atTop (𝓝 0) := by
    simpa using hsqk.add ((tendsto_const_div_atTop_nhds_zero_nat (2 * A)))
  refine squeeze_zero_norm' ?_ (hg.comp tendsto_sqrt_atTop)
  filter_upwards [eventually_ge_atTop 1] with n hn
  set k := Nat.sqrt n
  have hk1 : 1 ≤ k := Nat.le_sqrt.2 (by simpa using hn)
  have hkn : k ^ 2 ≤ n := Nat.sqrt_le' n
  have hnk : n < (k + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hkpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit := birkhoffSum_add_right_apply T h (k ^ 2) (n - k ^ 2) x
  rw [Nat.add_sub_cancel' hkn] at hsplit
  have hrest : |birkhoffSum T h (n - k ^ 2) (T^[k ^ 2] x)| ≤ 2 * k * A := by
    refine (abs_birkhoffSum_le hA _ _).trans ?_
    have : ((n - k ^ 2 : ℕ) : ℝ) ≤ 2 * k := by
      have : n - k ^ 2 ≤ 2 * k := by
        rw [Nat.sub_le_iff_le_add]; nlinarith [hnk]
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right this hA0
  simp only [Function.comp, Real.norm_eq_abs]
  rw [abs_div, abs_of_pos hnpos, hsplit, div_le_iff₀ hnpos]
  have hkn' : (k : ℝ) ^ 2 ≤ n := by exact_mod_cast hkn
  have h1 : |birkhoffSum T h (k ^ 2) x| ≤ |birkhoffSum T h (k ^ 2) x| / (k : ℝ) ^ 2 * n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hkpos]
    exact mul_le_mul_of_nonneg_left hkn' (abs_nonneg _)
  have h2 : 2 * k * A ≤ 2 * A / k * n := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    rw [div_mul_eq_mul_div, le_div_iff₀ hk0]
    have : (k : ℝ) * k ≤ n := by nlinarith
    nlinarith
  calc |birkhoffSum T h (k ^ 2) x + birkhoffSum T h (n - k ^ 2) (T^[k ^ 2] x)|
      ≤ |birkhoffSum T h (k ^ 2) x| + |birkhoffSum T h (n - k ^ 2) (T^[k ^ 2] x)| :=
        abs_add_le _ _
    _ ≤ _ := by nlinarith

end FiniteOrderMixing
