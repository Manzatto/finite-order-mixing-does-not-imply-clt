import FiniteOrderMixing.Realisation.Defs

/-!
# Transporting the symbolic process through a horseshoe coding (Lemma `lem:transfer`)

Let `cod : Σ → X` code a two-symbol horseshoe of `T`, let `ν` be the measure of Theorem C and
`μ = cod_* ν`.  This file proves, for an abstract metric space `X`:

* `HorseshoeCoding.exists_holder` — `‖f ∘ cod‖_θ ≲ ‖f‖_Lip` for `θ = ϱ` (the pullback bound `(12)`);
* `expMixing_map` — exponential mixing passes from `(σ, ν)` to `(T, μ)`;
* `support_map_cod` — `supp μ = cod(Σ)`;
* `orbitProcess_cod`, `birkhoffSum_cod` — `f₀ ∘ cod = Z₀` identifies the processes `(14)`;
* `not_expMixing_of_lower` — a polynomial lower bound on separated correlations excludes
  exponential mixing (Corollary `cor:higher-order`, step 2, for an abstract system);
* `realisationProperties_of_coding` — items (i)–(iv), (vi) of Theorems A and B.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace FiniteOrderMixing

/-! ## The shift as a permutation -/

/-- The left shift as a permutation of `Σ`. -/
def shiftPerm : Equiv.Perm Config where
  toFun := shift
  invFun ω j := ω (j - 1)
  left_inv ω := by funext j; simp [shift]
  right_inv ω := by funext j; simp [shift]

@[simp] lemma shiftPerm_apply (ω : Config) : shiftPerm ω = shift ω := rfl

lemma shiftPerm_inv_apply (ω : Config) (j : ℤ) : (shiftPerm⁻¹ ω) j = ω (j - 1) := rfl

lemma shiftPerm_zpow_apply (i : ℤ) (ω : Config) (j : ℤ) : (shiftPerm ^ i) ω j = ω (j + i) := by
  induction i using Int.induction_on generalizing ω j with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
    simp only [shiftPerm_apply, shift]
    congr 1; ring
  | pred i ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, shiftPerm_inv_apply]
    congr 1; ring

/-! ## Observables -/

lemma measurable_birkhoffSum {Y : Type*} [MeasurableSpace Y] {T : Y → Y} (hT : Measurable T)
    {f : Y → ℝ} (hf : Measurable f) (n : ℕ) : Measurable (birkhoffSum T f n) := by
  unfold birkhoffSum
  exact Finset.measurable_sum _ fun k _ => hf.comp (hT.iterate k)

section Lip

variable {X : Type*} [PseudoMetricSpace X]

lemma LipBound.continuous {f : X → ℝ} {A : ℝ} (hf : LipBound f A) : Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := A.toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.coe_toNNReal']
  exact (hf.2 x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)

lemma LipBound.nonneg [Nonempty X] {f : X → ℝ} {A : ℝ} (hf : LipBound f A) : 0 ≤ A :=
  (abs_nonneg _).trans (hf.1 (Classical.arbitrary X))

lemma LipBound.mono {f : X → ℝ} {A B : ℝ} (hf : LipBound f A) (hAB : A ≤ B) : LipBound f B :=
  ⟨fun x => (hf.1 x).trans hAB, fun x y =>
    (hf.2 x y).trans (mul_le_mul_of_nonneg_right hAB dist_nonneg)⟩

end Lip

/-! ## Horseshoe codings -/

namespace HorseshoeCoding

variable {X : Type*} [MetricSpace X] {T : X → X} {cod : Config → X}

lemma iterate (h : HorseshoeCoding T cod) (n : ℕ) (ω : Config) :
    cod (shift^[n] ω) = T^[n] (cod ω) :=
  (Function.Semiconj.iterate_right (f := cod) (ga := shift) (gb := T) h.conj n) ω

lemma zpow {T : Equiv.Perm X} (h : HorseshoeCoding T cod) (i : ℤ) (ω : Config) :
    cod ((shiftPerm ^ i) ω) = (T ^ i) (cod ω) := by
  induction i using Int.induction_on generalizing ω with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih,
      shiftPerm_apply, h.conj]
  | pred i ih =>
    rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
    congr 1
    rw [Equiv.Perm.eq_inv_iff_eq, ← h.conj]
    exact congrArg cod (shiftPerm.apply_symm_apply ω)

/-- The pullback bound `(12)`: `‖f ∘ cod‖_θ ≤ κ ‖f‖_Lip` with `θ = ϱ`. -/
lemma exists_holder (h : HorseshoeCoding T cod) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ (f : X → ℝ) (A : ℝ), LipBound f A → HolderBound θ (f ∘ cod) (κ * A) := by
  classical
  obtain ⟨C, ϱ, hϱ0, hϱ1, hC⟩ := h.holder
  set κ := max 2 (C / ϱ)
  have hκ2 : 2 ≤ κ := le_max_left _ _
  refine ⟨ϱ, hϱ0, hϱ1, κ, by linarith, fun f A hf => ?_⟩
  have hA : 0 ≤ A := (abs_nonneg _).trans (hf.1 (cod fun _ => true))
  refine ⟨fun ω => (hf.1 _).trans (by nlinarith), fun ω ω' => ?_⟩
  simp only [Function.comp]
  unfold dθ
  split_ifs with hex
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero, mul_one]
      calc |f (cod ω) - f (cod ω')| ≤ |f (cod ω)| + |f (cod ω')| := abs_sub _ _
        _ ≤ 2 * A := by linarith [hf.1 (cod ω), hf.1 (cod ω')]
        _ ≤ κ * A := mul_le_mul_of_nonneg_right hκ2 hA
    · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hagree : ∀ j : ℤ, j.natAbs ≤ k → ω j = ω' j := by
        intro j hj
        by_contra hne
        have := Nat.find_min' hex ⟨j, rfl, hne⟩
        omega
      rw [hk]
      calc |f (cod ω) - f (cod ω')| ≤ A * dist (cod ω) (cod ω') := hf.2 _ _
        _ ≤ A * (C * ϱ ^ k) := mul_le_mul_of_nonneg_left (hC k ω ω' hagree) hA
        _ = C / ϱ * A * ϱ ^ (k + 1) := by field_simp; ring
        _ ≤ κ * A * ϱ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hA)
            (pow_nonneg hϱ0.le _)
  · have : ω = ω' := funext fun j => by_contra fun hne => hex ⟨j.natAbs, j, rfl, hne⟩
    subst this
    simp

end HorseshoeCoding

/-! ## Transfer of the measure -/

section Transfer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma integral_map_cod {cod : Config → X} (hcod : Measurable cod) (ν : Measure Config)
    {F : X → ℝ} (hF : Measurable F) : ∫ x, F x ∂(ν.map cod) = ∫ ω, F (cod ω) ∂ν :=
  integral_map hcod.aemeasurable hF.aestronglyMeasurable

/-- Exponential mixing passes through a horseshoe coding (Lemma `lem:transfer`(i)). -/
theorem expMixing_map {ν : Measure Config} {T : X → X} (hT : Measurable T) {cod : Config → X}
    (hc : HorseshoeCoding T cod) {θ κ : ℝ}
    (hhold : ∀ (f : X → ℝ) (A : ℝ), LipBound f A → HolderBound θ (f ∘ cod) (κ * A)) {s : ℕ}
    (hmix : ExpMixingOrder ν shift (HolderBound θ) s) :
    ExpMixingOrder (ν.map cod) T LipBound s := by
  obtain ⟨C, c, hc0, hmix⟩ := hmix
  refine ⟨C * κ ^ s, c, hc0, fun f A hf n hn d hd => ?_⟩
  have hm := hc.continuous.measurable
  have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
  have h1 : ∫ x, ∏ i, f i (T^[n i] x) ∂(ν.map cod) =
      ∫ ω, ∏ i, (f i ∘ cod) (shift^[n i] ω) ∂ν := by
    rw [integral_map_cod hm ν (Finset.measurable_prod (f := fun i x => f i (T^[n i] x))
      Finset.univ fun i _ => (hfm i).comp (hT.iterate _))]
    congr 1; funext ω
    exact Finset.prod_congr rfl fun i _ => by simp [hc.iterate]
  have h2 : ∀ i, ∫ x, f i x ∂(ν.map cod) = ∫ ω, (f i ∘ cod) ω ∂ν := fun i =>
    integral_map_cod hm ν (hfm i)
  have := hmix (fun i => f i ∘ cod) (fun i => κ * A i) (fun i => hhold _ _ (hf i)) n hn d hd
  rw [h1]
  simp only [h2]
  calc _ ≤ C * Real.exp (-c * d) * ∏ i, (κ * A i) := this
    _ = C * κ ^ s * Real.exp (-c * d) * ∏ i, A i := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]; ring

lemma ExpMixingOrder.mono {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {T : Y → Y}
    {Bd Bd' : (Y → ℝ) → ℝ → Prop} (hBd : ∀ f A, Bd' f A → Bd f A) {s : ℕ}
    (h : ExpMixingOrder μ T Bd s) : ExpMixingOrder μ T Bd' s := by
  obtain ⟨C, c, hc, h⟩ := h
  exact ⟨C, c, hc, fun f A hf => h f A fun i => hBd _ _ (hf i)⟩

/-- `supp (cod_* ν) = cod(Σ)` for a full-support `ν`. -/
theorem support_map_cod {ν : Measure Config} [ν.IsOpenPosMeasure] {cod : Config → X}
    (hcod : Continuous cod) : (ν.map cod).support = Set.range cod := by
  ext x
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro hx
    by_contra hnot
    have hcl : IsClosed (Set.range cod) := (isCompact_range hcod).isClosed
    have := hx _ (hcl.isOpen_compl.mem_nhds hnot)
    rw [Measure.map_apply hcod.measurable hcl.isOpen_compl.measurableSet] at this
    simp at this
  · rintro ⟨ω, rfl⟩ U hU
    exact (Measure.measure_pos_of_mem_nhds ν (hcod.continuousAt.preimage_mem_nhds hU)).trans_le
      (Measure.le_map_apply hcod.measurable.aemeasurable U)

lemma measurePreserving_map {ν : Measure Config} (hν : MeasurePreserving shift ν ν) {T : X → X}
    (hT : Measurable T) {cod : Config → X} (hc : HorseshoeCoding T cod) :
    MeasurePreserving T (ν.map cod) (ν.map cod) := by
  have hm := hc.continuous.measurable
  refine ⟨hT, ?_⟩
  have hcomm : T ∘ cod = cod ∘ shift := funext fun ω => (hc.conj ω).symm
  rw [Measure.map_map hT hm, hcomm, ← Measure.map_map hm measurable_shift, hν.map_eq]

omit [MeasurableSpace X] [BorelSpace X] in
lemma orbitProcess_cod {T : Equiv.Perm X} {cod : Config → X} (hc : HorseshoeCoding T cod)
    {f₀ : X → ℝ} (hf₀ : ∀ ω, f₀ (cod ω) = Z 0 ω) (i : ℤ) (ω : Config) :
    orbitProcess T f₀ i (cod ω) = Z i ω := by
  rw [orbitProcess, ← hc.zpow, hf₀]
  simp [Z, shiftPerm_zpow_apply]

omit [MeasurableSpace X] [BorelSpace X] in
lemma birkhoffSum_cod {T : X → X} {cod : Config → X} (hc : HorseshoeCoding T cod)
    {f₀ : X → ℝ} (hf₀ : ∀ ω, f₀ (cod ω) = Z 0 ω) (n : ℕ) (ω : Config) :
    birkhoffSum T f₀ n (cod ω) = S n ω := by
  simp only [birkhoffSum, S]
  exact Finset.sum_congr rfl fun k _ => by rw [← hc.iterate, hf₀, Z_shift_iterate, zero_add]

omit [MetricSpace X] [BorelSpace X] in
lemma iIndepFun_map {ι : Type*} {ν : Measure Config} {cod : Config → X} (hcod : Measurable cod)
    {Y : ι → X → ℝ} (hY : ∀ i, Measurable (Y i)) {W : ι → Config → ℝ}
    (hYW : ∀ i ω, Y i (cod ω) = W i ω) (h : iIndepFun W ν) : iIndepFun Y (ν.map cod) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have hpre : ∀ i, cod ⁻¹' (Y i ⁻¹' sets i) = W i ⁻¹' sets i := fun i => by
    ext ω; simp [hYW]
  calc (ν.map cod) (⋂ i ∈ S, Y i ⁻¹' sets i) = ν (⋂ i ∈ S, W i ⁻¹' sets i) := by
        rw [Measure.map_apply hcod (Finset.measurableSet_biInter S fun i hi => hY i (hsets i hi))]
        simp only [Set.preimage_iInter, hpre]
    _ = ∏ i ∈ S, ν (W i ⁻¹' sets i) := h S hsets
    _ = ∏ i ∈ S, (ν.map cod) (Y i ⁻¹' sets i) := Finset.prod_congr rfl fun i hi => by
        rw [Measure.map_apply hcod (hY i (hsets i hi)), hpre]

omit [MetricSpace X] [BorelSpace X] in
lemma tuplewiseIndep_map {ν : Measure Config} {cod : Config → X} (hcod : Measurable cod)
    {Y : ℤ → X → ℝ} (hY : ∀ i, Measurable (Y i)) {W : ℤ → Config → ℝ}
    (hYW : ∀ i ω, Y i (cod ω) = W i ω) {p : ℕ} (h : TuplewiseIndep ν W p) :
    TuplewiseIndep (ν.map cod) Y p := fun J hJ =>
  iIndepFun_map hcod (fun j => hY j) (fun j ω => hYW j ω) (h J hJ)

omit [MetricSpace X] [BorelSpace X] in
lemma symmetricSigns_map {ν : Measure Config} {cod : Config → X} (hcod : Measurable cod)
    {Y : ℤ → X → ℝ} (hY : ∀ i, Measurable (Y i)) {W : ℤ → Config → ℝ}
    (hYW : ∀ i ω, Y i (cod ω) = W i ω) (h : SymmetricSigns ν W) :
    SymmetricSigns (ν.map cod) Y := fun j => by
  obtain ⟨h1, h2⟩ := h j
  have hm1 : MeasurableSet {x | Y j x = 1} := hY j (measurableSet_singleton 1)
  have hm2 : MeasurableSet {x | Y j x = -1} := hY j (measurableSet_singleton (-1))
  refine ⟨?_, ?_⟩
  · have hm : MeasurableSet {x | Y j x = 1 ∨ Y j x = -1} := hm1.union hm2
    rw [ae_map_iff hcod.aemeasurable hm]
    simpa [hYW] using h1
  · rw [Measure.map_apply hcod hm1]
    convert h2 using 2
    ext ω; simp [hYW]

omit [MetricSpace X] [BorelSpace X] in
lemma noGaussian_map {ν : Measure Config} {cod : Config → X} (hcod : Measurable cod)
    {Y : ℕ → X → ℝ} (hY : ∀ n, Measurable (Y n)) {W : ℕ → Config → ℝ}
    (hYW : ∀ n ω, Y n (cod ω) = W n ω) (h : NoGaussianSubseqLimit ν W) :
    NoGaussianSubseqLimit (ν.map cod) Y := by
  intro nk hnk v hconv
  refine h nk hnk v fun u => ?_
  have := hconv u
  rw [show (fun k => ∫ ω, u (W (nk k) ω / Real.sqrt (nk k)) ∂ν) =
      fun k => ∫ x, u (Y (nk k) x / Real.sqrt (nk k)) ∂(ν.map cod) from funext fun k => by
    rw [integral_map_cod (F := fun x => u (Y (nk k) x / Real.sqrt (nk k))) hcod ν
      (u.continuous.measurable.comp ((hY _).div_const _))]
    simp [hYW]]
  exact this

end Transfer

/-! ## Failure of exponential mixing from a lower bound -/

/-- If some observable `φ` with `∫ φ = 0` has order-`L` correlations `≥ c N^{-L/2}` at gaps
`≥ N/C`, the system is not exponentially mixing of order `L` (Corollary `cor:higher-order`). -/
theorem not_expMixing_of_lower {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {T : Y → Y}
    {Bd : (Y → ℝ) → ℝ → Prop} {φ : Y → ℝ} {A₀ : ℝ} (hφ : Bd φ A₀) (hφ0 : ∫ y, φ y ∂μ = 0)
    {L m : ℕ} (hm : L = 2 * m) (hL : 1 ≤ L)
    (hlow : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ n : Fin L → ℕ, StrictMono n ∧
      (∀ i, n i < N) ∧ Gapped n (N / C) ∧
        c * (N : ℝ) ^ (-(L : ℝ) / 2) ≤ |∫ y, ∏ i, φ (T^[n i] y) ∂μ|) :
    ¬ ExpMixingOrder μ T Bd L := by
  rintro ⟨C0, c0, hc0, hmix⟩
  obtain ⟨c, C, hc, hC, N₀, hN⟩ := hlow
  set a := c0 / C
  have ha : 0 < a := div_pos hc0 hC
  have hbound : ∀ N ≥ max N₀ 1, c ≤ C0 * A₀ ^ L * ((N : ℝ) ^ m * Real.exp (-(a * N))) := by
    intro N hN'
    obtain ⟨n, hn, -, hgap, hcorr⟩ := hN N (le_of_max_le_left hN')
    have hN0 : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by have := le_of_max_le_right hN'; omega)
    have h := hmix (fun _ => φ) (fun _ => A₀) (fun _ => hφ) n hn _ hgap
    beta_reduce at h
    rw [Finset.prod_eq_zero (i := ⟨0, by omega⟩) (Finset.mem_univ _) hφ0] at h
    simp only [sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    have hrpow : (N : ℝ) ^ (-(L : ℝ) / 2) = ((N : ℝ) ^ m)⁻¹ := by
      rw [show -(L : ℝ) / 2 = -(m : ℝ) by rw [hm]; push_cast; ring, Real.rpow_neg hN0.le,
        Real.rpow_natCast]
    rw [hrpow] at hcorr
    have h1 : c * ((N : ℝ) ^ m)⁻¹ ≤ C0 * Real.exp (-c0 * (N / C)) * A₀ ^ L := hcorr.trans h
    have hNm : (0 : ℝ) < (N : ℝ) ^ m := by positivity
    have e : -c0 * (N / C) = -(a * N) := by simp only [a]; ring
    rw [e] at h1
    have := mul_le_mul_of_nonneg_right h1 hNm.le
    rw [mul_assoc, inv_mul_cancel₀ hNm.ne', mul_one] at this
    linarith
  have htend : Tendsto (fun N : ℕ => C0 * A₀ ^ L * ((N : ℝ) ^ m * Real.exp (-(a * N)))) atTop
      (𝓝 0) := by
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop ha)
    have h3 := (h1.const_mul ((1 / a) ^ m)).const_mul (C0 * A₀ ^ L)
    simp only [mul_zero] at h3
    refine h3.congr fun N => ?_
    simp only [Function.comp]
    rw [← mul_assoc ((1 / a) ^ m), ← mul_pow, one_div, ← mul_assoc, inv_mul_cancel_left₀ ha.ne',
      mul_assoc]
  have := ge_of_tendsto htend (Filter.eventually_atTop.2 ⟨max N₀ 1, hbound⟩)
  linarith

/-! ## Low moments of the symbolic process -/

lemma integral_Z_eq_zero {ν : Measure Config} [IsProbabilityMeasure ν] (h : SymmetricSigns ν Z)
    (j : ℤ) : ∫ ω, Z j ω ∂ν = 0 := by
  have hset : {ω : Config | Z j ω = 1} = {ω | ω j = true} := by
    ext ω; cases hω : ω j <;> simp [Z, hω, spin]; norm_num
  have hZ : ∀ ω, Z j ω = 2 * Set.indicator {ω : Config | ω j = true} 1 ω - 1 := fun ω => by
    cases hω : ω j <;> simp [Z, spin, Set.indicator, hω]; norm_num
  have hmeas : MeasurableSet {ω : Config | ω j = true} :=
    measurableSet_eq_fun (measurable_pi_apply j) measurable_const
  have h2 := (h j).2
  rw [hset] at h2
  have h₁ : Integrable (fun ω => 2 * Set.indicator {ω : Config | ω j = true} (1 : Config → ℝ) ω)
      ν := ((integrable_const (1 : ℝ)).indicator hmeas).const_mul 2
  rw [integral_congr_ae (ae_of_all _ hZ), integral_sub h₁ (integrable_const _), integral_const_mul,
    integral_indicator_one hmeas, measureReal_def, h2]
  simp

lemma integral_S_sq_of_props {R : ℕ} (hR : 1 ≤ R) {ν : Measure Config}
    (hν : SymbolicProperties R ν) (n : ℕ) : ∫ ω, S n ω ^ 2 ∂ν = n := by
  classical
  have := hν.isProb
  have hZb : ∀ (i : ℤ), Integrable (Z i) ν := fun i =>
    Integrable.of_bound (measurable_Z i).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, Z, abs_spin])
  have hZZ : ∀ i j : ℤ, Integrable (fun ω => Z i ω * Z j ω) ν := fun i j =>
    Integrable.of_bound ((measurable_Z i).mul (measurable_Z j)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_mul, Z, Z, abs_spin, abs_spin,
        one_mul])
  have hpair : ∀ i j : ℕ, ∫ ω, Z i ω * Z j ω ∂ν = if i = j then 1 else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      simp [Z, ← sq, spin_sq]
    · have hne : (i : ℤ) ≠ j := by exact_mod_cast hij
      have hJ : ({(i : ℤ), (j : ℤ)} : Finset ℤ).card ≤ 2 * R + 1 := by
        rw [Finset.card_pair hne]; omega
      have hind := (hν.tuplewise _ hJ).indepFun
        (i := ⟨(i : ℤ), by simp⟩) (j := ⟨(j : ℤ), by simp⟩) (by simpa using hne)
      have := hind.integral_mul_eq_mul_integral (measurable_Z i).aestronglyMeasurable
        (measurable_Z j).aestronglyMeasurable
      simp only [Pi.mul_apply] at this
      rw [this, integral_Z_eq_zero hν.signs, zero_mul]
  have hsq : ∀ ω, S n ω ^ 2 = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      Z i ω * Z j ω := fun ω => by
    rw [S, sq, Finset.sum_mul_sum]
  simp_rw [hsq]
  have hin : ∀ i : ℕ, ∫ ω, ∑ j ∈ Finset.range n, Z i ω * Z j ω ∂ν =
      ∑ j ∈ Finset.range n, ∫ ω, Z i ω * Z j ω ∂ν := fun i =>
    integral_finsetSum _ fun (j : ℕ) _ => hZZ (i : ℤ) (j : ℤ)
  rw [integral_finsetSum _ fun (i : ℕ) _ => integrable_finsetSum _ fun (j : ℕ) _ =>
    hZZ (i : ℤ) (j : ℤ)]
  simp_rw [hin, hpair]
  simp [Finset.filter_true_of_mem fun x hx => Finset.mem_range.1 hx]

/-! ## Items (i)–(iv), (vi) through a coding -/

section Realisation

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma measurable_zpow_of_continuous {T : Equiv.Perm X} (hT : Continuous T)
    (hTi : Continuous ⇑T⁻¹) (i : ℤ) : Continuous ⇑(T ^ i) := by
  induction i using Int.induction_on with
  | zero => simpa using continuous_id
  | succ i ih => rw [zpow_add_one, Equiv.Perm.coe_mul]; exact ih.comp hT
  | pred i ih => rw [zpow_sub_one, Equiv.Perm.coe_mul]; exact ih.comp hTi

/-- **Lemma `lem:transfer`** and items (i)–(iv), (vi) of Theorems A and B: all the properties of
Theorem C pass to `μ = cod_* ν` and the observable `f₀` with `f₀ ∘ cod = Z₀`. -/
theorem realisationProperties_of_coding {R : ℕ} (hR : 2 ≤ R) {ν : Measure Config}
    (hν : SymbolicProperties R ν) {T : Equiv.Perm X} (hT : Continuous T)
    (hTi : Continuous ⇑T⁻¹) {cod : Config → X} (hc : HorseshoeCoding T cod) {f₀ : X → ℝ}
    (hf₀c : Continuous f₀) (hf₀ : ∀ ω, f₀ (cod ω) = Z 0 ω)
    {Bd : (X → ℝ) → ℝ → Prop} (hBd : ∀ f A, Bd f A → LipBound f A) {A₀ : ℝ} (hA₀ : Bd f₀ A₀) :
    RealisationProperties T (Set.range cod) (ν.map cod) f₀ Bd R := by
  have := hν.isProb
  have := hν.fullSupport
  have hm := hc.continuous.measurable
  have hTm : Measurable T := hT.measurable
  have : IsProbabilityMeasure (ν.map cod) := inferInstance
  have hf₀m := hf₀c.measurable
  have hcentred : ∫ x, f₀ x ∂(ν.map cod) = 0 := by
    rw [integral_map_cod hm ν hf₀m]; simp_rw [hf₀]; exact integral_Z_eq_zero hν.signs 0
  have hproc : ∀ i, Measurable (orbitProcess T f₀ i) := fun i =>
    hf₀m.comp (measurable_zpow_of_continuous hT hTi i).measurable
  have hcorr : ∀ {L : ℕ} (n : Fin L → ℕ),
      ∫ x, ∏ i, f₀ (T^[n i] x) ∂(ν.map cod) = ∫ ω, ∏ i, Z (n i) ω ∂ν := fun n => by
    rw [integral_map_cod hm ν (Finset.measurable_prod (f := fun i x => f₀ (T^[n i] x))
      Finset.univ fun i _ => hf₀m.comp (hTm.iterate _))]
    congr 1; funext ω
    exact Finset.prod_congr rfl fun i _ => by
      rw [← hc.iterate, hf₀, Z_shift_iterate, zero_add]
  have hhigher : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ n : Fin (2 * R + 2) → ℕ, StrictMono n ∧ (∀ i, n i < N) ∧ Gapped n (N / C) ∧
        c * (N : ℝ) ^ (-((2 * R + 2 : ℕ) : ℝ) / 2) ≤
          |∫ x, ∏ i, f₀ (T^[n i] x) ∂(ν.map cod)| := by
    obtain ⟨c, C, hc, hC, N₀, hN⟩ := hν.higherOrder
    refine ⟨c, C, hc, hC, N₀, fun N hN' => ?_⟩
    obtain ⟨n, hn, hlt, hgap, hlow⟩ := hN N hN'
    exact ⟨n, hn, hlt, hgap, by rw [hcorr]; exact hlow.trans (neg_le_abs _)⟩
  obtain ⟨θ, hθ0, hθ1, κ, -, hhold⟩ := hc.exists_holder
  refine
    { isProb := inferInstance
      invariant := measurePreserving_map hν.invariant hTm hc
      support := support_map_cod hc.continuous
      mixing := fun s hs hsR => (expMixing_map hTm hc hhold
        (hν.mixing θ hθ0 hθ1 s hs hsR)).mono hBd
      signs := symmetricSigns_map hm hproc (orbitProcess_cod hc hf₀) hν.signs
      tuplewise := tuplewiseIndep_map hm hproc (orbitProcess_cod hc hf₀) hν.tuplewise
      centred := hcentred
      noGaussian := noGaussian_map hm (measurable_birkhoffSum hTm hf₀m)
        (birkhoffSum_cod hc hf₀) hν.noGaussian
      higherOrder := hhigher
      notMixing := not_expMixing_of_lower hA₀ hcentred (m := R + 1) (by ring) (by omega)
        (by simpa using hhigher) }

end Realisation

end FiniteOrderMixing
