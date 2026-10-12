import FiniteOrderMixing.Limit

/-!
# Properties of `ν` (Proposition `prop:limit` (ii)–(iii))

* `nu_measurePreserving` — `ν` is shift invariant;
* `nu_isOpenPosMeasure` — `ν` has full support;
* `integral_chi_small`, `nu_cyl_half` — characters of `1 ≤ |K| ≤ L-1` coordinates have mean zero,
  and every pattern on at most `L-1` coordinates has probability `2^{-|E|}`;
* `nu_tuplewise`, `nu_signs` — `(L-1)`-tuplewise independence with symmetric marginals, in the
  sense of `iIndepFun`.
-/

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

namespace FiniteOrderMixing

/-- Probability measures on `Σ` with the same integrals of cylinder functions coincide. -/
lemma measure_eq_of_integral_dep {μ₁ μ₂ : Measure Config} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂]
    (h : ∀ (E : Finset ℤ) (G : Config → ℝ), Dep G E → ∫ ω, G ω ∂μ₁ = ∫ ω, G ω ∂μ₂) :
    μ₁ = μ₂ := by
  refine ext_of_generate_finite (measurableCylinders fun _ : ℤ => Bool)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs => ?_)
    (by simp)
  obtain ⟨t, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hs
  have hr : Measurable (fun f : Config => fun i : t => f i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hmeas : MeasurableSet (cylinder t S) := hr hS
  have hdep : Dep (Set.indicator (cylinder t S) 1) t := by
    intro ω ω' hω
    have : t.restrict ω = t.restrict ω' := funext fun i => hω i i.2
    have hmem : ω ∈ cylinder t S ↔ ω' ∈ cylinder t S := by
      simp only [cylinder, Set.mem_preimage, this]
    by_cases hω1 : ω ∈ cylinder t S
    · rw [Set.indicator_of_mem hω1, Set.indicator_of_mem (hmem.1 hω1)]; rfl
    · rw [Set.indicator_of_notMem hω1, Set.indicator_of_notMem (fun h => hω1 (hmem.2 h))]
  have := h t _ hdep
  rw [integral_indicator_one hmeas, integral_indicator_one hmeas, measureReal_def,
    measureReal_def] at this
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

/-- A criterion for the independence of finitely-valued random variables. -/
lemma iIndepFun_of_singleton {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]
    [∀ i, DecidableEq (β i)] [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableSingletonClass (β i)]
    {f : ∀ i, Ω → β i} (hf : ∀ i, Measurable (f i))
    (h : ∀ y : ∀ i, β i, μ {ω | ∀ i, f i ω = y i} = ∏ i, μ {ω | f i ω = y i}) :
    iIndepFun f μ := by
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (hf i).aemeasurable]
  refine Measure.ext_of_singleton fun y => ?_
  have e1 : (fun ω i => f i ω) ⁻¹' {y} = {ω | ∀ i, f i ω = y i} := by
    ext ω; simp [funext_iff]
  rw [Measure.map_apply (measurable_pi_iff.mpr hf) (measurableSet_singleton y), e1, h y,
    ← Set.univ_pi_singleton y, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.map_apply (hf i) (measurableSet_singleton _)]
  rfl

lemma ofReal_half_pow (n : ℕ) : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (2⁻¹ : ℝ≥0∞) ^ n := by
  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat]

/-- Fourier expansion of the indicator of a pattern. -/
lemma indPat_eq_sum (E : Finset ℤ) (x : E → Bool) (ω : Config) :
    indPat E x ω = (1 / 2) ^ E.card * ∑ T ∈ E.powerset, chi T (extE E x) * chi T ω := by
  have h1 : ∀ j, (1 + Z j (extE E x) * Z j ω) / 2 =
      if ω j = extE E x j then 1 else 0 := fun j => by
    cases h1 : ω j <;> cases h2 : extE E x j <;> simp [Z, h1, h2, spin]
  have h2 : indPat E x ω = ∏ j ∈ E, (if ω j = extE E x j then (1 : ℝ) else 0) := by
    rw [Finset.prod_boole]
    simp only [indPat]
    congr 1
    apply propext
    constructor
    · intro hx j hj; rw [← hx]; simp [restr, extE, hj]
    · intro hx; funext j; have := hx j j.2; simp only [extE, j.2, dite_eq_left] at this; exact this
  rw [h2, ← Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_div_distrib, Finset.prod_one_add]
  simp only [Finset.prod_const, div_eq_inv_mul, chi, ← Finset.prod_mul_distrib]
  rw [mul_one, inv_pow]

variable {L : ℕ}

section Props

variable {P : Measure Hspace} (hP : HierarchyLaw L P) (hL : 6 ≤ L) (hLe : Even L)
include hP hL hLe

/-- `ν` is shift invariant (Proposition `prop:limit` (ii)). -/
theorem nu_measurePreserving : MeasurePreserving shift (nu hP hL hLe) (nu hP hL hLe) := by
  refine ⟨measurable_shift, ?_⟩
  refine measure_eq_of_integral_dep fun E G hG => ?_
  rw [integral_map measurable_shift.aemeasurable hG.measurable.aestronglyMeasurable]
  have hG' : Dep (fun ω => G (transl 1 ω)) (tr 1 E) := hG.transl 1
  set ℓ := kE (tr 1 E) + kE E
  change ∫ ω, G (transl 1 ω) ∂(nu hP hL hLe) = _
  rw [integral_nu' hP hL hLe (subset_refl _) (Nat.le_add_right _ _) hG',
    integral_nu' hP hL hLe (subset_refl _) (Nat.le_add_left _ _) hG]
  simp_rw [← Eh_shiftH]
  conv_rhs => rw [← (hP.stationary 1).map_eq]
  rw [integral_map (measurable_shiftH 1).aemeasurable
    (measurable_Eh hL ℓ E G).aestronglyMeasurable]

/-- Every cylinder set has positive `ν`-measure. -/
theorem nu_cyl_pos (E : Finset ℤ) (x : E → Bool) : 0 < nu hP hL hLe {ω | restr E ω = x} := by
  rw [nu_cyl]
  apply ENNReal.ofReal_pos.2
  simp only [qP]
  have hint := integrable_Eh hP hL hLe (dep_indPat E x) (kE E)
  have hpos : ∀ᵐ h ∂P, 0 < Eh L h (kE E) E (indPat E x) := by
    filter_upwards [hP.good] with h hg
    exact Eh_pos hg hL hLe (indPat_nonneg E x) (dep_indPat E x)
      ⟨extE E x, by simp [indPat, restr_extE]⟩
  have := hP.isProb
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun h hh => hh.le) hint]
  by_contra hcon
  push Not at hcon
  have h0 : P (Function.support fun h => Eh L h (kE E) E (indPat E x)) = 0 :=
    le_antisymm hcon bot_le
  have hz : ∀ᵐ h ∂P, Eh L h (kE E) E (indPat E x) = 0 := by
    rw [ae_iff]; simpa [Function.support] using h0
  have hfalse : ∀ᵐ _h ∂P, False := by
    filter_upwards [hpos, hz] with h h1 h2; linarith
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
  have := measure_univ (μ := P)
  rw [hfalse] at this
  simp at this

/-- `ν` has full support (Proposition `prop:limit` (ii)). -/
theorem nu_isOpenPosMeasure : (nu hP hL hLe).IsOpenPosMeasure := by
  constructor
  rintro U hU ⟨ω0, hω0⟩
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU ω0 hω0
  have hsub : {ω | restr I ω = restr I ω0} ⊆ U := fun ω hω => hIU fun i hi => by
    have : ω i = ω0 i := congrFun hω ⟨i, hi⟩
    rw [this]; exact (hu i hi).2
  exact (lt_of_lt_of_le (nu_cyl_pos hP hL hLe I _) (measure_mono hsub)).ne'

/-- Characters of `1 ≤ |K| ≤ L - 1` coordinates have mean zero. -/
theorem integral_chi_small {K : Finset ℤ} (hne : K.Nonempty) (hcard : K.card ≤ L - 1) :
    ∫ ω, chi K ω ∂(nu hP hL hLe) = 0 := by
  rw [integral_nu hP hL hLe (dep_chi K)]
  rw [integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
  · simp
  filter_upwards [hP.good] with h hg
  exact Eh_chi_small hg hL hLe _ hne hcard

/-- Characters of at most `L - 1` coordinates have the same mean as under the uniform law. -/
theorem integral_chi_eq_avg {K B : Finset ℤ} (hKB : K ⊆ B) (hcard : K.card ≤ L - 1) :
    ∫ ω, chi K ω ∂(nu hP hL hLe) = avg B (chi K) := by
  rcases K.eq_empty_or_nonempty with hK | hK
  · subst hK
    have : chi ∅ = fun _ => (1 : ℝ) := funext chi_empty
    rw [this, avg_const]; simp
  · rw [integral_chi_small hP hL hLe hK hcard, avg_chi hKB hK]

/-- Patterns on at most `L - 1` coordinates have probability `2^{-|E|}`. -/
theorem integral_indPat_small {E : Finset ℤ} (hcard : E.card ≤ L - 1) (x : E → Bool) :
    ∫ ω, indPat E x ω ∂(nu hP hL hLe) = (1 / 2) ^ E.card := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (indPat_eq_sum E x)), integral_const_mul,
    integral_finsetSum _ fun T _ => ((dep_chi T).integrable _).const_mul _]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro T hT hne
    rw [integral_const_mul, integral_chi_small hP hL hLe (Finset.nonempty_iff_ne_empty.2 hne)
      ((Finset.card_le_card (Finset.mem_powerset.1 hT)).trans hcard), mul_zero]
  · simp

theorem nu_cyl_half {E : Finset ℤ} (hcard : E.card ≤ L - 1) (x : E → Bool) :
    nu hP hL hLe {ω | restr E ω = x} = (2⁻¹ : ℝ≥0∞) ^ E.card := by
  rw [nu_cyl, ← integral_indPat hP hL hLe, integral_indPat_small hP hL hLe hcard,
    ofReal_half_pow]

lemma nu_coord (j : ℤ) (b : Bool) : nu hP hL hLe {ω | ω j = b} = 2⁻¹ := by
  have := nu_cyl_half hP hL hLe (E := {j}) (by simp; omega) (fun _ => b)
  rw [Finset.card_singleton, pow_one] at this
  rw [← this]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, restr, funext_iff, Subtype.forall, Finset.mem_singleton,
    forall_eq]

/-- `(L-1)`-tuplewise independence (Proposition `prop:limit` (iii)). -/
theorem nu_tuplewise : TuplewiseIndep (nu hP hL hLe) Z (L - 1) := by
  classical
  intro J hJ
  have hbool : iIndepFun (fun j : J => fun ω : Config => ω j) (nu hP hL hLe) := by
    refine iIndepFun_of_singleton (fun j => measurable_pi_apply _) fun y => ?_
    have e1 : {ω : Config | ∀ j : J, ω j = y j} = {ω | restr J ω = y} := by
      ext ω; simp [restr, funext_iff]
    rw [e1, nu_cyl_half hP hL hLe hJ,
      Finset.prod_congr rfl fun j _ => nu_coord hP hL hLe j.1 (y j)]
    simp
  exact hbool.comp (fun _ => spin) (fun _ => measurable_of_countable _)

/-- Symmetric signs (Proposition `prop:limit` (iii)). -/
theorem nu_signs : SymmetricSigns (nu hP hL hLe) Z := by
  intro j
  refine ⟨Filter.Eventually.of_forall fun ω => ?_, ?_⟩
  · cases h : ω j <;> simp [Z, h, spin]
  · have : {ω : Config | Z j ω = 1} = {ω | ω j = true} := by
      ext ω; cases h : ω j <;> simp [Z, h, spin]; norm_num
    rw [this, nu_coord, one_div]

end Props

end FiniteOrderMixing
