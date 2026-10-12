import FiniteOrderMixing.Dependence
import FiniteOrderMixing.Symbolic

/-!
# Construction of the stationary hierarchy law

`exists_hierarchyLaw` proves Proposition `prop:hierarchy`, constructing the nested marker law
from the finitely dependent colouring. The main symbolic theorem is in `TheoremC.lean`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace FiniteOrderMixing

variable {L : ℕ}

lemma measure_eq_ofReal_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {S : Set α} (hS : MeasurableSet S) :
    μ S = ENNReal.ofReal (∫ x, S.indicator 1 x ∂μ) := by
  rw [integral_indicator_one hS, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma measurable_prop_mem (k : ℕ) (j : ℤ) : Measurable fun h : Hspace => h k j = true := by
  exact (measurable_of_countable (fun b : Bool => b = true)).comp
    ((measurable_pi_apply j).comp (measurable_pi_apply k))

lemma measurableSet_good (L : ℕ) : MeasurableSet {h : Hspace | Good L h} := by
  have e : {h : Hspace | Good L h} = {h | (∀ j, h 0 j = true) ∧
      (∀ k j, h (k + 1) j = true → h k j = true) ∧
      (∀ k, 1 ≤ k → ∀ u v : ℤ, h k u = true → h k v = true → u < v → u + sc L k < v) ∧
      (∀ (k : ℕ) (i : ℤ), ∃ j, i ≤ j ∧ j < i + 3 * sc L k ∧ h k j = true)} := by
    ext h
    exact ⟨fun hg => ⟨hg.1, hg.2, hg.3, hg.4⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩
  rw [e, measurableSet_setOfPred]
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_))
  · exact Measurable.forall fun j => measurable_prop_mem 0 j
  · exact Measurable.forall fun k => Measurable.forall fun j =>
      (measurable_prop_mem (k + 1) j).imp (measurable_prop_mem k j)
  · exact Measurable.forall fun k => measurable_const.imp (Measurable.forall fun u =>
      Measurable.forall fun v => (measurable_prop_mem k u).imp ((measurable_prop_mem k v).imp
        (measurable_const.imp measurable_const)))
  · exact Measurable.forall fun k => Measurable.forall fun i => Measurable.exists fun j =>
      measurable_const.and (measurable_const.and (measurable_prop_mem k j))

/-- **Proposition `prop:hierarchy`.** -/
theorem exists_hierarchyLaw (hL : 1 ≤ L) : ∃ P : Measure Hspace, HierarchyLaw L P := by
  classical
  obtain ⟨q, hq2, PV, hC⟩ := exists_colouringLaw L hL
  have := hC.prob
  have hq : 1 ≤ q := by omega
  have hMh := measurable_Mh L hq (q := q)
  refine ⟨(POmega PV).map (Mh L), ⟨inferInstance, ?_, fun m => ?_, 4 * q, fun k I J hIJ => ?_⟩⟩
  · exact (ae_map_iff hMh.aemeasurable (measurableSet_good L)).2 (ae_good hC hL)
  · refine ⟨measurable_shiftH m, ?_⟩
    have hcomm : shiftH m ∘ Mh L = Mh L ∘ tau (q := q) L m := funext fun ω => (Mh_tau m ω).symm
    rw [Measure.map_map (measurable_shiftH m) hMh, hcomm,
      ← Measure.map_map hMh (measurable_tau hq m), (tau_mp hC hq m).map_eq]
  · -- independence of the marker configurations on separated windows
    have hX : ∀ K : Finset ℤ, Measurable (rI k K) := fun K => measurable_rI k K
    change IndepFun (rI k I) (rI k J) ((POmega PV).map (Mh L))
    rw [indepFun_iff_map_prod_eq_prod_map_map (hX I).aemeasurable (hX J).aemeasurable]
    refine Measure.ext_of_singleton fun ⟨x, y⟩ => ?_
    have hpair : Measurable fun h : Hspace => (rI k I h, rI k J h) := (hX I).prodMk (hX J)
    rw [← Set.singleton_prod_singleton, Measure.prod_prod,
      Measure.map_apply hpair ((measurableSet_singleton x).prod (measurableSet_singleton y)),
      Measure.map_apply (hX I) (measurableSet_singleton x),
      Measure.map_apply (hX J) (measurableSet_singleton y),
      Measure.map_apply hMh (hpair ((measurableSet_singleton x).prod (measurableSet_singleton y))),
      Measure.map_apply hMh ((hX I) (measurableSet_singleton x)),
      Measure.map_apply hMh ((hX J) (measurableSet_singleton y))]
    set f : (Finset.range (k + 1) ×ˢ I → Bool) → ℝ := fun z => if z = x then 1 else 0
    set g : (Finset.range (k + 1) ×ˢ J → Bool) → ℝ := fun z => if z = y then 1 else 0
    have hS1 : MeasurableSet (Mh L ⁻¹' (rI k I ⁻¹' {x})) := hMh ((hX I) (measurableSet_singleton x))
    have hS2 : MeasurableSet (Mh L ⁻¹' (rI k J ⁻¹' {y})) := hMh ((hX J) (measurableSet_singleton y))
    have hS12 : MeasurableSet (Mh L ⁻¹' ((fun h => (rI k I h, rI k J h)) ⁻¹' ({x} ×ˢ {y}))) :=
      hMh (hpair ((measurableSet_singleton x).prod (measurableSet_singleton y)))
    have i1 : (Mh L ⁻¹' (rI k I ⁻¹' {x})).indicator (1 : (ℕ → ℤ → Fin q) → ℝ) =
        fun ω => f (rI k I (Mh L ω)) := by
      funext ω; simp [Set.indicator, f]
    have i2 : (Mh L ⁻¹' (rI k J ⁻¹' {y})).indicator (1 : (ℕ → ℤ → Fin q) → ℝ) =
        fun ω => g (rI k J (Mh L ω)) := by
      funext ω; simp [Set.indicator, g]
    have i12 : (Mh L ⁻¹' ((fun h => (rI k I h, rI k J h)) ⁻¹' ({x} ×ˢ {y}))).indicator
        (1 : (ℕ → ℤ → Fin q) → ℝ) = fun ω => f (rI k I (Mh L ω)) * g (rI k J (Mh L ω)) := by
      funext ω; simp only [Set.indicator, f, g]; split_ifs <;> simp_all
    rw [measure_eq_ofReal_integral _ hS12, measure_eq_ofReal_integral _ hS1,
      measure_eq_ofReal_integral _ hS2, i1, i2, i12,
      indep_core hC hq hq2 hL k I J (fun i hi j hj => by
        have := hIJ i hi j hj; push_cast at this ⊢; linarith) f g,
      ENNReal.ofReal_mul (integral_nonneg fun ω => by simp only [f]; split_ifs <;> norm_num)]

end FiniteOrderMixing
