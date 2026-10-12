import FiniteOrderMixing.Realisation.Defs

/-!
# Smooth volumes

A measure `m` on a manifold is a **smooth volume** if, in every chart, it has a smooth positive
density with respect to a Haar measure of the model space.  Smooth volumes charge nonempty open
sets (`IsSmoothVolume.isOpenPosMeasure`), which is the only property of `m` used for physicality.
-/

open Set Filter Topology Manifold MeasureTheory
open scoped ContDiff

namespace FiniteOrderMixing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]

/-- `m` is a **smooth volume**: in the chart at every point `x`, `m` has a smooth positive density
`ρ` with respect to an additive Haar measure `λ` of the model space. -/
def IsSmoothVolume (m : Measure M) : Prop :=
  ∀ x : M, ∃ (lam : Measure E) (ρ : E → ℝ), lam.IsAddHaarMeasure ∧
    ContDiffOn ℝ ∞ ρ (extChartAt I x).target ∧ (∀ e ∈ (extChartAt I x).target, 0 < ρ e) ∧
    (m.restrict (extChartAt I x).source).map (extChartAt I x) =
      (lam.restrict (extChartAt I x).target).withDensity fun e => ENNReal.ofReal (ρ e)

variable {I}

/-- **Smooth volumes charge nonempty open sets.** -/
theorem IsSmoothVolume.isOpenPosMeasure [BorelSpace E] [BorelSpace M] [I.Boundaryless]
    {m : Measure M} (hm : IsSmoothVolume I m) : m.IsOpenPosMeasure := by
  refine ⟨fun W hW hWne => ?_⟩
  obtain ⟨x, hx⟩ := hWne
  obtain ⟨lam, ρ, hlam, hρs, hρp, hmap⟩ := hm x
  set φ := extChartAt I x
  have hsrc : IsOpen φ.source := isOpen_extChartAt_source x
  have htgt : IsOpen φ.target := isOpen_extChartAt_target x
  -- the image of `W ∩ source` in the chart
  set V := φ.target ∩ φ.symm ⁻¹' W
  have hV : IsOpen V := (continuousOn_extChartAt_symm x).isOpen_inter_preimage htgt hW
  have hxV : φ x ∈ V := ⟨mem_extChartAt_target x, by simpa [φ, extChartAt_to_inv] using hx⟩
  -- `m W ≥ (map φ (m|source)) V`
  have h1 : (m.restrict φ.source).map φ V ≤ m W := by
    rw [Measure.map_apply_of_aemeasurable
      ((continuousOn_extChartAt x).aemeasurable hsrc.measurableSet) hV.measurableSet,
      Measure.restrict_apply' hsrc.measurableSet]
    apply measure_mono
    rintro q ⟨⟨-, hq⟩, hqs⟩
    have : φ.symm (φ q) = q := φ.left_inv hqs
    rw [mem_preimage, this] at hq
    exact hq
  -- the density is bounded below near `φ x`
  have hρc : ContinuousAt ρ (φ x) :=
    (hρs.continuousOn.continuousAt (htgt.mem_nhds (mem_extChartAt_target x)))
  set c := ρ (φ x) / 2
  have hc : 0 < c := by have := hρp _ (mem_extChartAt_target x); positivity
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball (φ x) ε ⊆ V ∩ {e | c < ρ e} := by
    have : V ∩ {e | c < ρ e} ∈ 𝓝 (φ x) :=
      inter_mem (hV.mem_nhds hxV) (hρc.eventually (lt_mem_nhds (by
        have := hρp _ (mem_extChartAt_target x); simp only [c]; linarith)))
    exact Metric.mem_nhds_iff.1 this
  have h2 : 0 < (lam.restrict φ.target).withDensity (fun e => ENNReal.ofReal (ρ e)) V := by
    rw [withDensity_apply _ hV.measurableSet]
    have hB : Metric.ball (φ x) ε ⊆ V := fun e he => (hball he).1
    calc (0 : ENNReal) < ENNReal.ofReal c * lam (Metric.ball (φ x) ε) :=
          ENNReal.mul_pos (by simpa using hc) (Metric.measure_ball_pos lam _ hε).ne'
      _ = ∫⁻ _ in Metric.ball (φ x) ε, ENNReal.ofReal c ∂lam := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ e in Metric.ball (φ x) ε, ENNReal.ofReal (ρ e) ∂lam :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet fun e he =>
            ENNReal.ofReal_le_ofReal (hball he).2.le
      _ = ∫⁻ e in Metric.ball (φ x) ε, ENNReal.ofReal (ρ e) ∂(lam.restrict φ.target) := by
          rw [Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
            inter_eq_left.2 (hB.trans inter_subset_left)]
      _ ≤ ∫⁻ e in V, ENNReal.ofReal (ρ e) ∂(lam.restrict φ.target) := lintegral_mono_set hB
  rw [← hmap] at h2
  exact (h2.trans_le h1).ne'

end FiniteOrderMixing
