module

public import Mathlib

/-!
# Kolmogorov extension on `α^ℤ` for a finite alphabet `α`

For the compact product `ℤ → α` of a finite discrete space, every measurable cylinder is clopen,
hence compact and open.  A countable cover of a cylinder by cylinders therefore has a finite
subcover, so the finitely additive content `projectiveFamilyContent` of a projective family is
σ-subadditive, and the Carathéodory extension `AddContent.measure` gives the projective limit.
-/

@[expose] public section

open MeasureTheory Set

namespace FiniteOrderMixing

section General

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [DiscreteTopology α] [Finite α]

omit [Finite α] in
/-- A measurable cylinder of `ℤ → α` is clopen. -/
lemma isClopen_of_mem_measurableCylinders' {s : Set (ℤ → α)}
    (hs : s ∈ measurableCylinders fun _ : ℤ => α) : IsClopen s := by
  obtain ⟨I, S, -, rfl⟩ := (mem_measurableCylinders s).1 hs
  exact (isClopen_discrete S).preimage (continuous_pi fun i => continuous_apply (i : ℤ))

/-- **Kolmogorov extension** for a finite alphabet: a projective family of probability measures
on the finite coordinate sets has a projective limit, which is a probability measure. -/
theorem kolmogorov_extension_finite (P : ∀ E : Finset ℤ, Measure (E → α))
    [∀ E, IsProbabilityMeasure (P E)] (hP : IsProjectiveMeasureFamily (α := fun _ : ℤ => α) P) :
    ∃ ν : Measure (ℤ → α), IsProbabilityMeasure ν ∧ IsProjectiveLimit ν P := by
  set m := projectiveFamilyContent hP
  have hsub : m.IsSigmaSubadditive := by
    intro f hf hU
    obtain ⟨t, ht⟩ :=
      (isClopen_of_mem_measurableCylinders' hU).isClosed.isCompact.elim_finite_subcover
        f (fun i => (isClopen_of_mem_measurableCylinders' (hf i)).isOpen) subset_rfl
    calc m (⋃ i, f i) ≤ m (⋃ i ∈ t, f i) :=
          addContent_mono isSetSemiring_measurableCylinders hU
            (isSetRing_measurableCylinders.biUnion_mem t fun i _ => hf i) ht
      _ ≤ ∑ i ∈ t, m (f i) := addContent_biUnion_le isSetRing_measurableCylinders fun i _ => hf i
      _ ≤ ∑' i, m (f i) := ENNReal.sum_le_tsum t
  set ν := m.measure isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge hsub
  have hlim : IsProjectiveLimit ν P := by
    intro E
    ext S hS
    rw [Measure.map_apply (Finset.measurable_restrict E) hS]
    change ν (cylinder E S) = P E S
    rw [AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm hsub
      (cylinder_mem_measurableCylinders E S hS), projectiveFamilyContent_cylinder hP hS]
  exact ⟨ν, hlim.isProbabilityMeasure, hlim⟩

end General

/-- **Kolmogorov extension** for `{-1,1}^ℤ`: a projective family of probability measures on the
finite coordinate sets extends to a probability measure. -/
theorem kolmogorov_extension
    (P : ∀ E : Finset ℤ, Measure (E → Bool)) [∀ E, IsProbabilityMeasure (P E)]
    (hproj : ∀ (E F : Finset ℤ) (hEF : E ⊆ F),
      (P F).map (fun x : F → Bool => fun j : E => x ⟨j, hEF j.2⟩) = P E) :
    ∃ ν : Measure (ℤ → Bool), IsProbabilityMeasure ν ∧
      ∀ E : Finset ℤ, ν.map (fun ω : ℤ → Bool => fun j : E => ω j) = P E := by
  have hP : IsProjectiveMeasureFamily (α := fun _ : ℤ => Bool) P :=
    fun I J hJI => (hproj J I hJI).symm
  obtain ⟨ν, hν, hlim⟩ := kolmogorov_extension_finite P hP
  exact ⟨ν, hν, hlim⟩

end FiniteOrderMixing
