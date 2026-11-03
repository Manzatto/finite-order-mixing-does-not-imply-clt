module
public import FiniteOrderMixing.Realisation.Physical

/-!
# Theorem B statement

The smooth physical realization on compact smooth surfaces from Theorem B of the paper.
-/

open MeasureTheory ProbabilityTheory Filter Topology Manifold Bundle
open scoped ContDiff

@[expose] public section

namespace FiniteOrderMixing

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N]
  [RiemannianBundle (fun (x : N) ↦ TangentSpace J x)]

/-- **Theorem `thm:physical`** (physical realisation). For every `R ≥ 2`,
a nonempty compact smooth surface without boundary, possibly disconnected, carries a `C^∞`
diffeomorphism and an invariant physical measure with all the stated statistical properties.
The auxiliary bounded distance preserves the topology and the Riemannian `C¹` norm. -/
def TheoremB [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace N] [Nonempty N]
    [MeasurableSpace N] [BorelSpace N]
    [IsContinuousRiemannianBundle E' (fun (x : N) ↦ TangentSpace J x)] : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    letI := boundedRiemannianMetric J N
    ∃ (T : N ≃ₘ^∞⟮J, J⟯ N) (Λ : Set N) (μ : Measure N) (f₀ : N → ℝ),
      IsHyperbolicHorseshoe J T Λ ∧ PhysicalRealisation J T Λ μ f₀ R

end FiniteOrderMixing
