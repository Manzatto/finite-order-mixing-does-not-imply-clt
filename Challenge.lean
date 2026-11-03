module
public import FiniteOrderMixing.StatementA
public import FiniteOrderMixing.StatementB
public import FiniteOrderMixing.StatementC

/-!
# Challenge statements

These are the three main results from the cited paper. Their formal statements are shared with
the proof development; the corresponding proofs are supplied by `Solution.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Manifold Bundle
open scoped ContDiff

@[expose] public section

namespace PalomarEntry

/-- The analytic Anosov torus realization (Theorem A). -/
theorem theoremA : FiniteOrderMixing.TheoremA := by
  sorry

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N]
  [RiemannianBundle (fun (x : N) ↦ TangentSpace J x)]

/-- The smooth physical realization on compact smooth surfaces (Theorem B). -/
theorem theoremB [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    (hE : Module.finrank ℝ E' = 2) [J.Boundaryless]
    [IsManifold J ∞ N] [CompactSpace N] [Nonempty N] [MeasurableSpace N] [BorelSpace N]
    [IsContinuousRiemannianBundle E' (fun (x : N) ↦ TangentSpace J x)] :
    FiniteOrderMixing.TheoremB J (N := N) := by
  sorry

/-- The stationary symbolic construction (Theorem C). -/
theorem theoremC : FiniteOrderMixing.TheoremC := by
  sorry

end PalomarEntry
