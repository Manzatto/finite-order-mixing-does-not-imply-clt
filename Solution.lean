module
public import FiniteOrderMixing.TheoremA
public import FiniteOrderMixing.TheoremB
public import FiniteOrderMixing.TheoremC

/-!
# Proofs for the Palomar challenge statements

Each declaration reuses the corresponding proof in the formalization.
-/

open MeasureTheory ProbabilityTheory Filter Topology Manifold Bundle
open scoped ContDiff

@[expose] public section

namespace PalomarEntry

theorem theoremA : FiniteOrderMixing.TheoremA := FiniteOrderMixing.theoremA

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N]
  [RiemannianBundle (fun (x : N) ↦ TangentSpace J x)]

theorem theoremB [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    (hE : Module.finrank ℝ E' = 2) [J.Boundaryless]
    [IsManifold J ∞ N] [CompactSpace N] [Nonempty N] [MeasurableSpace N] [BorelSpace N]
    [IsContinuousRiemannianBundle E' (fun (x : N) ↦ TangentSpace J x)] :
    FiniteOrderMixing.TheoremB J (N := N) :=
  FiniteOrderMixing.theoremB J hE

theorem theoremC : FiniteOrderMixing.TheoremC := FiniteOrderMixing.theoremC

end PalomarEntry
