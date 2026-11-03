module
public import FiniteOrderMixing.Realisation.Physical
public import FiniteOrderMixing.StatementB

/-!
# Theorem B: physical realisation

`TheoremB` is the statement of Theorem `thm:physical` of the paper.
`theoremB` proves it. Auxiliary results are in `Realisation/Physical.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Manifold Bundle
open scoped ContDiff

@[expose] public section

namespace FiniteOrderMixing

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N]
  [RiemannianBundle (fun (x : N) ↦ TangentSpace J x)]

/-! ## Proof -/

/-- **Theorem `thm:physical`**, from the explicit hyperbolic wandering construction. -/
theorem theoremB [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    (hE : Module.finrank ℝ E' = 2) [J.Boundaryless]
    [IsManifold J ∞ N] [CompactSpace N] [Nonempty N] [MeasurableSpace N] [BorelSpace N]
    [IsContinuousRiemannianBundle E' (fun (x : N) ↦ TangentSpace J x)] :
    TheoremB J (N := N) := by
  intro R hR
  let := boundedRiemannianMetric J N
  have hd : ∀ x y : N, edist x y = min 2 (riemannianEDist J x y) := fun _ _ => rfl
  apply theoremB_of_metric J
    (fun _ _ h => h.lipBound_of_boundedRiemannian hd) ⊤ R hR
  intro w
  obtain ⟨T, cod, hc, hh, -, hW⟩ := surface_wandering_hyp_of_chartUpperLip J hE
    (chartUpperLip_of_edist_le_riemannian (I := J) (M' := N)
      (fun x y => by rw [hd]; exact min_le_right _ _))
    ⊤ le_top w
  exact ⟨T, cod, hc, hh, hW⟩

end FiniteOrderMixing
