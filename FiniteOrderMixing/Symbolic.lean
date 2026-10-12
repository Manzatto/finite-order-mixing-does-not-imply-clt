import FiniteOrderMixing.Moment
import FiniteOrderMixing.Statements

/-!
# Proof of Theorem `thm:symbolic` from Proposition `prop:hierarchy`

`symbolic_of_hierarchyLaw` assembles all the properties of the measure `ν` constructed in
Section `sec:limit` from any law of the nested marker sets with properties `(H1)–(H4)`, for
`L = 2R + 2`.
-/

open MeasureTheory ProbabilityTheory
open scoped Nat

namespace FiniteOrderMixing

/-- Theorem `thm:symbolic`, assuming a law of the nested marker sets with `(H1)–(H4)`. -/
theorem symbolic_of_hierarchyLaw {R : ℕ} (hR : 2 ≤ R) {P : Measure Hspace}
    (hP : HierarchyLaw (2 * R + 2) P) : ∃ ν : Measure Config, SymbolicProperties R ν := by
  have hL : 6 ≤ 2 * R + 2 := by omega
  have hLe : Even (2 * R + 2) := ⟨R + 1, by ring⟩
  have hm : 2 * R + 2 = 2 * (R + 1) := by ring
  refine ⟨nu hP hL hLe, ?_⟩
  obtain ⟨K, hK⟩ := nu_windows hP hL hLe
  obtain ⟨δ, hδ, n₀, hmom⟩ := nu_moment hP hL hLe hm
  exact
    { isProb := inferInstance
      invariant := nu_measurePreserving hP hL hLe
      fullSupport := nu_isOpenPosMeasure hP hL hLe
      signs := nu_signs hP hL hLe
      tuplewise := by
        have := nu_tuplewise hP hL hLe
        rwa [show 2 * R + 2 - 1 = 2 * R + 1 by omega] at this
      windows := ⟨K, fun s _ hsR a b hab => hK s (by omega) a b hab⟩
      mixing := fun θ h0 h1 s _ hsR => nu_expMixing hP hL hLe θ h0 h1 s (by omega)
      moment := ⟨δ, hδ, n₀, fun n hn => by
        have := hmom n hn
        rwa [show 2 * (R + 1) = 2 * R + 2 by ring, show 2 * R + 2 - 1 = 2 * R + 1 by omega]
          at this⟩
      noGaussian := nu_noGaussian hP hL hLe hm
      higherOrder := nu_higherOrder hP hL hLe hm
      notMixingL := fun θ h0 h1 => nu_not_expMixing hP hL hLe hm θ h0 h1 }

end FiniteOrderMixing
