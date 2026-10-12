import FiniteOrderMixing.HierarchyLaw
import FiniteOrderMixing.Symbolic

/-!
# Theorem C: symbolic realisation

`TheoremC` is the statement of Theorem `thm:symbolic` of the paper;
`theoremC` proves it. Auxiliary results are in `HierarchyLaw.lean` and `Symbolic.lean`.
-/

open MeasureTheory ProbabilityTheory

namespace FiniteOrderMixing

/-! ## Statement -/

/-- **Theorem `thm:symbolic`** (symbolic realisation). -/
def TheoremC : Prop :=
  ∀ R : ℕ, 2 ≤ R → ∃ ν : Measure Config, SymbolicProperties R ν

/-! ## Proof -/

/-- **Theorem `thm:symbolic`.** -/
theorem theoremC : TheoremC := by
  intro R hR
  obtain ⟨P, hP⟩ := exists_hierarchyLaw (L := 2 * R + 2) (by omega)
  exact symbolic_of_hierarchyLaw hR hP

end FiniteOrderMixing
