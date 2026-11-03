module
public import FiniteOrderMixing.HierarchyLaw
public import FiniteOrderMixing.Symbolic
public import FiniteOrderMixing.StatementC

/-!
# Theorem C: symbolic realisation

`TheoremC` is the statement of Theorem `thm:symbolic` of the paper;
`theoremC` proves it. Auxiliary results are in `HierarchyLaw.lean` and `Symbolic.lean`.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace FiniteOrderMixing

/-! ## Proof -/

/-- **Theorem `thm:symbolic`.** -/
theorem theoremC : TheoremC := by
  intro R hR
  obtain ⟨P, hP⟩ := exists_hierarchyLaw (L := 2 * R + 2) (by omega)
  exact symbolic_of_hierarchyLaw hR hP

end FiniteOrderMixing
