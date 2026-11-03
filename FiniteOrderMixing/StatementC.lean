module
public import FiniteOrderMixing.Statements

/-!
# Theorem C statement

The stationary symbolic construction from Theorem C of the paper.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace FiniteOrderMixing

/-- **Theorem `thm:symbolic`** (symbolic realisation). -/
def TheoremC : Prop :=
  ∀ R : ℕ, 2 ≤ R → ∃ ν : Measure Config, SymbolicProperties R ν

end FiniteOrderMixing
