module
public import FiniteOrderMixing.Realisation.Torus

/-!
# Theorem A statement

The analytic Anosov torus realization from Theorem A of the paper.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

@[expose] public section

namespace FiniteOrderMixing

/-- **Theorem `thm:analytic`** (linear Anosov realisation). There are `k₀ ≥ 2`, a two-symbol
horseshoe `Λ` of `T = A^{k₀}` and a smooth `f₀` such that, for every `R ≥ 2`, some invariant
probability measure `μ` has all the properties of Theorem A. -/
def TheoremA : Prop :=
  ∃ k₀ : ℕ, 2 ≤ k₀ ∧ IsAnalyticAnosovTorus (catMap ^ k₀) ∧
    ∃ Λ : Set Torus, IsTwoSymbolHorseshoe ⇑(catMap ^ k₀ : Equiv.Perm Torus) Λ ∧
    IsUniformlyHyperbolicTorus (catMap ^ k₀) Λ ∧
    ∃ f₀ : Torus → ℝ, ContDiff ℝ (⊤ : ℕ∞) (torusLift f₀) ∧
      ∀ R : ℕ, 2 ≤ R → ∃ μ : Measure Torus, TorusRealisation k₀ Λ f₀ R μ

end FiniteOrderMixing
