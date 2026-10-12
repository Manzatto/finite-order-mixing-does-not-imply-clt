import FiniteOrderMixing.Realisation.Torus
import FiniteOrderMixing.TheoremC

/-!
# Theorem A: linear Anosov realisation

`TheoremA` is the statement of Theorem `thm:analytic` of the paper;
`theoremA` proves it. Auxiliary results are in `Realisation/Torus.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace FiniteOrderMixing

/-! ## Statement -/

/-- **Theorem `thm:analytic`** (linear Anosov realisation).  There are `k₀ ≥ 2`, a two-symbol
horseshoe `Λ` of `T = A^{k₀}` and a smooth `f₀` such that, for every `R ≥ 2`, some invariant
probability measure `μ` has all the properties of Theorem A. -/
def TheoremA : Prop :=
  ∃ k₀ : ℕ, 2 ≤ k₀ ∧ IsAnalyticAnosovTorus (catMap ^ k₀) ∧
    ∃ Λ : Set Torus, IsTwoSymbolHorseshoe ⇑(catMap ^ k₀ : Equiv.Perm Torus) Λ ∧
    IsUniformlyHyperbolicTorus (catMap ^ k₀) Λ ∧
    ∃ f₀ : Torus → ℝ, ContDiff ℝ (⊤ : ℕ∞) (torusLift f₀) ∧
      ∀ R : ℕ, 2 ≤ R → ∃ μ : Measure Torus, TorusRealisation k₀ Λ f₀ R μ

/-! ## Proof -/

/-- **Theorem `thm:analytic`** (linear Anosov realisation), from Theorem C and the explicit
horseshoe `catMap_horseshoe` of `A²`. -/
theorem theoremA : TheoremA := by
  let k₀ : ℕ := 2
  let cod := catCod
  have hc : HorseshoeCoding ⇑(catMap ^ k₀ : Equiv.Perm Torus) cod := catCod_horseshoeCoding
  obtain ⟨f₀, hf₀s, hf₀c, hf₀b, hf₀, htrig⟩ := exists_smooth_sign hc.continuous hc.injective
  have hf₀1 : ContDiff ℝ 1 (torusLift f₀) := hf₀s.of_le (by exact_mod_cast le_top)
  obtain ⟨A₀, hA₀⟩ := exists_C1Bound hf₀1 hf₀b
  refine ⟨k₀, le_rfl, catMap_sq_analyticAnosov, Set.range cod, ⟨cod, hc, rfl⟩,
    catCod_uniformlyHyperbolic, f₀, hf₀s, fun R hR => ?_⟩
  obtain ⟨ν, hν⟩ := theoremC R hR
  have hT := continuous_catMap_pow k₀
  have hprops := realisationProperties_of_coding hR hν hT (continuous_catMap_pow_inv k₀) hc hf₀c
    hf₀ (fun f A h => h.lipBound) hA₀
  obtain ⟨δ, hδ, hrob⟩ := robust_of_coding hR hν hT.measurable hc hf₀c hf₀ hf₀b
  obtain ⟨g, hg, hgδ⟩ := htrig δ hδ
  exact ⟨ν.map cod, hprops, δ, hδ, fun g hg => hrob g hg.lipBound, g, hg, hgδ⟩

end FiniteOrderMixing
