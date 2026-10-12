import FiniteOrderMixing.Basic

/-!
# Properties of the symbolic process

`SymbolicProperties R ν` records the conclusions of Theorem `thm:symbolic` for a
full-support shift-invariant probability measure `ν` on
`Σ = {-1,1}^ℤ` such that, with `L = 2R + 2`:

* (i)   the coordinate process is `{-1,1}`-valued, symmetric and `(2R+1)`-tuplewise independent;
* (ii)  windows separated by `K_R · (max window length)` are jointly independent (`s ≤ R`);
* (iii) `(Σ, σ, ν)` is exponentially mixing of every order `2 ≤ s ≤ R` on `F_θ(Σ)`;
* (iv)  `E_ν (S_n/√n)^L ≤ (L-1)!! - δ` for large `n`; hence no Gaussian subsequential limit;
* (v)   an order-`L` correlation at gaps `≳ N` is `≳ N^{-L/2}`; hence no exponential mixing of
        order `L`.

The main statement `TheoremC` and its proof `theoremC` are in `TheoremC.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Nat BoundedContinuousFunction

namespace FiniteOrderMixing

/-- Observables of the symbolic system with `‖F‖_θ ≲ A`. -/
def HolderObs (θ : ℝ) : (Config → ℝ) → ℝ → Prop := HolderBound θ

/-- The list of properties (i)–(v) of Theorem `thm:symbolic` for a given measure `ν`. -/
structure SymbolicProperties (R : ℕ) (ν : Measure Config) : Prop where
  isProb : IsProbabilityMeasure ν
  invariant : MeasurePreserving shift ν ν
  fullSupport : ν.IsOpenPosMeasure
  /-- (i) symmetric signs and `(2R+1)`-tuplewise independence. -/
  signs : SymmetricSigns ν Z
  tuplewise : TuplewiseIndep ν Z (2 * R + 1)
  /-- (ii) independence of separated windows. -/
  windows : ∃ K : ℕ, ∀ s, 2 ≤ s → s ≤ R → ∀ a b : Fin s → ℤ, WindowsSeparated K a b →
    iIndepFun (fun i => window (a i) (b i)) ν
  /-- (iii) exponential mixing through order `R` for `d_θ`-Hölder observables. -/
  mixing : ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ s, 2 ≤ s → s ≤ R →
    ExpMixingOrder ν shift (HolderObs θ) s
  /-- (iv) deficit in the `L`-th moment, `L = 2R + 2`. -/
  moment : ∃ δ > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∫ ω, (S n ω / Real.sqrt n) ^ (2 * R + 2) ∂ν ≤ ((2 * R + 1)‼ : ℝ) - δ
  /-- (iv) hence no Gaussian weak subsequential limit. -/
  noGaussian : NoGaussianSubseqLimit ν S
  /-- (v) polynomially large order-`L` correlation at gaps proportional to `N`. -/
  higherOrder : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∃ n : Fin (2 * R + 2) → ℕ, StrictMono n ∧ (∀ i, n i < N) ∧ Gapped n (N / C) ∧
      c * (N : ℝ) ^ (-((2 * R + 2 : ℕ) : ℝ) / 2) ≤ -∫ ω, ∏ i, Z (n i) ω ∂ν
  /-- (v) hence no exponential mixing of order `L`. -/
  notMixingL : ∀ θ : ℝ, 0 < θ → θ < 1 → ¬ ExpMixingOrder ν shift (HolderObs θ) (2 * R + 2)

end FiniteOrderMixing
