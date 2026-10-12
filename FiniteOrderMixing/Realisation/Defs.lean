import FiniteOrderMixing.Statements
import FiniteOrderMixing.Realisation.TorusGeometry

/-!
# Shared definitions for dynamical realisations

This file defines the common coding and statistical properties, the torus model, and
`TorusRealisation` and `SurfaceRealisation`. The statements and proofs of the main theorems
are in `FiniteOrderMixing/TheoremA.lean` and `FiniteOrderMixing/TheoremB.lean`.

## Conventions

* As in `Basic.lean`, norms are encoded as *bounds*.  `LipBound f A` says that `A` dominates
  both `‖f‖_∞` and the Lipschitz constant of `f`; `C1Bound f A` (on the torus) says that `A`
  dominates both `‖f‖_∞` and `‖Df‖_∞`.  Since `max ≤ sum ≤ 2 max`, every estimate
  `≤ C ∏ ‖f_i‖_{C¹}` is equivalent to one `≤ C' ∏ A_i`.
* **Horseshoes.**  `HorseshoeCoding T cod` says that `cod : Σ → X` is a continuous injective
  conjugacy `cod ∘ σ = T ∘ cod` from the full two-sided shift onto its image, whose cylinders on
  `[-ℓ, ℓ]` have images of diameter `≤ C ϱ^ℓ` (Theorem `thm:hyperbolic-coding`).  A two-symbol
  horseshoe is the image of such a coding. Theorem A additionally records uniform hyperbolicity
  of this image and a real-analytic Anosov certificate for the ambient linear torus map.
* **Surfaces.** The auxiliary version `theoremB_lipschitz` uses a metric locally bi-Lipschitz
  to chart coordinates (`IsChartLipschitzMetric`) and Lipschitz observables. The main statement
  `TheoremB` uses `C¹` observables and a Riemannian structure, including on disconnected surfaces;
  its properties are recorded by `PhysicalRealisation` in `Realisation/Physical.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Manifold

namespace FiniteOrderMixing

/-! ## Observables on a metric space -/

/-- `LipBound f A`: `A` bounds both `‖f‖_∞` and the Lipschitz constant of `f`. -/
def LipBound {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (A : ℝ) : Prop :=
  (∀ x, |f x| ≤ A) ∧ ∀ x y, |f x - f y| ≤ A * dist x y

/-! ## Two-symbol horseshoes -/

/-- `cod : Σ → X` codes a two-symbol horseshoe of `T`: a continuous injective conjugacy from the
full shift `(Σ, σ)` onto its image, with exponentially small images of cylinders. -/
structure HorseshoeCoding {X : Type*} [PseudoMetricSpace X] (T : X → X) (cod : Config → X) :
    Prop where
  continuous : Continuous cod
  injective : Function.Injective cod
  conj : ∀ ω, cod (shift ω) = T (cod ω)
  holder : ∃ C ϱ : ℝ, 0 < ϱ ∧ ϱ < 1 ∧ ∀ (ℓ : ℕ) (ω ω' : Config),
    (∀ j : ℤ, j.natAbs ≤ ℓ → ω j = ω' j) → dist (cod ω) (cod ω') ≤ C * ϱ ^ ℓ

/-- `Λ` is a two-symbol horseshoe of `T`: the image of a horseshoe coding. -/
def IsTwoSymbolHorseshoe {X : Type*} [PseudoMetricSpace X] (T : X → X) (Λ : Set X) : Prop :=
  ∃ cod : Config → X, HorseshoeCoding T cod ∧ Set.range cod = Λ

/-! ## Processes, basins -/

/-- The two-sided process `(f ∘ T^i)_{i ∈ ℤ}` of an invertible map `T`. -/
def orbitProcess {X : Type*} (T : Equiv.Perm X) (f : X → ℝ) (i : ℤ) (x : X) : ℝ :=
  f ((T ^ i) x)

/-- The statistical basin `B_T(μ)`: points whose time averages of every continuous observable
converge to its `μ`-integral. -/
def statBasin {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (T : X → X) (μ : Measure X) :
    Set X :=
  {x | ∀ g : C(X, ℝ), Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop (𝓝 (∫ y, g y ∂μ))}

/-! ## The common list of properties of Theorems A and B -/

/-- Items (i)–(iv) and (vi) of Theorems A and B, for the invertible map `T`, the horseshoe `Λ`,
the measure `μ`, the observable `f₀`, the class of observables `Bd` (with bounds) and the
order `R`.  The exponential mixing (ii) is given for every order `2 ≤ s ≤ R`. -/
structure RealisationProperties {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (T : Equiv.Perm X) (Λ : Set X) (μ : Measure X) (f₀ : X → ℝ)
    (Bd : (X → ℝ) → ℝ → Prop) (R : ℕ) : Prop where
  isProb : IsProbabilityMeasure μ
  invariant : MeasurePreserving T μ μ
  /-- (i) `supp μ = Λ`. -/
  support : μ.support = Λ
  /-- (ii) exponential mixing of every order `2 ≤ s ≤ R` for the class `Bd`. -/
  mixing : ∀ s, 2 ≤ s → s ≤ R → ExpMixingOrder μ T Bd s
  /-- (iii) the process `(f₀ ∘ T^i)_{i∈ℤ}` is `{-1,1}`-valued, symmetric and
  `(2R+1)`-tuplewise independent; in particular `μ(f₀) = 0`. -/
  signs : SymmetricSigns μ (orbitProcess T f₀)
  tuplewise : TuplewiseIndep μ (orbitProcess T f₀) (2 * R + 1)
  centred : ∫ x, f₀ x ∂μ = 0
  /-- (iv) `S_n f₀ / √n` has no Gaussian weak subsequential limit. -/
  noGaussian : NoGaussianSubseqLimit μ (birkhoffSum T f₀)
  /-- (vi) polynomially large order-`(2R+2)` correlations at gaps `≥ N/C`. -/
  higherOrder : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∃ n : Fin (2 * R + 2) → ℕ, StrictMono n ∧ (∀ i, n i < N) ∧ Gapped n (N / C) ∧
      c * (N : ℝ) ^ (-((2 * R + 2 : ℕ) : ℝ) / 2) ≤ |∫ x, ∏ i, f₀ (T^[n i] x) ∂μ|
  /-- (vi) hence no exponential mixing of order `2R+2` for the class `Bd`. -/
  notMixing : ¬ ExpMixingOrder μ T Bd (2 * R + 2)

/-! ## The torus and Theorem A -/

/-- The lift `f̃ = f ∘ (ℝ² → 𝕋²)` of a function on the torus to a `ℤ²`-periodic function on `ℝ²`. -/
def torusLift (f : Torus → ℝ) (x : Fin 2 → ℝ) : ℝ := f fun i => (x i : UnitAddCircle)

/-- `C1Bound f A`: `f ∈ C¹(𝕋²)` and `A` bounds both `‖f‖_∞` and `‖Df‖_∞`. -/
def C1Bound (f : Torus → ℝ) (A : ℝ) : Prop :=
  ContDiff ℝ 1 (torusLift f) ∧ (∀ x, |f x| ≤ A) ∧ ∀ x, ‖fderiv ℝ (torusLift f) x‖ ≤ A

/-- `g` is a real trigonometric polynomial: `g = Re ∑_{k ∈ s} c_k e^{2πi⟨k,·⟩}`. -/
def IsRealTrigPoly (g : Torus → ℝ) : Prop :=
  ∃ (s : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ),
    ∀ x, g x = (∑ k ∈ s, c k * UnitAddTorus.mFourier k x).re

/-- The cat map `A(x, y) = (2x + y, x + y) mod 1`. -/
def catMap : Equiv.Perm Torus where
  toFun x := ![2 • x 0 + x 1, x 0 + x 1]
  invFun x := ![x 0 - x 1, -x 0 + 2 • x 1]
  left_inv x := by
    funext i; fin_cases i <;> simp [two_nsmul]; abel
  right_inv x := by
    funext i; fin_cases i <;> simp [two_nsmul] <;> abel

/-- The properties of Theorem A for `T = A^{k₀}`, the horseshoe `Λ`, the observable `f₀`, the
order `R` and the measure `μ`. -/
structure TorusRealisation (k₀ : ℕ) (Λ : Set Torus) (f₀ : Torus → ℝ) (R : ℕ)
    (μ : Measure Torus) : Prop extends
    RealisationProperties (catMap ^ k₀) Λ μ f₀ C1Bound R where
  /-- (v) a `C¹`-neighbourhood of `f₀` without Gaussian limits, containing a real
  trigonometric polynomial. -/
  robust : ∃ δ > 0,
    (∀ g : Torus → ℝ, C1Bound (g - f₀) δ →
      NoGaussianSubseqLimit μ (birkhoffSum ⇑(catMap ^ k₀ : Equiv.Perm Torus) fun x => g x - ∫ y, g y ∂μ)) ∧
    ∃ g : Torus → ℝ, IsRealTrigPoly g ∧ C1Bound (g - f₀) δ

/-! ## Surfaces and Theorem B -/

section Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- The metric of `M` is locally bi-Lipschitz to the chart coordinates.  Riemannian distances
have this property. -/
def IsChartLipschitzMetric : Prop :=
  ∀ x : M, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, ∀ z ∈ U,
    dist y z ≤ C * ‖extChartAt I x y - extChartAt I x z‖ ∧
      ‖extChartAt I x y - extChartAt I x z‖ ≤ C * dist y z

variable [MeasurableSpace M]

/-- The properties of Theorem B for a `C^r` diffeomorphism `T`, the horseshoe `Λ`, the measure
`μ`, the observable `f₀` and the order `R`.  Observables are Lipschitz for the metric of `M`. -/
structure SurfaceRealisation {r : WithTop ℕ∞} (T : M ≃ₘ^r⟮I, I⟯ M) (Λ : Set M) (μ : Measure M)
    (f₀ : M → ℝ) (R : ℕ) : Prop extends
    RealisationProperties T.toEquiv Λ μ f₀ LipBound R where
  /-- `f₀ ∈ C^∞(M)`. -/
  smooth : ContMDiff I 𝓘(ℝ) (⊤ : ℕ∞) f₀
  /-- (iv) a neighbourhood of `f₀` without Gaussian limits. -/
  robust : ∃ δ > 0, ∀ g : M → ℝ, LipBound (g - f₀) δ →
    NoGaussianSubseqLimit μ (birkhoffSum T fun x => g x - ∫ y, g y ∂μ)
  /-- (v) a nonempty open set on which time averages converge uniformly; it lies in the basin. -/
  basin : ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧
    (∀ g : C(M, ℝ), TendstoUniformlyOn (fun n y => birkhoffAverage ℝ T g n y)
      (fun _ => ∫ y, g y ∂μ) atTop W) ∧ W ⊆ statBasin T μ
  /-- (v) hence `μ` is physical: its basin has positive measure for every measure charging open
  sets, in particular for every smooth volume. -/
  physical : ∀ m : Measure M, m.IsOpenPosMeasure → 0 < m (statBasin T μ)

end Surface

end FiniteOrderMixing
