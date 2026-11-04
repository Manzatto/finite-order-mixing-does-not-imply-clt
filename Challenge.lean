module

public import Mathlib

/-!
# Palomar challenge statements

This file restates the project-local statement vocabulary needed for Theorems A, B, and C.
It imports Mathlib only; the proof development remains in the project modules.

The `run_cmd` lines reset Lean's local auxiliary-lemma cache at the original source-module
boundaries. Without these resets, Lean shares generated proof helpers across unrelated
statements in this single file, while the separately compiled source modules do not.
The resets do not change declarations, axioms, notation, or kernel checking.
-/

open MeasureTheory ProbabilityTheory Filter Topology Manifold Bundle
open scoped ENNReal NNReal Nat BoundedContinuousFunction ContDiff

@[expose] public section

namespace FiniteOrderMixing

abbrev Config := ℤ → Bool

def spin (b : Bool) : ℝ := if b then 1 else -1

def shift (w : Config) : Config := fun j => w (j + 1)

def Z (j : ℤ) (w : Config) : ℝ := spin (w j)

def S (n : ℕ) (w : Config) : ℝ := ∑ j ∈ Finset.range n, Z j w

noncomputable def dθ (θ : ℝ) (w w' : Config) : ℝ :=
  open Classical in
  if h : ∃ n : ℕ, ∃ j : ℤ, j.natAbs = n ∧ w j ≠ w' j then θ ^ Nat.find h else 0

def HolderBound (θ : ℝ) (F : Config → ℝ) (A : ℝ) : Prop :=
  (∀ w, |F w| ≤ A) ∧ ∀ w w', |F w - F w'| ≤ A * dθ θ w w'

def Gapped {s : ℕ} (n : Fin s → ℕ) (d : ℝ) : Prop :=
  ∀ i j : Fin s, i < j → (n i : ℝ) + d ≤ n j

def ExpMixingOrder {X : Type*} [MeasurableSpace X] (μ : Measure X) (T : X → X)
    (Bd : (X → ℝ) → ℝ → Prop) (s : ℕ) : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∀ (f : Fin s → X → ℝ) (A : Fin s → ℝ), (∀ i, Bd (f i) (A i)) →
    ∀ (n : Fin s → ℕ), StrictMono n → ∀ d : ℝ, Gapped n d →
      |∫ x, ∏ i, f i (T^[n i] x) ∂μ - ∏ i, ∫ x, f i x ∂μ| ≤
        C * Real.exp (-c * d) * ∏ i, A i

def ConvergesInDistribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ) (lam : Measure ℝ) : Prop :=
  ∀ u : ℝ →ᵇ ℝ, Tendsto (fun k => ∫ w, u (Y k w) ∂μ) atTop (𝓝 (∫ x, u x ∂lam))

def NoGaussianSubseqLimit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ (nk : ℕ → ℕ), StrictMono nk → ∀ v : ℝ≥0,
    ¬ ConvergesInDistribution μ
      (fun k w => Y (nk k) w / Real.sqrt (nk k)) (gaussianReal 0 v)

def TuplewiseIndep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℤ → Ω → ℝ)
    (p : ℕ) : Prop :=
  ∀ J : Finset ℤ, J.card ≤ p → iIndepFun (fun j : J => X j) μ

def SymmetricSigns {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℤ → Ω → ℝ) : Prop :=
  ∀ j, (∀ᵐ w ∂μ, X j w = 1 ∨ X j w = -1) ∧ μ {w | X j w = 1} = 1 / 2

def WindowsSeparated {s : ℕ} (K : ℕ) (a b : Fin s → ℤ) : Prop :=
  (∀ i, a i ≤ b i) ∧ ∀ i j l : Fin s, i < j → b i + K * (b l - a l + 1) < a j

def window (a b : ℤ) (w : Config) : Finset.Icc a b → Bool := fun j => w j

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def HolderObs (θ : ℝ) : (Config → ℝ) → ℝ → Prop := HolderBound θ

structure SymbolicProperties (R : ℕ) (ν : Measure Config) : Prop where
  isProb : IsProbabilityMeasure ν
  invariant : MeasurePreserving shift ν ν
  fullSupport : ν.IsOpenPosMeasure
  signs : SymmetricSigns ν Z
  tuplewise : TuplewiseIndep ν Z (2 * R + 1)
  windows : ∃ K : ℕ, ∀ s, 2 ≤ s → s ≤ R → ∀ a b : Fin s → ℤ, WindowsSeparated K a b →
    iIndepFun (fun i => window (a i) (b i)) ν
  mixing : ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ s, 2 ≤ s → s ≤ R →
    ExpMixingOrder ν shift (HolderObs θ) s
  moment : ∃ δ > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∫ w, (S n w / Real.sqrt n) ^ (2 * R + 2) ∂ν ≤ ((2 * R + 1)‼ : ℝ) - δ
  noGaussian : NoGaussianSubseqLimit ν S
  higherOrder : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∃ n : Fin (2 * R + 2) → ℕ, StrictMono n ∧ (∀ i, n i < N) ∧ Gapped n (N / C) ∧
      c * (N : ℝ) ^ (-((2 * R + 2 : ℕ) : ℝ) / 2) ≤
        -∫ w, ∏ i, Z (n i) w ∂ν
  notMixingL : ∀ θ : ℝ, 0 < θ → θ < 1 →
    ¬ ExpMixingOrder ν shift (HolderObs θ) (2 * R + 2)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

abbrev Torus := UnitAddTorus (Fin 2)

abbrev TorusVector := Fin 2 → ℝ

def torusProj (x : TorusVector) : Torus := fun i => (x i : UnitAddCircle)

structure TorusLinearCoordinates (T : Torus → Torus)
    (L : TorusVector ≃L[ℝ] TorusVector) : Prop where
  projection : ∀ x, T (torusProj x) = torusProj (L x)
  localCoordinates : ∀ p : TorusVector,
    ∃ c d : OpenPartialHomeomorph TorusVector Torus,
      p ∈ c.source ∧ L p ∈ d.source ∧
      (∀ x, c x = torusProj x) ∧ (∀ x, d x = torusProj x) ∧
      (fun x => d.symm (T (c x))) =ᶠ[𝓝 p] L ∧
      AnalyticAt ℝ (fun x => d.symm (T (c x))) p ∧
      HasFDerivAt (fun x => d.symm (T (c x)))
        (L : TorusVector →L[ℝ] TorusVector) p

def TorusHyperbolicLift (L : TorusVector ≃L[ℝ] TorusVector) (Λ : Set Torus) : Prop :=
  ∃ (s u : TorusVector) (ρ : ℝ),
    s ≠ 0 ∧ u ≠ 0 ∧
    (∀ v : TorusVector, ∃ a b : ℝ, v = a • s + b • u) ∧
    (∀ a b : ℝ, a • s + b • u = 0 → a = 0 ∧ b = 0) ∧
    0 < ρ ∧ ρ < 1 ∧ L s = ρ • s ∧ L.symm u = ρ • u ∧
    ∀ p : TorusVector, torusProj p ∈ Λ → ∀ (n : ℕ) (a : ℝ),
      ‖fderiv ℝ (L ^ n) p (a • s)‖ ≤ ρ ^ n * ‖a • s‖ ∧
      ‖fderiv ℝ (L.symm ^ n) p (a • u)‖ ≤ ρ ^ n * ‖a • u‖

def IsAnalyticAnosovTorus (T : Equiv.Perm Torus) : Prop :=
  ∃ L : TorusVector ≃L[ℝ] TorusVector,
    TorusLinearCoordinates T L ∧ TorusLinearCoordinates (T⁻¹ : Equiv.Perm Torus) L.symm ∧
    TorusHyperbolicLift L Set.univ

def IsUniformlyHyperbolicTorus (T : Equiv.Perm Torus) (Λ : Set Torus) : Prop :=
  ∃ L : TorusVector ≃L[ℝ] TorusVector,
    TorusLinearCoordinates T L ∧ TorusLinearCoordinates (T⁻¹ : Equiv.Perm Torus) L.symm ∧
    TorusHyperbolicLift L Λ

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def LipBound {X : Type*} [PseudoMetricSpace X] (f : X → ℝ) (A : ℝ) : Prop :=
  (∀ x, |f x| ≤ A) ∧ ∀ x y, |f x - f y| ≤ A * dist x y

structure HorseshoeCoding {X : Type*} [PseudoMetricSpace X] (T : X → X) (cod : Config → X) :
    Prop where
  continuous : Continuous cod
  injective : Function.Injective cod
  conj : ∀ w, cod (shift w) = T (cod w)
  holder : ∃ C ϱ : ℝ, 0 < ϱ ∧ ϱ < 1 ∧ ∀ (ℓ : ℕ) (w w' : Config),
    (∀ j : ℤ, j.natAbs ≤ ℓ → w j = w' j) →
      dist (cod w) (cod w') ≤ C * ϱ ^ ℓ

def IsTwoSymbolHorseshoe {X : Type*} [PseudoMetricSpace X] (T : X → X) (Λ : Set X) : Prop :=
  ∃ cod : Config → X, HorseshoeCoding T cod ∧ Set.range cod = Λ

def orbitProcess {X : Type*} (T : Equiv.Perm X) (f : X → ℝ) (i : ℤ) (x : X) : ℝ :=
  f ((T ^ i) x)

def statBasin {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (T : X → X) (μ : Measure X) : Set X :=
  {x | ∀ g : C(X, ℝ),
    Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop (𝓝 (∫ y, g y ∂μ))}

structure RealisationProperties {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (T : Equiv.Perm X) (Λ : Set X) (μ : Measure X) (f₀ : X → ℝ)
    (Bd : (X → ℝ) → ℝ → Prop) (R : ℕ) : Prop where
  isProb : IsProbabilityMeasure μ
  invariant : MeasurePreserving T μ μ
  support : μ.support = Λ
  mixing : ∀ s, 2 ≤ s → s ≤ R → ExpMixingOrder μ T Bd s
  signs : SymmetricSigns μ (orbitProcess T f₀)
  tuplewise : TuplewiseIndep μ (orbitProcess T f₀) (2 * R + 1)
  centred : ∫ x, f₀ x ∂μ = 0
  noGaussian : NoGaussianSubseqLimit μ (birkhoffSum T f₀)
  higherOrder : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∃ n : Fin (2 * R + 2) → ℕ, StrictMono n ∧ (∀ i, n i < N) ∧ Gapped n (N / C) ∧
      c * (N : ℝ) ^ (-((2 * R + 2 : ℕ) : ℝ) / 2) ≤
        |∫ x, ∏ i, f₀ (T^[n i] x) ∂μ|
  notMixing : ¬ ExpMixingOrder μ T Bd (2 * R + 2)

def torusLift (f : Torus → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  f fun i => (x i : UnitAddCircle)

def C1Bound (f : Torus → ℝ) (A : ℝ) : Prop :=
  ContDiff ℝ 1 (torusLift f) ∧ (∀ x, |f x| ≤ A) ∧
    ∀ x, ‖fderiv ℝ (torusLift f) x‖ ≤ A

def IsRealTrigPoly (g : Torus → ℝ) : Prop :=
  ∃ (s : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ),
    ∀ x, g x = (∑ k ∈ s, c k * UnitAddTorus.mFourier k x).re

def catMap : Equiv.Perm Torus where
  toFun x := ![2 • x 0 + x 1, x 0 + x 1]
  invFun x := ![x 0 - x 1, -x 0 + 2 • x 1]
  left_inv x := by
    funext i; fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero', Matrix.cons_val_succ', two_nsmul] <;> abel
  right_inv x := by
    funext i; fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero', Matrix.cons_val_succ', two_nsmul] <;> abel

structure TorusRealisation (k₀ : ℕ) (Λ : Set Torus) (f₀ : Torus → ℝ) (R : ℕ)
    (μ : Measure Torus) : Prop extends
    RealisationProperties (catMap ^ k₀) Λ μ f₀ C1Bound R where
  robust : ∃ δ > 0,
    (∀ g : Torus → ℝ, C1Bound (g - f₀) δ →
      NoGaussianSubseqLimit μ
        (birkhoffSum ⇑(catMap ^ k₀ : Equiv.Perm Torus)
          fun x => g x - ∫ y, g y ∂μ)) ∧
    ∃ g : Torus → ℝ, IsRealTrigPoly g ∧ C1Bound (g - f₀) δ

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def TheoremA : Prop :=
  ∃ k₀ : ℕ, 2 ≤ k₀ ∧ IsAnalyticAnosovTorus (catMap ^ k₀) ∧
    ∃ Λ : Set Torus,
      IsTwoSymbolHorseshoe ⇑(catMap ^ k₀ : Equiv.Perm Torus) Λ ∧
      IsUniformlyHyperbolicTorus (catMap ^ k₀) Λ ∧
      ∃ f₀ : Torus → ℝ, ContDiff ℝ (⊤ : ℕ∞) (torusLift f₀) ∧
        ∀ R : ℕ, 2 ≤ R → ∃ μ : Measure Torus, TorusRealisation k₀ Λ f₀ R μ

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def IsHyperbolicSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    (T : M → M) (Λ : Set M) : Prop :=
  IsCompact Λ ∧ T '' Λ = Λ ∧ ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
    ∃ Es Eu : ∀ x : M, Submodule ℝ (TangentSpace I x),
      (∀ x ∈ Λ, IsCompl (Es x) (Eu x)) ∧
      (∀ x ∈ Λ, (Es x).map
        (mfderiv I I T x : TangentSpace I x →ₗ[ℝ] TangentSpace I (T x)) = Es (T x)) ∧
      (∀ x ∈ Λ, (Eu x).map
        (mfderiv I I T x : TangentSpace I x →ₗ[ℝ] TangentSpace I (T x)) = Eu (T x)) ∧
      (∀ x ∈ Λ, ∀ n : ℕ, ∀ v ∈ Es x,
        ‖mfderiv I I (T^[n]) x v‖ ≤ C * ρ ^ n * ‖v‖) ∧
      (∀ x ∈ Λ, ∀ n : ℕ, ∀ v ∈ Eu x,
        ‖v‖ ≤ C * ρ ^ n * ‖mfderiv I I (T^[n]) x v‖)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

noncomputable def dSupNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    (f : M → ℝ) : ℝ := ⨆ x, ‖mfderiv I 𝓘(ℝ, ℝ) f x‖

universe u_3 in
noncomputable def supNorm {M : Type u_3} (f : M → ℝ) : ℝ := ⨆ x, |f x|

noncomputable def c1Norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    (f : M → ℝ) : ℝ := supNorm f + dSupNorm I f

def C1BoundM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    (f : M → ℝ) (A : ℝ) : Prop :=
  ContMDiff I 𝓘(ℝ, ℝ) 1 f ∧ ∃ a b : ℝ, (∀ x, |f x| ≤ a) ∧
    (∀ x, ‖mfderiv I 𝓘(ℝ, ℝ) f x‖ ≤ b) ∧ a + b ≤ A

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def IsSmoothVolume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [MeasurableSpace M] (m : Measure M) : Prop :=
  ∀ x : M, ∃ (lam : Measure E) (ρ : E → ℝ), lam.IsAddHaarMeasure ∧
    ContDiffOn ℝ ∞ ρ (extChartAt I x).target ∧
    (∀ e ∈ (extChartAt I x).target, 0 < ρ e) ∧
    (m.restrict (extChartAt I x).source).map (extChartAt I x) =
      (lam.restrict (extChartAt I x).target).withDensity
        (fun e => ENNReal.ofReal (ρ e))

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def IsHyperbolicHorseshoe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    (T : M → M) (Λ : Set M) : Prop :=
  IsTwoSymbolHorseshoe T Λ ∧ IsHyperbolicSet I T Λ

structure PhysicalRealisation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [MeasurableSpace M]
    {r : WithTop ℕ∞} (T : M ≃ₘ^r⟮I, I⟯ M) (Λ : Set M) (μ : Measure M)
    (f₀ : M → ℝ) (R : ℕ) : Prop extends
    RealisationProperties T.toEquiv Λ μ f₀ (C1BoundM I) R where
  smooth : ContMDiff I 𝓘(ℝ) ∞ f₀
  mixingC1 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ f : Fin R → M → ℝ, (∀ i, ContMDiff I 𝓘(ℝ, ℝ) 1 (f i)) →
      ∀ n : Fin R → ℕ, StrictMono n → ∀ d : ℝ, Gapped n d →
        |∫ x, ∏ i, f i (T^[n i] x) ∂μ - ∏ i, ∫ x, f i x ∂μ| ≤
          C * Real.exp (-c * d) * ∏ i, c1Norm I (f i)
  robust : ∃ δ > 0, ∀ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 1 g →
    c1Norm I (g - f₀) < δ →
      NoGaussianSubseqLimit μ
        (birkhoffSum T fun x => g x - ∫ y, g y ∂μ)
  basin : ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧
    (∀ g : C(M, ℝ), TendstoUniformlyOn
      (fun n y => birkhoffAverage ℝ T g n y)
      (fun _ => ∫ y, g y ∂μ) atTop W) ∧ W ⊆ statBasin T μ
  basinPos : ∀ m : Measure M, m.IsOpenPosMeasure → 0 < m (statBasin T μ)
  physical : ∀ m : Measure M, IsSmoothVolume I m → 0 < m (statBasin T μ)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

@[instance_reducible] noncomputable def boundedRiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] [T3Space M] :
    MetricSpace M := by
  let d : M → M → ℝ≥0∞ := fun x y => min 2 (riemannianEDist I x y)
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofEDistOfTopology d
    (fun x => by simp [d, riemannianEDist_self])
    (fun x y => by simp only [d, riemannianEDist_comm (I := I) (x := x) (y := y)])
    (fun x y z => by
      dsimp [d]
      grw [riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z),
        min_add_distrib, min_le_right])
    (fun x => (basis_sets (𝓝 x)).to_hasBasis'
      (fun s hs => by
        obtain ⟨c, hc, hcs⟩ := setOfPred_riemannianEDist_lt_subset_nhds' I hs
        refine ⟨min c 1, by positivity, fun y hy => hcs ?_⟩
        change min 2 (riemannianEDist I x y) < min c 1 at hy
        have hlt : riemannianEDist I x y < min c 1 := by
          rcases (min_lt_iff.1 hy) with h | h
          · exact False.elim (by have := h.trans_le (min_le_right c 1); norm_num at this)
          · exact h
        exact hlt.trans_le (min_le_left _ _))
      (fun c hc => by
        filter_upwards [eventually_riemannianEDist_lt I x hc] with y hy
        exact (min_le_right _ _).trans_lt hy))
  letI : EMetricSpace M := EMetricSpace.ofT0PseudoEMetricSpace M
  exact EMetricSpace.toMetricSpace fun x y =>
    ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (min_le_left _ _)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def TheoremB {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
    {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N]
    [RiemannianBundle (fun (x : N) ↦ TangentSpace J x)]
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace N] [Nonempty N]
    [MeasurableSpace N] [BorelSpace N]
    [IsContinuousRiemannianBundle E' (fun (x : N) ↦ TangentSpace J x)] : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    letI := boundedRiemannianMetric J N
    ∃ (T : N ≃ₘ^∞⟮J, J⟯ N) (Λ : Set N) (μ : Measure N) (f₀ : N → ℝ),
      IsHyperbolicHorseshoe J T Λ ∧ PhysicalRealisation J T Λ μ f₀ R

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def TheoremC : Prop :=
  ∀ R : ℕ, 2 ≤ R → ∃ ν : Measure Config, SymbolicProperties R ν

end FiniteOrderMixing

open MeasureTheory ProbabilityTheory Filter Topology Manifold Bundle
open scoped ContDiff

namespace PalomarEntry

theorem theoremA : FiniteOrderMixing.TheoremA := by
  sorry

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N]
  [RiemannianBundle (fun (x : N) ↦ TangentSpace J x)]

theorem theoremB [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    (hE : Module.finrank ℝ E' = 2) [J.Boundaryless]
    [IsManifold J ∞ N] [CompactSpace N] [Nonempty N] [MeasurableSpace N] [BorelSpace N]
    [IsContinuousRiemannianBundle E' (fun (x : N) ↦ TangentSpace J x)] :
    FiniteOrderMixing.TheoremB J (N := N) := by
  sorry

theorem theoremC : FiniteOrderMixing.TheoremC := by
  sorry

end PalomarEntry
