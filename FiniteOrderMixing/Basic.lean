module

public import Mathlib

/-!
# Finite-order exponential mixing does not imply the CLT — basic notions

Shared vocabulary for the formalization of the paper.

## Conventions

* The symbol space `Σ = {-1,1}^ℤ` is encoded as `Config := ℤ → Bool`, with `true ↦ 1`,
  `false ↦ -1` (see `spin`).
* Norms are encoded as *bounds*: instead of the paper's `‖F‖_θ = ‖F‖_∞ + Lip_θ(F)` we use the
  predicate `HolderBound θ F A` ("`A` dominates both `‖F‖_∞` and `Lip_θ F`").  Since
  `max ≤ sum ≤ 2 max`, every estimate `≤ C ∏ ‖F_i‖` is equivalent to one `≤ C' ∏ A_i`, with
  `C' = 2^s C`; the constants in the paper are not tracked, so nothing is lost.
* The minimal time gap `Δ(n_1,…,n_s)` is encoded by the predicate `Gapped n d`
  ("all gaps are at least `d`"); an estimate `≤ C e^{-cΔ}` is the same as
  `∀ d, Gapped n d → … ≤ C e^{-c d}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace FiniteOrderMixing

/-! ## The symbolic space -/

/-- The two-sided binary shift space `Σ = {-1,1}^ℤ`, encoded as `ℤ → Bool`. -/
abbrev Config := ℤ → Bool

/-- `true ↦ 1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma spin_true : spin true = 1 := rfl
@[simp] lemma spin_false : spin false = -1 := rfl

lemma spin_sq (b : Bool) : spin b ^ 2 = 1 := by cases b <;> norm_num [spin]

lemma abs_spin (b : Bool) : |spin b| = 1 := by cases b <;> norm_num [spin]

/-- The left shift `(σ ω)_j = ω_{j+1}`. -/
def shift (ω : Config) : Config := fun j => ω (j + 1)

@[fun_prop]
lemma measurable_shift : Measurable shift :=
  Measurable.of_eval fun _ => measurable_pi_apply _

lemma continuous_shift : Continuous shift :=
  continuous_pi fun _ => continuous_apply _

lemma shift_iterate_apply (n : ℕ) (ω : Config) (j : ℤ) :
    (shift^[n] ω) j = ω (j + n) := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [shift]
    congr 1
    push_cast
    ring

/-- The coordinate process `Z_j(ω) = ω_j ∈ {-1,1}`. -/
def Z (j : ℤ) (ω : Config) : ℝ := spin (ω j)

@[fun_prop]
lemma measurable_Z (j : ℤ) : Measurable (Z j) :=
  (measurable_of_countable spin).comp (measurable_pi_apply j)

lemma Z_shift_iterate (n : ℕ) (j : ℤ) (ω : Config) : Z j (shift^[n] ω) = Z (j + n) ω := by
  simp [Z, shift_iterate_apply]

/-- Partial sums `S_n = ∑_{j<n} Z_j`. -/
def S (n : ℕ) (ω : Config) : ℝ := ∑ j ∈ Finset.range n, Z j ω

@[fun_prop]
lemma measurable_S (n : ℕ) : Measurable (S n) :=
  Finset.measurable_sum _ fun j _ => measurable_Z j

/-! ## The metric `d_θ` and Hölder observables -/

/-- `d_θ(ω, ω') = θ^{min {|j| : ω_j ≠ ω'_j}}` (and `0` if `ω = ω'`). -/
noncomputable def dθ (θ : ℝ) (ω ω' : Config) : ℝ :=
  open Classical in
  if h : ∃ n : ℕ, ∃ j : ℤ, j.natAbs = n ∧ ω j ≠ ω' j then θ ^ Nat.find h else 0

/-- `HolderBound θ F A`: `A` bounds both `‖F‖_∞` and the `d_θ`-Lipschitz constant of `F`,
i.e. `‖F‖_θ ≤ 2A` and `A ≤ ‖F‖_θ` is always a valid choice. -/
def HolderBound (θ : ℝ) (F : Config → ℝ) (A : ℝ) : Prop :=
  (∀ ω, |F ω| ≤ A) ∧ ∀ ω ω', |F ω - F ω'| ≤ A * dθ θ ω ω'

/-! ## Time tuples -/

/-- All gaps of the time tuple are at least `d`: `Δ(n) ≥ d`. -/
def Gapped {s : ℕ} (n : Fin s → ℕ) (d : ℝ) : Prop :=
  ∀ i j : Fin s, i < j → (n i : ℝ) + d ≤ n j

/-! ## Exponential mixing -/

/-- Exponential mixing of order `s` for an abstract dynamical system `(X, T, μ)` and a class of
observables described by a bound predicate `Bd f A` ("`A` dominates the norm of `f`"):
`|μ(∏ f_i ∘ T^{n_i}) - ∏ μ(f_i)| ≤ C e^{-cΔ(n)} ∏ ‖f_i‖`. -/
def ExpMixingOrder {X : Type*} [MeasurableSpace X] (μ : Measure X) (T : X → X)
    (Bd : (X → ℝ) → ℝ → Prop) (s : ℕ) : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∀ (f : Fin s → X → ℝ) (A : Fin s → ℝ), (∀ i, Bd (f i) (A i)) →
    ∀ (n : Fin s → ℕ), StrictMono n → ∀ d : ℝ, Gapped n d →
      |∫ x, ∏ i, f i (T^[n i] x) ∂μ - ∏ i, ∫ x, f i x ∂μ| ≤ C * Real.exp (-c * d) * ∏ i, A i

/-! ## Convergence in distribution and Gaussian limits -/

/-- `Y_k ⇒ λ` under `μ`: the laws of `Y_k` converge weakly to `λ`, i.e.
`∫ u(Y_k) dμ → ∫ u dλ` for every bounded continuous `u`. -/
def ConvergesInDistribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ) (lam : Measure ℝ) : Prop :=
  ∀ u : ℝ →ᵇ ℝ, Tendsto (fun k => ∫ ω, u (Y k ω) ∂μ) atTop (𝓝 (∫ x, u x ∂lam))

/-- The normalised sums `Y_n / √n` have **no Gaussian weak subsequential limit**:
for every strictly increasing `n_k` and every variance `v ≥ 0` (including `v = 0`, the point mass),
`Y_{n_k}/√n_k ⇏ N(0, v)`. -/
def NoGaussianSubseqLimit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ (nk : ℕ → ℕ), StrictMono nk → ∀ v : ℝ≥0,
    ¬ ConvergesInDistribution μ (fun k ω => Y (nk k) ω / Real.sqrt (nk k)) (gaussianReal 0 v)

/-! ## Independence notions -/

/-- `p`-tuplewise independence of a real process `X`: any `≤ p` distinct coordinates are
jointly independent. -/
def TuplewiseIndep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℤ → Ω → ℝ)
    (p : ℕ) : Prop :=
  ∀ J : Finset ℤ, J.card ≤ p → iIndepFun (fun j : J => X j) μ

/-- `X` is `{-1,1}`-valued with symmetric marginals. -/
def SymmetricSigns {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℤ → Ω → ℝ) : Prop :=
  ∀ j, (∀ᵐ ω ∂μ, X j ω = 1 ∨ X j ω = -1) ∧ μ {ω | X j ω = 1} = 1 / 2

/-- Windows `I_i = [a_i, b_i]`, ordered, with successive distances `> K · max_l |I_l|`. -/
def WindowsSeparated {s : ℕ} (K : ℕ) (a b : Fin s → ℤ) : Prop :=
  (∀ i, a i ≤ b i) ∧ ∀ i j l : Fin s, i < j → b i + K * (b l - a l + 1) < a j

/-- Restriction of a configuration to the window `[a, b]`. -/
def window (a b : ℤ) (ω : Config) : Finset.Icc a b → Bool := fun j => ω j

end FiniteOrderMixing
