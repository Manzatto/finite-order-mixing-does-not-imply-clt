module

public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Tactic.Linarith

/-!
# Analyticity and uniform hyperbolicity for linear torus maps

We use the standard trivialization of the tangent bundle of `ℝ²/ℤ²`: tangent vectors are
vectors in `ℝ²`, independently of the base point. Actual open quotient charts certify the
local analytic coordinate maps and their derivatives. The hyperbolicity certificate records
a complementary pair of constant lines, invariance, and uniform derivative estimates.
This is a torus-specific formulation, not a definition for arbitrary manifolds.
-/

@[expose] public section

open Filter Topology

namespace FiniteOrderMixing

/-- The torus `𝕋² = (ℝ/ℤ)²`, with its flat (sup) metric. -/
abbrev Torus := UnitAddTorus (Fin 2)

/-- Tangent vectors in the standard quotient trivialization. -/
abbrev TorusVector := Fin 2 → ℝ

/-- The quotient projection `ℝ² → 𝕋²`. -/
def torusProj (x : TorusVector) : Torus := fun i => (x i : UnitAddCircle)

/-- An inverse quotient chart centered at a lift `p`; its source has side length one. -/
noncomputable def torusQuotientChart (p : TorusVector) :
    OpenPartialHomeomorph TorusVector Torus :=
  OpenPartialHomeomorph.pi fun i => AddCircle.openPartialHomeomorphCoe 1 (p i - 1 / 2)

lemma torusQuotientChart_apply (p x : TorusVector) : torusQuotientChart p x = torusProj x := rfl

lemma torusQuotientChart_mem_source (p : TorusVector) :
    p ∈ (torusQuotientChart p).source := by
  intro i _
  change p i ∈ Set.Ioo (p i - 1 / 2) (p i - 1 / 2 + 1)
  constructor <;> linarith

/-- A linear lift gives genuine analytic local coordinate expressions for a torus map.
The local derivative is the same continuous linear map at every base point. -/
structure TorusLinearCoordinates (T : Torus → Torus)
    (L : TorusVector ≃L[ℝ] TorusVector) : Prop where
  projection : ∀ x, T (torusProj x) = torusProj (L x)
  localCoordinates : ∀ p : TorusVector,
    ∃ c d : OpenPartialHomeomorph TorusVector Torus,
      p ∈ c.source ∧ L p ∈ d.source ∧
      (∀ x, c x = torusProj x) ∧ (∀ x, d x = torusProj x) ∧
      (fun x => d.symm (T (c x))) =ᶠ[𝓝 p] L ∧
      AnalyticAt ℝ (fun x => d.symm (T (c x))) p ∧
      HasFDerivAt (fun x => d.symm (T (c x))) (L : TorusVector →L[ℝ] TorusVector) p

theorem torusLinearCoordinates_of_projection (T : Torus → Torus)
    (L : TorusVector ≃L[ℝ] TorusVector)
    (h : ∀ x, T (torusProj x) = torusProj (L x)) : TorusLinearCoordinates T L := by
  refine ⟨h, fun p => ?_⟩
  let c := torusQuotientChart p
  let d := torusQuotientChart (L p)
  have hp : p ∈ c.source := torusQuotientChart_mem_source p
  have hLp : L p ∈ d.source := torusQuotientChart_mem_source (L p)
  have he : (fun x => d.symm (T (c x))) =ᶠ[𝓝 p] L := by
    have hn : ∀ᶠ x in 𝓝 p, L x ∈ d.source :=
      L.continuous.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hLp)
    filter_upwards [hn] with x hx
    rw [show c x = torusProj x from rfl, h,
      show torusProj (L x) = d (L x) from rfl, d.left_inv hx]
  exact ⟨c, d, hp, hLp, fun _ => rfl, fun _ => rfl, he,
    (L.analyticAt p).congr he.symm, L.hasFDerivAt.congr_of_eventuallyEq he⟩

/-- The same quotient-chart derivative certificate applies to every iterate. -/
theorem TorusLinearCoordinates.pow {T : Equiv.Perm Torus}
    {L : TorusVector ≃L[ℝ] TorusVector} (h : TorusLinearCoordinates T L) (n : ℕ) :
    TorusLinearCoordinates (T ^ n : Equiv.Perm Torus) (L ^ n) := by
  apply torusLinearCoordinates_of_projection
  intro x
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change T ((T ^ n) (torusProj x)) = torusProj (L ((L ^ n) x))
    rw [ih, h.projection]

/-- Uniform hyperbolicity on a set in the standard tangent trivialization. The nonzero
vectors `s,u` span complementary constant stable/unstable lines. Derivative estimates hold
at every lift of every point of the set, for every iterate, with constant `C = 1`. -/
def TorusHyperbolicLift (L : TorusVector ≃L[ℝ] TorusVector) (Λ : Set Torus) : Prop :=
  ∃ (s u : TorusVector) (ρ : ℝ),
    s ≠ 0 ∧ u ≠ 0 ∧
    (∀ v : TorusVector, ∃ a b : ℝ, v = a • s + b • u) ∧
    (∀ a b : ℝ, a • s + b • u = 0 → a = 0 ∧ b = 0) ∧
    0 < ρ ∧ ρ < 1 ∧ L s = ρ • s ∧ L.symm u = ρ • u ∧
    ∀ p : TorusVector, torusProj p ∈ Λ → ∀ (n : ℕ) (a : ℝ),
      ‖fderiv ℝ (L ^ n) p (a • s)‖ ≤ ρ ^ n * ‖a • s‖ ∧
      ‖fderiv ℝ (L.symm ^ n) p (a • u)‖ ≤ ρ ^ n * ‖a • u‖

lemma TorusHyperbolicLift.mono {L : TorusVector ≃L[ℝ] TorusVector}
    {Λ Λ' : Set Torus} (h : TorusHyperbolicLift L Λ) (hΛ : Λ' ⊆ Λ) :
    TorusHyperbolicLift L Λ' := by
  obtain ⟨s, u, ρ, hs, hu, hspan, hind, hρ0, hρ1, hLs, hLu, hb⟩ := h
  exact ⟨s, u, ρ, hs, hu, hspan, hind, hρ0, hρ1, hLs, hLu,
    fun p hp => hb p (hΛ hp)⟩

/-- Real-analytic Anosov certificate for a linear torus automorphism. Analyticity and
the derivative are certified in actual quotient charts for both the map and its inverse;
the tangent splitting and contraction estimates are global. -/
def IsAnalyticAnosovTorus (T : Equiv.Perm Torus) : Prop :=
  ∃ L : TorusVector ≃L[ℝ] TorusVector,
    TorusLinearCoordinates T L ∧ TorusLinearCoordinates (T⁻¹ : Equiv.Perm Torus) L.symm ∧
    TorusHyperbolicLift L Set.univ

/-- Uniform hyperbolicity of a set for a linear torus automorphism. -/
def IsUniformlyHyperbolicTorus (T : Equiv.Perm Torus) (Λ : Set Torus) : Prop :=
  ∃ L : TorusVector ≃L[ℝ] TorusVector,
    TorusLinearCoordinates T L ∧ TorusLinearCoordinates (T⁻¹ : Equiv.Perm Torus) L.symm ∧
    TorusHyperbolicLift L Λ

theorem IsAnalyticAnosovTorus.uniformlyHyperbolic {T : Equiv.Perm Torus}
    (h : IsAnalyticAnosovTorus T) (Λ : Set Torus) : IsUniformlyHyperbolicTorus T Λ := by
  obtain ⟨L, hf, hi, hh⟩ := h
  exact ⟨L, hf, hi, hh.mono (Set.subset_univ Λ)⟩

end FiniteOrderMixing
