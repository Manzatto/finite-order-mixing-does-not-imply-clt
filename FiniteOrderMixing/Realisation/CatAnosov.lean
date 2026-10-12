import FiniteOrderMixing.Realisation.CatHorseshoe

/-!
# The square of the cat map is real-analytic and Anosov

The lift is the invertible integer matrix `[[5,3],[3,2]]`. The constant stable and unstable
lines have slopes `(-1-√5)/2` and `(-1+√5)/2`. Its forward derivative contracts the stable
line by `rc`, and its inverse derivative contracts the unstable line by the same factor.
`TorusGeometry` supplies actual quotient charts for the analytic local expressions.
-/

open Filter Topology

namespace FiniteOrderMixing

/-- The invertible linear lift of `A²`, with inverse `[[2,-3],[-3,5]]`. -/
noncomputable def catSqLift : TorusVector ≃L[ℝ] TorusVector :=
  (show TorusVector ≃ₗ[ℝ] TorusVector from
    { toFun := fun x => ![5 * x 0 + 3 * x 1, 3 * x 0 + 2 * x 1]
      invFun := fun x => ![2 * x 0 - 3 * x 1, -3 * x 0 + 5 * x 1]
      left_inv := fun x => by funext i; fin_cases i <;> simp <;> ring
      right_inv := fun x => by funext i; fin_cases i <;> simp <;> ring
      map_add' := fun x y => by funext i; fin_cases i <;> simp <;> ring
      map_smul' := fun a x => by funext i; fin_cases i <;> simp <;> ring }).toContinuousLinearEquiv

lemma catSqLift_projection (x : TorusVector) :
    (catMap ^ 2) (torusProj x) = torusProj (catSqLift x) := catMap_sq_torusProj x

lemma catSqLift_symm_projection (x : TorusVector) :
    (catMap ^ 2 : Equiv.Perm Torus)⁻¹ (torusProj x) = torusProj (catSqLift.symm x) := by
  apply (catMap ^ 2 : Equiv.Perm Torus).injective
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply,
    catSqLift_projection, catSqLift.apply_symm_apply]

noncomputable def catStableVector : TorusVector := ![1, (-1 - s5) / 2]
noncomputable def catUnstableVector : TorusVector := ![1, (-1 + s5) / 2]

lemma catStableVector_ne_zero : catStableVector ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [catStableVector] at this

lemma catUnstableVector_ne_zero : catUnstableVector ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [catUnstableVector] at this

lemma catStableUnstable_span (v : TorusVector) :
    ∃ a b : ℝ, v = a • catStableVector + b • catUnstableVector := by
  have hs5 : s5 ≠ 0 := ne_of_gt (lt_trans (by norm_num) s5_gt)
  let b : ℝ := (v 1 - ((-1 - s5) / 2) * v 0) / s5
  refine ⟨v 0 - b, b, ?_⟩
  funext i
  fin_cases i
  · simp [catStableVector, catUnstableVector]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, catStableVector,
      catUnstableVector]
    dsimp [b]
    field_simp [hs5]
    ring

lemma catStableUnstable_independent (a b : ℝ)
    (h : a • catStableVector + b • catUnstableVector = 0) : a = 0 ∧ b = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [catStableVector, catUnstableVector] at h0 h1
  have hs5 : s5 ≠ 0 := ne_of_gt (lt_trans (by norm_num) s5_gt)
  have ha : a = -b := by linarith
  rw [ha] at h1
  have hb : b * s5 = 0 := by nlinarith only [h1]
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right hs5
  exact ⟨by linarith, hb0⟩

lemma catSqLift_stable : catSqLift catStableVector = rc • catStableVector := by
  funext i
  fin_cases i <;> simp [catSqLift, catStableVector, rc]
  <;> nlinarith [s5_sq]

lemma catSqLift_symm_unstable : catSqLift.symm catUnstableVector = rc • catUnstableVector := by
  funext i
  fin_cases i <;> simp [catSqLift, catUnstableVector, rc]
  <;> nlinarith [s5_sq]

/-- Iterating a linear map on an eigenline gives an exact contraction formula. -/
lemma linearEquiv_pow_eigenline (L : TorusVector ≃L[ℝ] TorusVector)
    {v : TorusVector} {ρ : ℝ} (hv : L v = ρ • v) (n : ℕ) (a : ℝ) :
    (L ^ n) (a • v) = ρ ^ n • (a • v) := by
  induction n with
  | zero =>
    change a • v = (1 : ℝ) • (a • v)
    rw [one_smul]
  | succ n ih =>
    rw [pow_succ']
    change L ((L ^ n) (a • v)) = _
    rw [ih, map_smul, map_smul, hv]
    simp only [smul_smul, pow_succ]
    congr 1
    ring

theorem catSqLift_hyperbolic : TorusHyperbolicLift catSqLift Set.univ := by
  refine ⟨catStableVector, catUnstableVector, rc,
    catStableVector_ne_zero, catUnstableVector_ne_zero,
    catStableUnstable_span, catStableUnstable_independent,
    rc_pos, rc_lt_one, catSqLift_stable, catSqLift_symm_unstable, ?_⟩
  intro p _ n a
  constructor
  · rw [ContinuousLinearEquiv.fderiv]
    change ‖(catSqLift ^ n) (a • catStableVector)‖ ≤ _
    rw [linearEquiv_pow_eigenline catSqLift catSqLift_stable,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg rc_pos.le n)]
  · rw [ContinuousLinearEquiv.fderiv]
    change ‖(catSqLift.symm ^ n) (a • catUnstableVector)‖ ≤ _
    rw [linearEquiv_pow_eigenline catSqLift.symm catSqLift_symm_unstable,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg rc_pos.le n)]

/-- `A²` is a real-analytic Anosov diffeomorphism in the standard quotient charts. -/
theorem catMap_sq_analyticAnosov : IsAnalyticAnosovTorus (catMap ^ 2) :=
  ⟨catSqLift,
    torusLinearCoordinates_of_projection _ _ catSqLift_projection,
    torusLinearCoordinates_of_projection _ _ catSqLift_symm_projection,
    catSqLift_hyperbolic⟩

/-- The explicitly coded horseshoe is uniformly hyperbolic. -/
theorem catCod_uniformlyHyperbolic :
    IsUniformlyHyperbolicTorus (catMap ^ 2) (Set.range catCod) :=
  catMap_sq_analyticAnosov.uniformlyHyperbolic _

end FiniteOrderMixing
