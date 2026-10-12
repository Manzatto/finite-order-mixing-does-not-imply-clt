import FiniteOrderMixing.Realisation.Robust
import FiniteOrderMixing.Realisation.CatAnosov

/-!
# Auxiliary results for the torus realisation

Lipschitz estimates for `C¹` observables, smooth separation of symbol cylinders,
trigonometric approximation, and continuity of the cat map and its iterates.
The main statement and proof are in `FiniteOrderMixing/TheoremA.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace FiniteOrderMixing

/-! ## Functions on the torus -/

lemma exists_rep_norm (a : UnitAddCircle) : ∃ t : ℝ, (t : UnitAddCircle) = a ∧ |t| = ‖a‖ := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
  refine ⟨s - round s, ?_, ?_⟩
  · rw [AddCircle.coe_sub, coe_int_unitAddCircle, sub_zero]
  · change |s - round s| = ‖(s : UnitAddCircle)‖
    rw [AddCircle.norm_eq]; simp

/-- `C¹` observables on the torus are Lipschitz: `|f x - f y| ≤ ‖Df‖_∞ d(x, y)`. -/
lemma C1Bound.lipBound {f : Torus → ℝ} {A : ℝ} (hf : C1Bound f A) : LipBound f A := by
  refine ⟨hf.2.1, fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := torusProj_surjective x
  choose d hd hdn using fun i => exists_rep_norm (y i - torusProj x' i)
  have hy : torusProj (x' + d) = y := by
    funext i
    simp only [torusProj, Pi.add_apply, AddCircle.coe_add, hd]
    exact add_sub_cancel _ _
  have hdiff : ∀ z ∈ (Set.univ : Set (Fin 2 → ℝ)), DifferentiableAt ℝ (torusLift f) z :=
    fun z _ => hf.1.differentiable one_ne_zero z
  have key := convex_univ.norm_image_sub_le_of_norm_fderiv_le hdiff (fun z _ => hf.2.2 z)
    (Set.mem_univ x') (Set.mem_univ (x' + d))
  rw [torusLift_apply, torusLift_apply, hy, add_sub_cancel_left] at key
  have hd_le : ‖d‖ ≤ dist y (torusProj x') := by
    refine (pi_norm_le_iff_of_nonneg dist_nonneg).2 fun i => ?_
    rw [Real.norm_eq_abs, hdn, ← dist_eq_norm]
    exact dist_le_pi_dist _ _ i
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf.2.2 0)
  rw [abs_sub_comm, ← Real.norm_eq_abs, dist_comm]
  exact key.trans (mul_le_mul_of_nonneg_left hd_le hA)

/-- The derivative of the lift of a `C¹` function on the torus is bounded. -/
lemma exists_bound_fderiv_torusLift {f : Torus → ℝ} (hf : ContDiff ℝ 1 (torusLift f)) :
    ∃ B, ∀ x, ‖fderiv ℝ (torusLift f) x‖ ≤ B := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hf.continuous_fderiv one_ne_zero).continuousOn
  have hper : ∀ k : Fin 2 → ℤ, (fun z => torusLift f (z + fun i => (k i : ℝ))) = torusLift f :=
    fun k => funext fun z => by simp only [torusLift_apply, torusProj_add_int]
  have key : ∀ (y : Fin 2 → ℝ) (k : Fin 2 → ℤ),
      fderiv ℝ (torusLift f) (y + fun i => (k i : ℝ)) = fderiv ℝ (torusLift f) y := fun y k => by
    rw [← fderiv_comp_add_right, hper]
  refine ⟨B, fun x => ?_⟩
  have hx : x = (fun i => Int.fract (x i)) + fun i => ((⌊x i⌋ : ℤ) : ℝ) := by
    funext i; simp [Int.fract_add_floor]
  rw [hx, key]
  exact hB _ fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

lemma exists_C1Bound {f : Torus → ℝ} (hf : ContDiff ℝ 1 (torusLift f)) {B₀ : ℝ}
    (hb : ∀ x, |f x| ≤ B₀) : ∃ A, C1Bound f A := by
  obtain ⟨B, hB⟩ := exists_bound_fderiv_torusLift hf
  exact ⟨max B₀ B, hf, fun x => (hb x).trans (le_max_left _ _),
    fun x => (hB x).trans (le_max_right _ _)⟩

/-! ## Trigonometric polynomials -/

lemma mFourier_torusProj (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    UnitAddTorus.mFourier k (torusProj x) =
      ∏ i, Complex.exp (2 * Real.pi * Complex.I * (k i) * (x i)) := by
  simp [UnitAddTorus.mFourier, torusProj]

lemma contDiff_mFourier_torusProj (k : Fin 2 → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => UnitAddTorus.mFourier k (torusProj x) := by
  simp_rw [mFourier_torusProj]
  refine contDiff_prod fun i _ => ?_
  have hlin : ContDiff ℝ (⊤ : ℕ∞) fun x : Fin 2 → ℝ => ((x i : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)
  exact Complex.contDiff_exp.comp (contDiff_const.mul hlin)

lemma contDiff_trig (s : Finset (Fin 2 → ℤ)) (c : (Fin 2 → ℤ) → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x =>
      (∑ k ∈ s, c k * UnitAddTorus.mFourier k (torusProj x)).re :=
  Complex.reCLM.contDiff.comp (ContDiff.sum fun k _ =>
    contDiff_const.mul (contDiff_mFourier_torusProj k))

/-! ## Approximation by trigonometric polynomials -/

lemma isRealTrigPoly_of_mem {Q : C(Torus, ℂ)} (hQ : Q ∈ UnitAddTorus.mFourierSubalgebra (Fin 2)) :
    IsRealTrigPoly fun x => (Q x).re := by
  classical
  have hQ' : Q ∈ (UnitAddTorus.mFourierSubalgebra (Fin 2)).toSubalgebra.toSubmodule := hQ
  rw [UnitAddTorus.mFourierSubalgebra_coe] at hQ'
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hQ'
  exact ⟨c.support, c, fun x => by simp [Finsupp.sum, ContinuousMap.coe_sum, smul_eq_mul]⟩

lemma exists_antideriv (p : Polynomial ℝ) : ∃ q : Polynomial ℝ, Polynomial.derivative q = p := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1),
    Polynomial.C (p.coeff i / (i + 1)) * Polynomial.X ^ (i + 1), ?_⟩
  rw [Polynomial.derivative_sum]
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.derivative_C_mul_X_pow, Nat.add_sub_cancel]
  congr 2
  push_cast
  field_simp

/-- If `P` is a complex trigonometric polynomial with `C¹` real part bounded by `M`, and
`ψ ∈ C¹(ℝ)`, then `ψ ∘ Re P` is `C¹`-approximated by the real trigonometric polynomials
`q ∘ Re P`, `q` a polynomial approximating `ψ` in `C¹([-M, M])`. -/
theorem exists_trig_near_comp {P : C(Torus, ℂ)} (hP : P ∈ UnitAddTorus.mFourierSubalgebra (Fin 2))
    (hP1 : ContDiff ℝ 1 (torusLift fun x => (P x).re)) {M : ℝ} (hM : 0 ≤ M)
    (hPM : ∀ x, |(P x).re| ≤ M) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : Torus → ℝ, IsRealTrigPoly g ∧ C1Bound (g - fun x => ψ (P x).re) δ := by
  classical
  set Pr : Torus → ℝ := fun x => (P x).re
  set F := torusLift Pr
  obtain ⟨B, hB⟩ := exists_bound_fderiv_torusLift hP1
  set B' := max B 0 + 1
  have hB' : 0 < B' := by positivity
  set η := min (δ / (2 * M + 1)) (δ / B')
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hψd : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-M) M (deriv ψ) hψd.continuousOn η hη
  obtain ⟨q₀, hq₀⟩ := exists_antideriv p
  set q := q₀ + Polynomial.C (ψ (-M) - q₀.eval (-M))
  have hqd : Polynomial.derivative q = p := by simp [q, hq₀]
  have hq_m : q.eval (-M) = ψ (-M) := by simp [q]
  set h : ℝ → ℝ := fun t => q.eval t - ψ t
  have hhd : ∀ t, HasDerivAt h (p.eval t - deriv ψ t) t := fun t => by
    have := (q.hasDerivAt t).sub ((hψ.differentiable one_ne_zero) t).hasDerivAt
    rwa [hqd] at this
  have hhdiff : ∀ t ∈ Set.Icc (-M) M, |p.eval t - deriv ψ t| ≤ η := fun t ht => (hp t ht).le
  have hval : ∀ t ∈ Set.Icc (-M) M, |h t| ≤ δ := by
    intro t ht
    have hmvt := (convex_Icc (-M) M).norm_image_sub_le_of_norm_deriv_le (f := h)
      (fun x _ => (hhd x).differentiableAt)
      (fun x hx => by rw [(hhd x).deriv, Real.norm_eq_abs]; exact hhdiff x hx)
      (Set.left_mem_Icc.2 (by linarith)) ht
    have h0 : h (-M) = 0 := by simp [h, hq_m]
    rw [h0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    have hη1 : η * (2 * M + 1) ≤ δ := by
      have := min_le_left (δ / (2 * M + 1)) (δ / B')
      calc η * (2 * M + 1) ≤ δ / (2 * M + 1) * (2 * M + 1) := by gcongr
        _ = δ := by field_simp
    obtain ⟨ht1, ht2⟩ := ht
    have habs : |t - -M| ≤ 2 * M + 1 := by rw [abs_le]; constructor <;> linarith
    calc |h t| ≤ η * |t - -M| := hmvt
      _ ≤ η * (2 * M + 1) := mul_le_mul_of_nonneg_left habs hη.le
      _ ≤ δ := hη1
  have hFM : ∀ x, F x ∈ Set.Icc (-M) M := fun x => by
    have := abs_le.1 (hPM (torusProj x))
    show (P (torusProj x)).re ∈ Set.Icc (-M) M
    exact ⟨this.1, this.2⟩
  refine ⟨fun x => q.eval (Pr x), ?_, ?_⟩
  · -- `q ∘ Re P` is a trigonometric polynomial
    set R : C(Torus, ℂ) := (1 / 2 : ℂ) • (P + star P)
    have hR : R ∈ UnitAddTorus.mFourierSubalgebra (Fin 2) :=
      SMulMemClass.smul_mem _ (add_mem hP (star_mem hP))
    have hRx : ∀ x, R x = ((Pr x : ℝ) : ℂ) := fun x => by
      simp only [R, Pr, ContinuousMap.smul_apply, ContinuousMap.add_apply,
        ContinuousMap.star_apply, smul_eq_mul, Complex.re_eq_add_conj]
      simp only [Complex.star_def]
      ring
    set Q : C(Torus, ℂ) := ∑ i ∈ Finset.range (q.natDegree + 1), ((q.coeff i : ℝ) : ℂ) • R ^ i
    have hQ : Q ∈ UnitAddTorus.mFourierSubalgebra (Fin 2) :=
      sum_mem fun i _ => SMulMemClass.smul_mem _ (pow_mem hR i)
    have hQx : ∀ x, Q x = ((q.eval (Pr x) : ℝ) : ℂ) := fun x => by
      rw [Polynomial.eval_eq_sum_range]
      simp only [Q, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
        Pi.smul_apply, ContinuousMap.coe_pow, Pi.pow_apply, hRx, smul_eq_mul]
      push_cast
      rfl
    have e : (fun x => q.eval (Pr x)) = fun x => (Q x).re :=
      funext fun x => by rw [hQx, Complex.ofReal_re]
    rw [e]
    exact isRealTrigPoly_of_mem hQ
  · -- the `C¹` bound
    have hlift : torusLift ((fun x => q.eval (Pr x)) - fun x => ψ (Pr x)) = h ∘ F := by
      funext x; rfl
    refine ⟨?_, fun x => hval _ ⟨by linarith [(abs_le.1 (hPM x)).1], (abs_le.1 (hPM x)).2⟩,
      fun x => ?_⟩
    · have hqc : ContDiff ℝ 1 fun t : ℝ => q.eval t := by
        simpa [Polynomial.coe_aeval_eq_eval] using q.contDiff_aeval (𝕜 := ℝ) 1
      rw [hlift]; exact (hqc.sub hψ).comp hP1
    · rw [hlift]
      have hFd := (hP1.differentiable one_ne_zero x).hasFDerivAt
      rw [((hhd (F x)).comp_hasFDerivAt x hFd).fderiv, norm_smul, Real.norm_eq_abs]
      have hη2 : η * B' ≤ δ := by
        have := min_le_right (δ / (2 * M + 1)) (δ / B')
        calc η * B' ≤ δ / B' * B' := by gcongr
          _ = δ := by field_simp
      calc |p.eval (F x) - deriv ψ (F x)| * ‖fderiv ℝ F x‖ ≤ η * B' :=
            mul_le_mul (hhdiff _ (hFM x)) ((hB x).trans (by simp only [B']; linarith [le_max_left B 0]))
              (norm_nonneg _) hη.le
        _ ≤ δ := hη2

/-! ## The observable `f₀` -/

/-- A smooth observable on the torus equal to `Z₀` along a coding: `f₀ ∘ cod = Z₀`, with
`|f₀| ≤ 1`, which is a `C¹`-limit of real trigonometric polynomials. -/
theorem exists_smooth_sign {cod : Config → Torus} (hcod : Continuous cod)
    (hinj : Function.Injective cod) :
    ∃ f₀ : Torus → ℝ, ContDiff ℝ (⊤ : ℕ∞) (torusLift f₀) ∧ Continuous f₀ ∧
      (∀ x, |f₀ x| ≤ 1) ∧ (∀ ω, f₀ (cod ω) = Z 0 ω) ∧
      ∀ δ > (0 : ℝ), ∃ g : Torus → ℝ, IsRealTrigPoly g ∧ C1Bound (g - f₀) δ := by
  classical
  -- the two symbol cylinders
  have hcl : ∀ b : Bool, IsClosed (cod '' {ω : Config | ω 0 = b}) := fun b =>
    ((isClosed_eq (continuous_apply 0) continuous_const).isCompact.image hcod).isClosed
  have hdisj : Disjoint (cod '' {ω : Config | ω 0 = false}) (cod '' {ω : Config | ω 0 = true}) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨ω, hω, rfl⟩ ⟨ω', hω', e⟩
    have := hinj e
    subst this
    simp_all
  obtain ⟨u, hu0, hu1, hu01⟩ := exists_continuous_zero_one_of_isClosed (hcl false) (hcl true) hdisj
  -- a trigonometric approximation of `2u - 1`
  set U : C(Torus, ℂ) := ⟨fun x => ((2 * u x - 1 : ℝ) : ℂ), by fun_prop⟩
  have hU : U ∈ (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin 2)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]; exact Submodule.mem_top
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hU
  obtain ⟨P, hP, hPU⟩ := Metric.mem_closure_iff.1 hU (1 / 4) (by norm_num)
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hP
  set P : C(Torus, ℂ) := c.sum fun k a => a • UnitAddTorus.mFourier k
  have hPx : ∀ x, P x = ∑ k ∈ c.support, c k * UnitAddTorus.mFourier k x := fun x => by
    simp [P, Finsupp.sum, ContinuousMap.coe_sum, smul_eq_mul]
  set Pr : Torus → ℝ := fun x => (P x).re
  have hPr : ∀ x, |Pr x - (2 * u x - 1)| < 1 / 4 := fun x => by
    have h1 := (ContinuousMap.dist_apply_le_dist x).trans_lt hPU
    rw [dist_comm, Complex.dist_eq] at h1
    refine lt_of_le_of_lt ?_ h1
    have : Pr x - (2 * u x - 1) = (P x - U x).re := by simp [Pr, U]
    rw [this]
    exact Complex.abs_re_le_norm _
  have hPS : P ∈ UnitAddTorus.mFourierSubalgebra (Fin 2) := by
    have : P ∈ (UnitAddTorus.mFourierSubalgebra (Fin 2)).toSubalgebra.toSubmodule := by
      rw [UnitAddTorus.mFourierSubalgebra_coe]; exact hP
    exact this
  have hP1 : ContDiff ℝ 1 (torusLift fun x => (P x).re) := by
    have : torusLift (fun x => (P x).re) = fun x =>
        (∑ k ∈ c.support, c k * UnitAddTorus.mFourier k (torusProj x)).re := by
      funext x; simp only [torusLift_apply, hPx]
    rw [this]; exact (contDiff_trig _ _).of_le (by exact_mod_cast le_top)
  have hPM : ∀ x, |(P x).re| ≤ 2 := fun x => by
    have h1 := hPr x
    have h2 := hu01 x
    rw [abs_lt] at h1
    rw [abs_le]; constructor <;> simp only [Pr] at h1 <;> linarith [h2.1, h2.2]
  set ψ : ℝ → ℝ := fun t => 2 * Real.smoothTransition (t + 1 / 2) - 1
  have hψ : ContDiff ℝ 1 ψ :=
    ((contDiff_const.mul (Real.smoothTransition.contDiff.comp
      (contDiff_id.add contDiff_const))).sub contDiff_const).of_le (by exact_mod_cast le_top)
  set f₀ : Torus → ℝ := fun x => 2 * Real.smoothTransition (Pr x + 1 / 2) - 1
  refine ⟨f₀, ?_, ?_, fun x => ?_, fun ω => ?_, fun δ hδ => ?_⟩
  · have hlift : torusLift f₀ = fun x => 2 * Real.smoothTransition
        ((∑ k ∈ c.support, c k * UnitAddTorus.mFourier k (torusProj x)).re + 1 / 2) - 1 := by
      funext x; simp only [torusLift_apply, f₀, Pr, hPx]
    rw [hlift]
    exact (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      ((contDiff_trig _ _).add contDiff_const))).sub contDiff_const
  · have : Continuous Pr := Complex.continuous_re.comp P.continuous
    fun_prop
  · have h0 := Real.smoothTransition.nonneg (Pr x + 1 / 2)
    have h1 := Real.smoothTransition.le_one (Pr x + 1 / 2)
    rw [abs_le]; constructor <;> simp only [f₀] <;> linarith
  · cases hω : ω 0
    · have hu : u (cod ω) = 0 := hu0 ⟨ω, hω, rfl⟩
      have := hPr (cod ω)
      rw [hu, abs_lt] at this
      simp only [f₀, Z, hω, spin_false]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
      norm_num
    · have hu : u (cod ω) = 1 := hu1 ⟨ω, hω, rfl⟩
      have := hPr (cod ω)
      rw [hu, abs_lt] at this
      simp only [f₀, Z, hω, spin_true]
      rw [Real.smoothTransition.one_of_one_le (by linarith)]
      norm_num
  · exact exists_trig_near_comp hPS hP1 (by norm_num) hPM hψ hδ

/-! ## The cat map -/

lemma continuous_catMap : Continuous ⇑catMap := by
  refine continuous_pi fun i => ?_
  simp only [catMap, Equiv.coe_fn_mk]
  fin_cases i <;> simp <;> fun_prop

lemma continuous_catMap_inv : Continuous ⇑catMap⁻¹ := by
  refine continuous_pi fun i => ?_
  simp only [catMap, Equiv.Perm.inv_def, Equiv.coe_fn_symm_mk]
  fin_cases i <;> simp <;> fun_prop

lemma continuous_catMap_pow (k : ℕ) : Continuous ⇑(catMap ^ k) := by
  rw [Equiv.Perm.coe_pow]; exact continuous_catMap.iterate k

lemma continuous_catMap_pow_inv (k : ℕ) : Continuous ⇑(catMap ^ k)⁻¹ := by
  rw [← inv_pow, Equiv.Perm.coe_pow]; exact continuous_catMap_inv.iterate k

end FiniteOrderMixing
