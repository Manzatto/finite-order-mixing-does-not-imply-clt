import FiniteOrderMixing.Realisation.Defs

/-!
# A two-symbol horseshoe for the square of the cat map (Lemma `lem:fixed-horseshoe`)

For the linear map `A = [[2,1],[1,1]]`, the horseshoe of `T = A²` is given by an explicit
arithmetic coding.  Let `Λ = (7 + 3√5)/2` and `r = Λ⁻¹ = (7 - 3√5)/2` be the eigenvalues of `A²`,
with eigenvectors `U = ((5+√5)/10, √5/5)` and `S = ((5-√5)/10, -√5/5)`, so that `U + S = e₁`.
For `ω ∈ Σ` put

  `a(ω) = Σ_{n ≥ 0} [ω_n] r^{n+1}`,  `b(ω) = Σ_{m ≥ 0} [ω_{-m-1}] r^m`,
  `cod(ω) = a(ω) U - b(ω) S  (mod ℤ²)`.

Then `a(σω) = Λ a(ω) - [ω₀]` and `b(σω) = [ω₀] + r b(ω)`, hence
`A² (a U - b S) = cod(σω) + [ω₀] e₁`, which is the conjugacy `cod ∘ σ = T ∘ cod`.  Cylinders on
`[-ℓ, ℓ]` have images of diameter `≲ r^ℓ`.  Injectivity: a lattice point `a U - b S` with `a, b`
in the ranges of the digit series must vanish, and the expansions in base `Λ > 2` are unique.

This replaces the appeal to Smale's homoclinic horseshoe theorem and to the regularity of
hyperbolic coding (Theorems `thm:homoclinic-horseshoe`, `thm:hyperbolic-coding`) for Theorem A.
-/

open Filter Topology

namespace FiniteOrderMixing

/-! ## The torus projection -/

lemma torusLift_apply (f : Torus → ℝ) (x : Fin 2 → ℝ) : torusLift f x = f (torusProj x) := rfl

lemma torusProj_surjective : Function.Surjective torusProj := fun y => by
  choose x hx using fun i => QuotientAddGroup.mk_surjective (y i)
  exact ⟨x, funext hx⟩

lemma coe_int_unitAddCircle (k : ℤ) : ((k : ℝ) : UnitAddCircle) = 0 :=
  (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2 ⟨k, by simp⟩

lemma torusProj_add_int (x : Fin 2 → ℝ) (k : Fin 2 → ℤ) :
    torusProj (x + fun i => (k i : ℝ)) = torusProj x := by
  funext i
  simp only [torusProj, Pi.add_apply, AddCircle.coe_add, coe_int_unitAddCircle, add_zero]

lemma continuous_torusProj : Continuous torusProj :=
  continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)

lemma norm_coe_unitAddCircle_le (x : ℝ) : ‖(x : UnitAddCircle)‖ ≤ |x| := by
  by_cases h : |x| ≤ 1 / 2
  · exact le_of_eq ((AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by simpa using h))
  · push Not at h
    exact (AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero).trans (by simp; linarith)

lemma dist_torusProj_le {x y : Fin 2 → ℝ} {C : ℝ} (hC : ∀ i, |x i - y i| ≤ C) :
    dist (torusProj x) (torusProj y) ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine (dist_pi_le_iff hC0).2 fun i => ?_
  simp only [torusProj]
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact (norm_coe_unitAddCircle_le _).trans (hC i)

lemma eq_int_of_torusProj_eq {x y : Fin 2 → ℝ} (h : torusProj x = torusProj y) (i : Fin 2) :
    ∃ k : ℤ, (k : ℝ) = x i - y i := by
  have hi := congrFun h i
  simp only [torusProj] at hi
  have : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by rw [AddCircle.coe_sub, hi, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 this
  exact ⟨k, by simpa using hk⟩

lemma catMap_torusProj (x : Fin 2 → ℝ) :
    catMap (torusProj x) = torusProj ![2 * x 0 + x 1, x 0 + x 1] := by
  funext i
  fin_cases i <;> simp [catMap, torusProj, two_mul, two_nsmul]

lemma catMap_sq_torusProj (x : Fin 2 → ℝ) :
    (catMap ^ 2) (torusProj x) = torusProj ![5 * x 0 + 3 * x 1, 3 * x 0 + 2 * x 1] := by
  rw [pow_two, Equiv.Perm.mul_apply, catMap_torusProj, catMap_torusProj]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

/-! ## Digit series -/

/-- `[b] ∈ {0, 1}`. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

lemma bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> simp [bit]

lemma bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp [bit]

lemma abs_bit_sub_le (b c : Bool) : |bit b - bit c| ≤ 1 := by
  cases b <;> cases c <;> simp [bit]

lemma abs_bit_sub_eq_one {b c : Bool} (h : b ≠ c) : |bit b - bit c| = 1 := by
  cases b <;> cases c <;> simp_all [bit]

section Series

variable {r : ℝ}

lemma summable_of_abs_le_geom (hr0 : 0 ≤ r) (hr1 : r < 1) {d : ℕ → ℝ}
    (hd : ∀ n, |d n| ≤ r ^ n) : Summable d :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one hr0 hr1) fun n => by
    rw [Real.norm_eq_abs]; exact hd n

lemma abs_tsum_shift_le (hr0 : 0 ≤ r) (hr1 : r < 1) {d : ℕ → ℝ} (hd : ∀ n, |d n| ≤ r ^ n)
    (k : ℕ) : |∑' i, d (i + k)| ≤ r ^ k / (1 - r) := by
  have hg : Summable fun i => r ^ (i + k) := by
    simp_rw [pow_add]; exact (summable_geometric_of_lt_one hr0 hr1).mul_right _
  have hds : Summable fun i => d (i + k) :=
    summable_of_abs_le_geom hr0 hr1 fun n => (hd (n + k)).trans
      (pow_le_pow_of_le_one hr0 hr1.le (by omega))
  have hsum : ∑' i, r ^ (i + k) = r ^ k / (1 - r) := by
    simp_rw [pow_add]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv, mul_comm]
  rw [← hsum, abs_le]
  constructor
  · rw [← tsum_neg]
    exact hg.neg.tsum_le_tsum (fun i => neg_le_of_abs_le (hd (i + k))) hds
  · exact hds.tsum_le_tsum (fun i => le_of_abs_le (hd (i + k))) hg

/-- The digit series `Σ_n [f n] r^n`. -/
noncomputable def dser (r : ℝ) (f : ℕ → Bool) : ℝ := ∑' n, bit (f n) * r ^ n

lemma abs_bit_mul_pow_le (hr0 : 0 ≤ r) (b : Bool) (n : ℕ) : |bit b * r ^ n| ≤ r ^ n := by
  rw [abs_mul, abs_of_nonneg (bit_nonneg b), abs_of_nonneg (pow_nonneg hr0 n)]
  exact mul_le_of_le_one_left (pow_nonneg hr0 n) (bit_le_one b)

lemma summable_dser (hr0 : 0 ≤ r) (hr1 : r < 1) (f : ℕ → Bool) :
    Summable fun n => bit (f n) * r ^ n :=
  summable_of_abs_le_geom hr0 hr1 fun n => abs_bit_mul_pow_le hr0 _ n

lemma dser_succ (hr0 : 0 ≤ r) (hr1 : r < 1) (f : ℕ → Bool) :
    dser r f = bit (f 0) + r * dser r (fun n => f (n + 1)) := by
  unfold dser
  rw [(summable_dser hr0 hr1 f).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, mul_one, pow_succ]
  congr 1
  exact tsum_congr fun n => by ring

lemma abs_dser_sub_le (hr0 : 0 ≤ r) (hr1 : r < 1) {f g : ℕ → Bool} {N : ℕ}
    (h : ∀ n < N, f n = g n) : |dser r f - dser r g| ≤ r ^ N / (1 - r) := by
  set d : ℕ → ℝ := fun n => (bit (f n) - bit (g n)) * r ^ n
  have hd : ∀ n, |d n| ≤ r ^ n := fun n => by
    simp only [d, abs_mul, abs_of_nonneg (pow_nonneg hr0 n)]
    exact mul_le_of_le_one_left (pow_nonneg hr0 n) (abs_bit_sub_le _ _)
  have hds := summable_of_abs_le_geom hr0 hr1 hd
  have heq : dser r f - dser r g = ∑' n, d n := by
    unfold dser
    rw [← (summable_dser hr0 hr1 f).tsum_sub (summable_dser hr0 hr1 g)]
    exact tsum_congr fun n => by simp only [d]; ring
  rw [heq, ← hds.sum_add_tsum_nat_add N,
    Finset.sum_eq_zero fun n hn => by simp [d, h n (Finset.mem_range.1 hn)], zero_add]
  exact abs_tsum_shift_le hr0 hr1 hd N

lemma abs_dser_le (hr0 : 0 ≤ r) (hr1 : r < 1) (f : ℕ → Bool) : |dser r f| ≤ 1 / (1 - r) := by
  have h0 : dser r (fun _ => false) = 0 := by simp [dser, bit]
  have := abs_dser_sub_le hr0 hr1 (f := f) (g := fun _ => false) (N := 0) (by simp)
  rwa [h0, sub_zero, pow_zero] at this

/-- Expansions in base `r⁻¹ > 2` with digits `0, 1` are unique. -/
lemma dser_injective (hr0 : 0 < r) (hr2 : r < 1 / 2) {f g : ℕ → Bool}
    (h : dser r f = dser r g) : f = g := by
  have hr1 : r < 1 := by linarith
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_contra hne
  set d : ℕ → ℝ := fun n => (bit (f n) - bit (g n)) * r ^ n
  have hd : ∀ n, |d n| ≤ r ^ n := fun n => by
    simp only [d, abs_mul, abs_of_nonneg (pow_nonneg hr0.le n)]
    exact mul_le_of_le_one_left (pow_nonneg hr0.le n) (abs_bit_sub_le _ _)
  have hds := summable_of_abs_le_geom hr0.le hr1 hd
  have heq : dser r f - dser r g = ∑' n, d n := by
    unfold dser
    rw [← (summable_dser hr0.le hr1 f).tsum_sub (summable_dser hr0.le hr1 g)]
    exact tsum_congr fun n => by simp only [d]; ring
  have hshift : Summable fun i => d (i + n) :=
    summable_of_abs_le_geom hr0.le hr1 fun i => (hd (i + n)).trans
      (pow_le_pow_of_le_one hr0.le hr1.le (by omega))
  have hsplit : ∑' i, d i = d n + ∑' i, d (i + (n + 1)) := by
    rw [← hds.sum_add_tsum_nat_add n,
      Finset.sum_eq_zero fun i hi => by simp [d, ih i (Finset.mem_range.1 hi)], zero_add,
      hshift.tsum_eq_zero_add]
    simp only [zero_add]
    congr 1
    exact tsum_congr fun i => by congr 1; ring
  have htail := abs_tsum_shift_le hr0.le hr1 hd (n + 1)
  have hdn : |d n| = r ^ n := by
    simp only [d, abs_mul, abs_bit_sub_eq_one hne, one_mul, abs_of_nonneg (pow_nonneg hr0.le n)]
  rw [h, sub_self, hsplit] at heq
  have hlt : r ^ (n + 1) / (1 - r) < r ^ n := by
    rw [div_lt_iff₀ (by linarith), pow_succ]
    have := pow_pos hr0 n
    nlinarith
  have : |d n| ≤ |∑' i, d (i + (n + 1))| := by
    rw [show d n = -∑' i, d (i + (n + 1)) by linarith, abs_neg]
  linarith

lemma continuous_dser (hr0 : 0 ≤ r) (hr1 : r < 1) {X : Type*} [TopologicalSpace X]
    {F : X → ℕ → Bool} (hF : ∀ n, Continuous fun x => F x n) :
    Continuous fun x => dser r (F x) :=
  continuous_tsum (fun n => ((continuous_of_discreteTopology (f := bit)).comp (hF n)).mul
      continuous_const)
    (summable_geometric_of_lt_one hr0 hr1) fun n x => by
      rw [Real.norm_eq_abs]; exact abs_bit_mul_pow_le hr0 _ n

end Series

/-! ## The constants -/

/-- `√5`. -/
noncomputable def s5 : ℝ := Real.sqrt 5

lemma s5_sq : s5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma s5_gt : 2 < s5 := by
  rw [s5, show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma s5_lt : s5 < 9 / 4 := by
  nlinarith [s5_sq, s5_gt]

/-- The contracting eigenvalue `r = (7 - 3√5)/2` of `A²`. -/
noncomputable def rc : ℝ := (7 - 3 * s5) / 2

/-- The expanding eigenvalue `Λ = (7 + 3√5)/2` of `A²`. -/
noncomputable def Lc : ℝ := (7 + 3 * s5) / 2

lemma rc_pos : 0 < rc := by unfold rc; nlinarith [s5_lt]
lemma rc_lt_half : rc < 1 / 2 := by unfold rc; nlinarith [s5_gt]
lemma rc_lt_one : rc < 1 := by linarith [rc_lt_half]
lemma Lc_mul_rc : Lc * rc = 1 := by unfold Lc rc; linear_combination (-9 / 4) * s5_sq

/-! ## The coding -/

/-- `a(ω) = Σ_{n ≥ 0} [ω_n] r^{n+1}`. -/
noncomputable def ca (ω : Config) : ℝ := rc * dser rc fun n => ω n

/-- `b(ω) = Σ_{m ≥ 0} [ω_{-m-1}] r^m`. -/
noncomputable def cb (ω : Config) : ℝ := dser rc fun m => ω (-(m : ℤ) - 1)

/-- The lift `a(ω) U - b(ω) S ∈ ℝ²` of the coding. -/
noncomputable def cx (ω : Config) : Fin 2 → ℝ :=
  ![ca ω * ((5 + s5) / 10) - cb ω * ((5 - s5) / 10), ca ω * (s5 / 5) - cb ω * (-s5 / 5)]

/-- The horseshoe coding of `A²`. -/
noncomputable def catCod (ω : Config) : Torus := torusProj (cx ω)

lemma ca_shift (ω : Config) : ca (shift ω) = Lc * ca ω - bit (ω 0) := by
  have h := dser_succ rc_pos.le rc_lt_one fun n => ω n
  have e : (fun n : ℕ => (shift ω) n) = fun n : ℕ => ω ((n + 1 : ℕ) : ℤ) := by
    funext n; simp [shift]
  simp only [ca]
  rw [e, ← mul_assoc, Lc_mul_rc, one_mul, h]
  simp

lemma cb_shift (ω : Config) : cb (shift ω) = bit (ω 0) + rc * cb ω := by
  have h := dser_succ rc_pos.le rc_lt_one fun m => ω (-(m : ℤ))
  have e : (fun m : ℕ => (shift ω) (-(m : ℤ) - 1)) = fun m : ℕ => ω (-(m : ℤ)) := by
    funext m; simp [shift]
  have e2 : (fun n : ℕ => ω (-((n + 1 : ℕ) : ℤ))) = fun m : ℕ => ω (-(m : ℤ) - 1) :=
    funext fun m => by congr 1; push_cast; ring
  simp only [cb]
  rw [e, h, e2]
  simp

lemma catCod_conj (ω : Config) : catCod (shift ω) = (catMap ^ 2) (catCod ω) := by
  have ha := ca_shift ω
  have hb := cb_shift ω
  have hs := s5_sq
  set k : Fin 2 → ℤ := ![if ω 0 then 1 else 0, 0]
  have hk : bit (ω 0) = ((k 0 : ℤ) : ℝ) := by cases h : ω 0 <;> simp [k, bit, h]
  rw [catCod, catCod, catMap_sq_torusProj, ← torusProj_add_int (cx (shift ω)) k]
  congr 1
  funext i
  fin_cases i
  · simp only [cx, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply]
    rw [← hk, ha, hb]
    simp only [Lc, rc]
    linear_combination (3 / 20) * (ca ω - cb ω) * hs
  · simp only [cx, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.add_apply]
    have hk1 : ((k 1 : ℤ) : ℝ) = 0 := by simp [k]
    rw [hk1, ha, hb]
    simp only [Lc, rc]
    linear_combination (3 / 10) * (ca ω - cb ω) * hs

lemma continuous_catCod : Continuous catCod := by
  have h1 : Continuous ca :=
    continuous_const.mul (continuous_dser rc_pos.le rc_lt_one fun n => continuous_apply _)
  have h2 : Continuous cb := continuous_dser rc_pos.le rc_lt_one fun n => continuous_apply _
  refine continuous_torusProj.comp (continuous_pi fun i => ?_)
  fin_cases i
  · simp only [cx, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; fun_prop
  · simp only [cx, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]; fun_prop

lemma abs_ca_sub_le {ω ω' : Config} {N : ℕ} (h : ∀ n < N, ω n = ω' n) :
    |ca ω - ca ω'| ≤ rc * (rc ^ N / (1 - rc)) := by
  rw [ca, ca, ← mul_sub, abs_mul, abs_of_pos rc_pos]
  exact mul_le_mul_of_nonneg_left (abs_dser_sub_le rc_pos.le rc_lt_one h) rc_pos.le

lemma abs_cb_sub_le {ω ω' : Config} {N : ℕ} (h : ∀ m < N, ω (-(m : ℤ) - 1) = ω' (-(m : ℤ) - 1)) :
    |cb ω - cb ω'| ≤ rc ^ N / (1 - rc) :=
  abs_dser_sub_le rc_pos.le rc_lt_one h

lemma catCod_injective : Function.Injective catCod := by
  intro ω ω' h
  obtain ⟨p, hp⟩ := eq_int_of_torusProj_eq h 0
  obtain ⟨q, hq⟩ := eq_int_of_torusProj_eq h 1
  simp only [cx, Matrix.cons_val_zero, Matrix.cons_val_one] at hp hq
  have hs := s5_sq
  have hs2 := s5_gt
  have hr0 := rc_pos
  have hr2 := rc_lt_half
  set Δa := ca ω - ca ω'
  set Δb := cb ω - cb ω'
  have hΔa : |Δa| ≤ rc * (1 / (1 - rc)) := by
    simpa using abs_ca_sub_le (ω := ω) (ω' := ω') (N := 0) (by simp)
  have hΔb : |Δb| ≤ 1 / (1 - rc) := by
    simpa using abs_cb_sub_le (ω := ω) (ω' := ω') (N := 0) (by simp)
  have h1r : 0 < 1 - rc := by linarith
  -- the second coordinate: `q = (√5/5)(Δa + Δb)`
  have hq' : (q : ℝ) = s5 / 5 * (Δa + Δb) := by rw [hq]; simp only [Δa, Δb]; ring
  have hqlt : |(q : ℝ)| < 1 := by
    rw [hq', abs_mul, abs_of_pos (by positivity)]
    have hsum : |Δa + Δb| ≤ (rc + 1) / (1 - rc) := by
      calc |Δa + Δb| ≤ |Δa| + |Δb| := abs_add_le _ _
        _ ≤ rc * (1 / (1 - rc)) + 1 / (1 - rc) := add_le_add hΔa hΔb
        _ = (rc + 1) / (1 - rc) := by ring
    calc s5 / 5 * |Δa + Δb| ≤ s5 / 5 * ((rc + 1) / (1 - rc)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ < 1 := by
          rw [mul_div_assoc', div_lt_one (by positivity)]
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by norm_num)]
          simp only [rc]
          nlinarith
  have hq0 : q = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast hqlt)
  have hab : Δb = -Δa := by
    rw [hq0, Int.cast_zero] at hq'
    have : s5 / 5 ≠ 0 := by positivity
    have := (mul_eq_zero.1 hq'.symm).resolve_left this
    linarith
  -- the first coordinate: `p = Δa`
  have hp' : (p : ℝ) = Δa := by
    rw [hp]
    have : ca ω * ((5 + s5) / 10) - cb ω * ((5 - s5) / 10) -
        (ca ω' * ((5 + s5) / 10) - cb ω' * ((5 - s5) / 10)) =
        Δa * ((5 + s5) / 10) - Δb * ((5 - s5) / 10) := by simp only [Δa, Δb]; ring
    rw [this, hab]; ring
  have hplt : |(p : ℝ)| < 1 := by
    rw [hp']
    refine hΔa.trans_lt ?_
    rw [mul_one_div, div_lt_one h1r]; linarith
  have hp0 : p = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast hplt)
  have hΔa0 : Δa = 0 := by rw [← hp', hp0, Int.cast_zero]
  have hΔb0 : Δb = 0 := by rw [hab, hΔa0, neg_zero]
  -- uniqueness of the digit expansions
  have hpos : (fun n : ℕ => ω n) = fun n : ℕ => ω' n := by
    apply dser_injective rc_pos rc_lt_half
    have : ca ω = ca ω' := by simp only [Δa] at hΔa0; linarith
    simp only [ca] at this
    exact mul_left_cancel₀ rc_pos.ne' this
  have hneg : (fun m : ℕ => ω (-(m : ℤ) - 1)) = fun m : ℕ => ω' (-(m : ℤ) - 1) := by
    apply dser_injective rc_pos rc_lt_half
    have : cb ω = cb ω' := by simp only [Δb] at hΔb0; linarith
    simpa only [cb] using this
  funext j
  rcases j with n | m
  · exact congrFun hpos n
  · have := congrFun hneg m
    have e : Int.negSucc m = -(m : ℤ) - 1 := by rw [Int.negSucc_eq]; ring
    rw [e]; exact this

lemma catCod_holder (ℓ : ℕ) (ω ω' : Config) (h : ∀ j : ℤ, j.natAbs ≤ ℓ → ω j = ω' j) :
    dist (catCod ω) (catCod ω') ≤ 2 / (1 - rc) * rc ^ ℓ := by
  have hr0 := rc_pos
  have hr1 := rc_lt_one
  have hs := s5_sq
  have hs2 := s5_gt
  have hs3 := s5_lt
  have hΔa : |ca ω - ca ω'| ≤ rc ^ ℓ / (1 - rc) := by
    refine (abs_ca_sub_le (N := ℓ + 1) fun n hn => h n (by omega)).trans ?_
    rw [pow_succ, ← mul_div_assoc, mul_comm rc]
    gcongr
    calc rc ^ ℓ * rc * rc ≤ rc ^ ℓ * 1 * 1 := by gcongr
      _ = rc ^ ℓ := by ring
  have hΔb : |cb ω - cb ω'| ≤ rc ^ ℓ / (1 - rc) :=
    abs_cb_sub_le (N := ℓ) fun m hm => h _ (by omega)
  refine dist_torusProj_le fun i => ?_
  have key : ∀ u v : ℝ, |u| ≤ 1 → |v| ≤ 1 →
      |(ca ω * u - cb ω * v) - (ca ω' * u - cb ω' * v)| ≤ 2 / (1 - rc) * rc ^ ℓ := by
    intro u v hu hv
    have : (ca ω * u - cb ω * v) - (ca ω' * u - cb ω' * v) =
        (ca ω - ca ω') * u - (cb ω - cb ω') * v := by ring
    rw [this]
    calc |(ca ω - ca ω') * u - (cb ω - cb ω') * v|
        ≤ |ca ω - ca ω'| * |u| + |cb ω - cb ω'| * |v| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ rc ^ ℓ / (1 - rc) * 1 + rc ^ ℓ / (1 - rc) * 1 := by gcongr
      _ = 2 / (1 - rc) * rc ^ ℓ := by ring
  fin_cases i
  · simp only [cx, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact key _ _ (by rw [abs_le]; constructor <;> nlinarith)
      (by rw [abs_le]; constructor <;> nlinarith)
  · simp only [cx, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact key _ _ (by rw [abs_le]; constructor <;> nlinarith)
      (by rw [abs_le]; constructor <;> nlinarith)

lemma catCod_horseshoeCoding : HorseshoeCoding ⇑(catMap ^ 2 : Equiv.Perm Torus) catCod :=
  { continuous := continuous_catCod
    injective := catCod_injective
    conj := catCod_conj
    holder := ⟨2 / (1 - rc), rc, rc_pos, rc_lt_one, catCod_holder⟩ }

/-- **Lemma `lem:fixed-horseshoe`**: `A²` has a two-symbol horseshoe with Hölder coding. -/
theorem catMap_horseshoe :
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∃ cod : Config → Torus,
      HorseshoeCoding ⇑(catMap ^ k₀ : Equiv.Perm Torus) cod :=
  ⟨2, le_rfl, catCod, catCod_horseshoeCoding⟩

end FiniteOrderMixing
