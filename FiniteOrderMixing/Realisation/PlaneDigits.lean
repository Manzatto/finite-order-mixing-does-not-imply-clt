import FiniteOrderMixing.Realisation.PlaneModel
import FiniteOrderMixing.Realisation.CatHorseshoe

/-!
# Ternary digits and the coding of the planar horseshoe

The inverse branches `φ_b(z) = (z + 2[b])/3` of the expanding direction, their compositions
`phis`, and the coding `pcod ω = (Σ_{i ≥ 0} 2[ω_i] 3^{-i-1}, Σ_{i ≥ 0} 2[ω_{-1-i}] 3^{-i-1})` of the
middle-thirds horseshoe.
-/

open Set Filter Topology

namespace FiniteOrderMixing

/-! ### Inverse branches -/

/-- The inverse branch `φ_b(z) = (z + 2[b])/3`. -/
noncomputable def phi (b : Bool) (z : ℝ) : ℝ := (z + 2 * bit b) / 3

/-- `φ_{d 0} ∘ ⋯ ∘ φ_{d (m-1)}`. -/
noncomputable def phis (d : ℕ → Bool) : ℕ → ℝ → ℝ
  | 0, z => z
  | m + 1, z => phi (d 0) (phis (fun i => d (i + 1)) m z)

/-- `φ_{w (j-1)} ∘ ⋯ ∘ φ_{w 0}`. -/
noncomputable def psis (w : ℕ → Bool) : ℕ → ℝ → ℝ
  | 0, y => y
  | j + 1, y => phi (w j) (psis w j y)

lemma phi_mem {b : Bool} {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) : phi b z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hz
  have := bit_nonneg b; have := bit_le_one b
  constructor <;> unfold phi <;> linarith

lemma phis_zero (d : ℕ → Bool) (z : ℝ) : phis d 0 z = z := rfl

lemma phis_succ (d : ℕ → Bool) (m : ℕ) (z : ℝ) :
    phis d (m + 1) z = phi (d 0) (phis (fun i => d (i + 1)) m z) := rfl

lemma phis_mem (d : ℕ → Bool) (m : ℕ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    phis d m z ∈ Icc (0 : ℝ) 1 := by
  induction m generalizing d with
  | zero => exact hz
  | succ m ih => exact phi_mem (ih _)

lemma phis_sub (d : ℕ → Bool) (m : ℕ) (z z' : ℝ) :
    phis d m z - phis d m z' = (z - z') / 3 ^ m := by
  induction m generalizing d with
  | zero => simp [phis]
  | succ m ih =>
    simp only [phis_succ, phi]
    rw [show (phis (fun i => d (i + 1)) m z + 2 * bit (d 0)) / 3 -
      (phis (fun i => d (i + 1)) m z' + 2 * bit (d 0)) / 3 =
      (phis (fun i => d (i + 1)) m z - phis (fun i => d (i + 1)) m z') / 3 by ring, ih]
    rw [pow_succ, div_div]

lemma phis_add (d : ℕ → Bool) (a b : ℕ) (z : ℝ) :
    phis d (a + b) z = phis d a (phis (fun i => d (i + a)) b z) := by
  induction a generalizing d with
  | zero => simp [phis]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, phis_succ, ih, phis_succ]
    congr 3

lemma phis_congr {d d' : ℕ → Bool} {m : ℕ} (h : ∀ i < m, d i = d' i) (z : ℝ) :
    phis d m z = phis d' m z := by
  induction m generalizing d d' with
  | zero => rfl
  | succ m ih =>
    rw [phis_succ, phis_succ, h 0 (by omega), ih fun i hi => h (i + 1) (by omega)]

lemma one_sub_phi (b : Bool) (z : ℝ) : 1 - phi b z = phi (!b) (1 - z) := by
  cases b <;> simp [phi, bit] <;> ring

lemma one_sub_phis (d : ℕ → Bool) (m : ℕ) (z : ℝ) :
    1 - phis d m z = phis (fun i => !d i) m (1 - z) := by
  induction m generalizing d with
  | zero => rfl
  | succ m ih => rw [phis_succ, phis_succ, one_sub_phi, ih]

lemma psis_eq_phis (w : ℕ → Bool) (j : ℕ) (y : ℝ) :
    psis w j y = phis (fun i => w (j - 1 - i)) j y := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [psis, ih, phis_succ]
    rw [phis_congr (d := fun i => w (j - 1 - i)) (d' := fun i => w (j + 1 - 1 - (i + 1)))
      (fun i hi => by congr 1; omega)]
    simp

lemma psis_mem (w : ℕ → Bool) (j : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    psis w j y ∈ Icc (0 : ℝ) 1 := by
  rw [psis_eq_phis]; exact phis_mem _ _ hy

/-- Two compositions sharing their first `h` digits are `3^{-h}`-close on `[0, 1]`. -/
lemma abs_phis_sub_phis_le {d d' : ℕ → Bool} {h m m' : ℕ} (hd : ∀ i < h, d i = d' i)
    (hm : h ≤ m) (hm' : h ≤ m') {z z' : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) (hz' : z' ∈ Icc (0 : ℝ) 1) :
    |phis d m z - phis d' m' z'| ≤ (1 / 3) ^ h := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hm'
  rw [phis_add, phis_add, phis_congr (d' := d') hd, phis_sub]
  have h1 := phis_mem (fun i => d (i + h)) a hz
  have h2 := phis_mem (fun i => d' (i + h)) b hz'
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ h), div_le_iff₀ (by positivity),
    div_pow, one_pow, div_mul_cancel₀ _ (by positivity)]
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The point `phis d m z` lies `3^{-m} δ` away from the endpoints if `z` lies `δ` away. -/
lemma phis_margin (d : ℕ → Bool) (m : ℕ) {δ z : ℝ} (hz0 : δ ≤ z) (hz1 : z ≤ 1 - δ) :
    δ / 3 ^ m ≤ phis d m z ∧ phis d m z ≤ 1 - δ / 3 ^ m := by
  induction m generalizing d with
  | zero => simpa using ⟨hz0, hz1⟩
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih (fun i => d (i + 1))
    rw [phis_succ, pow_succ]
    have hb0 := bit_nonneg (d 0); have hb1 := bit_le_one (d 0)
    have hp : (0 : ℝ) < 3 ^ m := by positivity
    have e : δ / (3 ^ m * 3) = δ / 3 ^ m / 3 := by rw [div_div]
    rw [e]
    unfold phi
    constructor <;> linarith

/-- If `z` is `δ`-inside `[0, 1]`, then `φ_b(z)` is `δ/3`-inside the strip `[2[b]/3, (1+2[b])/3]`. -/
lemma phi_strip (b : Bool) {δ z : ℝ} (hz0 : δ ≤ z) (hz1 : z ≤ 1 - δ) :
    2 * bit b / 3 + δ / 3 ≤ phi b z ∧ phi b z ≤ (1 + 2 * bit b) / 3 - δ / 3 := by
  unfold phi; constructor <;> linarith

/-! ### The coding of the horseshoe -/

/-- The unstable coordinate `Σ_{i ≥ 0} 2[ω_i] 3^{-i-1}`. -/
noncomputable def codX (ω : Config) : ℝ := 2 / 3 * dser (1 / 3) fun n => ω n

/-- The stable coordinate `Σ_{i ≥ 0} 2[ω_{-1-i}] 3^{-i-1}`. -/
noncomputable def codY (ω : Config) : ℝ := 2 / 3 * dser (1 / 3) fun m => ω (-(m : ℤ) - 1)

/-- The coding `Σ → ℝ²` of the middle-thirds horseshoe. -/
noncomputable def pcod (ω : Config) : P2 := (codX ω, codY ω)

lemma dser_third_mem (f : ℕ → Bool) : dser (1 / 3) f ∈ Icc (0 : ℝ) (3 / 2) := by
  constructor
  · exact tsum_nonneg fun n => mul_nonneg (bit_nonneg _) (by positivity)
  · have := abs_dser_le (r := 1 / 3) (by norm_num) (by norm_num) f
    norm_num at this
    exact (le_abs_self _).trans this

lemma codX_mem (ω : Config) : codX ω ∈ Icc (0 : ℝ) 1 := by
  have := dser_third_mem fun n => ω n
  unfold codX; constructor <;> nlinarith [this.1, this.2]

lemma codY_mem (ω : Config) : codY ω ∈ Icc (0 : ℝ) 1 := by
  have := dser_third_mem fun m => ω (-(m : ℤ) - 1)
  unfold codY; constructor <;> nlinarith [this.1, this.2]

lemma dser_third_eq (f : ℕ → Bool) :
    2 / 3 * dser (1 / 3) f = phi (f 0) (2 / 3 * dser (1 / 3) fun n => f (n + 1)) := by
  rw [dser_succ (by norm_num) (by norm_num)]
  unfold phi; ring

lemma codX_eq (ω : Config) : codX ω = phi (ω 0) (codX (shift ω)) := by
  have h : codX (shift ω) = 2 / 3 * dser (1 / 3) fun n : ℕ => ω ((n + 1 : ℕ) : ℤ) := by
    unfold codX; congr 2
  rw [h, codX, dser_third_eq]
  simp

lemma codY_shift (ω : Config) : codY (shift ω) = phi (ω 0) (codY ω) := by
  have h1 : codY (shift ω) = 2 / 3 * dser (1 / 3) fun m : ℕ => ω (-(m : ℤ)) := by
    unfold codY; congr 2; funext m; simp [shift]
  have h2 : (fun n : ℕ => ω (-((n + 1 : ℕ) : ℤ))) = fun m : ℕ => ω (-(m : ℤ) - 1) := by
    funext m; congr 1; push_cast; ring
  rw [h1, dser_third_eq]
  simp only [Nat.cast_zero, neg_zero]
  rw [h2]; rfl

lemma codX_eq_phis (ω : Config) (m : ℕ) :
    codX ω = phis (fun i => ω i) m (codX (shift^[m] ω)) := by
  induction m generalizing ω with
  | zero => rfl
  | succ m ih =>
    rw [phis_succ, codX_eq ω, ih (shift ω), Function.iterate_succ_apply]
    congr 2

lemma codY_iterate_psis (ω : Config) (m : ℕ) :
    codY (shift^[m] ω) = psis (fun i => ω i) m (codY ω) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', codY_shift, ih, psis, shift_iterate_apply]
    simp

lemma codY_iterate (ω : Config) (m : ℕ) :
    codY (shift^[m] ω) = phis (fun i => ω ((m : ℤ) - 1 - i)) m (codY ω) := by
  rw [codY_iterate_psis, psis_eq_phis]
  apply phis_congr; intro i hi
  congr 1
  rw [show m - 1 - i = m - (1 + i) by omega, Nat.cast_sub (by omega : 1 + i ≤ m)]
  push_cast; ring

lemma pcod_injective : Function.Injective pcod := by
  intro ω ω' h
  simp only [pcod, Prod.mk.injEq, codX, codY] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := dser_injective (r := 1 / 3) (by norm_num) (by norm_num)
    (mul_left_cancel₀ (by norm_num) h1)
  have e2 := dser_injective (r := 1 / 3) (by norm_num) (by norm_num)
    (mul_left_cancel₀ (by norm_num) h2)
  funext j
  rcases Int.eq_nat_or_neg j with ⟨m, rfl | rfl⟩
  · exact congrFun e1 m
  · rcases m with _ | m
    · simpa using congrFun e1 0
    · have := congrFun e2 m
      have e : -((m + 1 : ℕ) : ℤ) = -(m : ℤ) - 1 := by push_cast; ring
      rw [e]; exact this

lemma continuous_pcod : Continuous pcod := by
  apply Continuous.prodMk
  · exact continuous_const.mul (continuous_dser (by norm_num) (by norm_num)
      fun n => continuous_apply _)
  · exact continuous_const.mul (continuous_dser (by norm_num) (by norm_num)
      fun n => continuous_apply _)

lemma dist_pcod_le (ℓ : ℕ) (ω ω' : Config) (h : ∀ j : ℤ, j.natAbs ≤ ℓ → ω j = ω' j) :
    dist (pcod ω) (pcod ω') ≤ 1 * (1 / 3) ^ ℓ := by
  rw [Prod.dist_eq, one_mul, Real.dist_eq, Real.dist_eq]
  have hx := abs_dser_sub_le (r := 1 / 3) (by norm_num) (by norm_num)
    (f := fun n => ω n) (g := fun n => ω' n) (N := ℓ + 1)
    (fun n hn => h n (by simp; omega))
  have hy := abs_dser_sub_le (r := 1 / 3) (by norm_num) (by norm_num)
    (f := fun m => ω (-(m : ℤ) - 1)) (g := fun m => ω' (-(m : ℤ) - 1)) (N := ℓ)
    (fun m hm => h _ (by omega))
  apply max_le
  · simp only [pcod, codX]
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
    have e : (2 : ℝ) / 3 * ((1 / 3) ^ (ℓ + 1) / (1 - 1 / 3)) = (1 / 3) ^ ℓ / 3 := by
      rw [pow_succ]; ring
    calc (2 : ℝ) / 3 * |dser (1 / 3) (fun n => ω n) - dser (1 / 3) (fun n => ω' n)|
        ≤ 2 / 3 * ((1 / 3) ^ (ℓ + 1) / (1 - 1 / 3)) := by gcongr
      _ ≤ (1 / 3) ^ ℓ := by rw [e]; linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 3) ℓ]
  · simp only [pcod, codY]
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
    calc (2 : ℝ) / 3 * |dser (1 / 3) (fun m => ω (-(m : ℤ) - 1)) -
          dser (1 / 3) (fun m => ω' (-(m : ℤ) - 1))|
        ≤ 2 / 3 * ((1 / 3) ^ ℓ / (1 - 1 / 3)) := by gcongr
      _ = (1 / 3) ^ ℓ := by ring

end FiniteOrderMixing
