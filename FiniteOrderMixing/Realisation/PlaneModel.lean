import FiniteOrderMixing.Realisation.PlaneDiffeo

/-!
# The planar horseshoe model

A `C^n` diffeomorphism `T₀` of the plane, equal to the identity outside `[-5, 5]²`, which is affine
on three vertical strips of the unit square:

* on `[-1/100, 1/3 + 1/100] × [-1/4, 5/4]`: `T₀(x, y) = (3x, y/3)`;
* on `[2/3 - 1/100, 1 + 1/100] × [-1/4, 5/4]`: `T₀(x, y) = (3x - 2, (y + 2)/3)`;
* on `[11/24, 13/24] × [-1/4, 5/4]`: `T₀(x, y) = (1 - y, 1/2 + γ(x - 1/2))`.

The first two give an affine horseshoe with middle-thirds Cantor sets; the third map turns the
unstable (horizontal) direction of the gap strip into the stable (vertical) direction.  `T₀` is a
composition of three vertical contractions, a twist map, a vertical contraction and three
horizontal expansions.
-/

open Set

namespace FiniteOrderMixing

namespace PlaneDiffeo

variable {n : ℕ∞}

/-! ### Twists by a quarter turn -/

/-- The angle function: `π/2` on `[0, r²]`, `0` on `[2r², ∞)`. -/
noncomputable def quarterAngle (r : ℝ) (t : ℝ) : ℝ :=
  Real.pi / 2 * Real.smoothTransition ((2 * r ^ 2 - t) / r ^ 2)

lemma contDiff_quarterAngle (r : ℝ) : ContDiff ℝ n (quarterAngle r) := by
  unfold quarterAngle
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp (by fun_prop))

/-- The quarter-turn twist about `c`: a rotation by `π/2` on the disc of radius `r`, the identity
outside the disc of radius `√2 r`. -/
noncomputable def qtwist (c : P2) (r : ℝ) : PlaneDiffeo n :=
  twist c (quarterAngle r) (contDiff_quarterAngle r)

lemma qtwist_rot (c : P2) {r : ℝ} (hr : 0 < r) {p : P2} (hp : nsq c p ≤ r ^ 2) :
    (qtwist c r : PlaneDiffeo n) p = (c.1 - (p.2 - c.2), c.2 + (p.1 - c.1)) := by
  have h : quarterAngle r (nsq c p) = Real.pi / 2 := by
    unfold quarterAngle
    rw [Real.smoothTransition.one_of_one_le, mul_one]
    rw [le_div_iff₀ (by positivity)]; linarith
  rw [qtwist, twist_apply]
  simp only [twistFun, h, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ext <;> simp only <;> ring

lemma qtwist_far (c : P2) {r : ℝ} (hr : 0 < r) {p : P2} (hp : 2 * r ^ 2 ≤ nsq c p) :
    (qtwist c r : PlaneDiffeo n) p = p := by
  have h : quarterAngle r (nsq c p) = 0 := by
    unfold quarterAngle
    rw [Real.smoothTransition.zero_of_nonpos, mul_zero]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [qtwist, twist_apply]
  simp only [twistFun, h, Real.cos_zero, Real.sin_zero]
  ext <;> simp only <;> ring

/-! ### The model -/

lemma cp_C0 : ContrParams (53 / 300) (1 / 5) (1 / 3) 2 3 := ⟨by norm_num, by norm_num, by norm_num,
  by norm_num, by norm_num, by norm_num⟩
lemma cp_Cg : ContrParams (1 / 24) (1 / 12) (1 / 12) 1 2 := ⟨by norm_num, by norm_num, by norm_num,
  by norm_num, by norm_num, by norm_num⟩
lemma cp_Sg {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) : ContrParams (1 / 16) (1 / 12) γ (1 / 12) (1 / 6) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, hγ, hγ1⟩
lemma cp_E0 : ContrParams (1 / 4) (3 / 10) (1 / 3) 2 3 := ⟨by norm_num, by norm_num, by norm_num,
  by norm_num, by norm_num, by norm_num⟩
lemma cp_Eg : ContrParams (1 / 48) (1 / 24) (1 / 12) 1 2 := ⟨by norm_num, by norm_num, by norm_num,
  by norm_num, by norm_num, by norm_num⟩

/-- `p` lies outside the square `(-5, 5)²`. -/
def Far (p : P2) : Prop := 5 ≤ |p.1| ∨ 5 ≤ |p.2|

lemma far_x {p : P2} (hp : Far p) {c R : ℝ} (hc : |c| + R ≤ 5) (hfar : ¬ R ≤ |p.1 - c|) :
    5 ≤ |p.2| := by
  rcases hp with h | h
  · exfalso; apply hfar; have := abs_sub_abs_le_abs_sub p.1 c; linarith
  · exact h

lemma vContr_far {c₁ R₁ R₁' c s R R' : ℝ} (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R')
    (h1 : |c₁| + R₁' ≤ 5) (h2 : |c| + R' ≤ 5) {p : P2} (hp : Far p) :
    vContr hn c₁ R₁ R₁' c s R R' hP p = p := by
  by_cases hx : R₁' ≤ |p.1 - c₁|
  · exact vContr_of_far hn hP hx
  · apply vContr_of_far_y hn hP
    have := far_x hp h1 hx
    have := abs_sub_abs_le_abs_sub p.2 c; linarith

lemma hExp_far {c₁ R₁ R₁' c s R R' : ℝ} (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R')
    (h1 : |c₁| + R₁' ≤ 5) (h2 : |c| + R' ≤ 5) {p : P2} (hp : Far p) :
    hExp hn c₁ R₁ R₁' c s R R' hP p = p := by
  by_cases hx : R' ≤ |p.1 - c|
  · exact hExp_of_far_x hn hP hx
  · apply hExp_of_far hn hP
    have := far_x hp h2 hx
    have := abs_sub_abs_le_abs_sub p.2 c₁; linarith

lemma qtwist_far' {p : P2} (hp : Far p) :
    (qtwist ((1 : ℝ) / 2, (1 : ℝ) / 2) (1 / 12) : PlaneDiffeo n) p = p := by
  apply qtwist_far _ (by norm_num)
  unfold nsq
  simp only
  rcases hp with h | h
  · have : 9 / 2 ≤ |p.1 - 1 / 2| := by have := abs_sub_abs_le_abs_sub p.1 (1 / 2); norm_num at this ⊢; linarith
    have h2 : (9 / 2) ^ 2 ≤ (p.1 - 1 / 2) ^ 2 := by
      rw [← sq_abs (p.1 - 1 / 2)]; exact pow_le_pow_left₀ (by norm_num) this 2
    nlinarith [sq_nonneg (p.2 - 1 / 2)]
  · have : 9 / 2 ≤ |p.2 - 1 / 2| := by have := abs_sub_abs_le_abs_sub p.2 (1 / 2); norm_num at this ⊢; linarith
    have h2 : (9 / 2) ^ 2 ≤ (p.2 - 1 / 2) ^ 2 := by
      rw [← sq_abs (p.2 - 1 / 2)]; exact pow_le_pow_left₀ (by norm_num) this 2
    nlinarith [sq_nonneg (p.1 - 1 / 2)]

/-- The eight factors of `T₀`. -/
noncomputable def mC0 (hn : 1 ≤ n) : PlaneDiffeo n :=
  vContr hn (1 / 6) (53 / 300) (1 / 5) 0 (1 / 3) 2 3 cp_C0
noncomputable def mC1 (hn : 1 ≤ n) : PlaneDiffeo n :=
  vContr hn (5 / 6) (53 / 300) (1 / 5) 1 (1 / 3) 2 3 cp_C0
noncomputable def mCg (hn : 1 ≤ n) : PlaneDiffeo n :=
  vContr hn (1 / 2) (1 / 24) (1 / 12) (1 / 2) (1 / 12) 1 2 cp_Cg
noncomputable def mR : PlaneDiffeo n := qtwist ((1 : ℝ) / 2, (1 : ℝ) / 2) (1 / 12)
noncomputable def mSg (hn : 1 ≤ n) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) : PlaneDiffeo n :=
  vContr hn (1 / 2) (1 / 16) (1 / 12) (1 / 2) γ (1 / 12) (1 / 6) (cp_Sg hγ hγ1)
noncomputable def mE0 (hn : 1 ≤ n) : PlaneDiffeo n := hExp hn (1 / 6) (1 / 4) (3 / 10) 0 (1 / 3) 2 3 cp_E0
noncomputable def mE1 (hn : 1 ≤ n) : PlaneDiffeo n := hExp hn (5 / 6) (1 / 4) (3 / 10) 1 (1 / 3) 2 3 cp_E0
noncomputable def mEg (hn : 1 ≤ n) : PlaneDiffeo n :=
  hExp hn (1 / 2) (1 / 48) (1 / 24) (1 / 2) (1 / 12) 1 2 cp_Eg

/-- The model map `T₀`. -/
noncomputable def model (hn : 1 ≤ n) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) : PlaneDiffeo n :=
  (mC0 hn).trans <| (mC1 hn).trans <| (mCg hn).trans <| mR.trans <| (mSg hn hγ hγ1).trans <|
    (mE0 hn).trans <| (mE1 hn).trans (mEg hn)

variable (hn : 1 ≤ n) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)

lemma model_apply (p : P2) : model hn γ hγ hγ1 p =
    mEg hn (mE1 hn (mE0 hn (mSg hn hγ hγ1 ((mR : PlaneDiffeo n) (mCg hn (mC1 hn (mC0 hn p))))))) := rfl

lemma model_far {p : P2} (hp : Far p) : model hn γ hγ hγ1 p = p := by
  rw [model_apply]
  rw [show mC0 hn p = p from vContr_far hn cp_C0 (by norm_num) (by norm_num) hp,
    show mC1 hn p = p from vContr_far hn cp_C0 (by norm_num) (by norm_num) hp,
    show mCg hn p = p from vContr_far hn cp_Cg (by norm_num) (by norm_num) hp,
    show (mR : PlaneDiffeo n) p = p from qtwist_far' hp,
    show mSg hn hγ hγ1 p = p from vContr_far hn (cp_Sg hγ hγ1) (by norm_num) (by norm_num) hp,
    show mE0 hn p = p from hExp_far hn cp_E0 (by norm_num) (by norm_num) hp,
    show mE1 hn p = p from hExp_far hn cp_E0 (by norm_num) (by norm_num) hp,
    show mEg hn p = p from hExp_far hn cp_Eg (by norm_num) (by norm_num) hp]

lemma model_left {x y : ℝ} (hx0 : -1 / 100 ≤ x) (hx1 : x ≤ 1 / 3 + 1 / 100) (hy0 : -1 / 4 ≤ y)
    (hy1 : y ≤ 5 / 4) :
    model hn γ hγ hγ1 (x, y) = (3 * x, y / 3) := by
  have e1 : mC0 hn (x, y) = (x, y / 3) := by
    rw [mC0, vContr_apply hn cp_C0 (by simp only; rw [abs_le]; constructor <;> linarith)
      (by simp only; rw [abs_le]; constructor <;> linarith)]
    ext <;> simp only; ring
  have e2 : mC1 hn (x, y / 3) = (x, y / 3) :=
    vContr_of_far hn cp_C0 (by simp only; rw [abs_sub_comm, le_abs]; left; linarith)
  have e3 : mCg hn (x, y / 3) = (x, y / 3) :=
    vContr_of_far hn cp_Cg (by simp only; rw [abs_sub_comm, le_abs]; left; linarith)
  have e4 : (mR : PlaneDiffeo n) (x, y / 3) = (x, y / 3) :=
    qtwist_far _ (by norm_num) (by
      unfold nsq; simp only
      nlinarith [sq_nonneg (y / 3 - 1 / 2), mul_self_nonneg (1 / 2 - x - 47 / 300)])
  have e5 : mSg hn hγ hγ1 (x, y / 3) = (x, y / 3) :=
    vContr_of_far hn (cp_Sg hγ hγ1) (by simp only; rw [abs_sub_comm, le_abs]; left; linarith)
  have e6 : mE0 hn (x, y / 3) = (3 * x, y / 3) := by
    rw [mE0, hExp_apply hn cp_E0 (by simp only; rw [abs_le]; constructor <;> linarith)
      (by simp only; rw [sub_zero, abs_le]; constructor <;> linarith)]
    ext <;> simp only; field_simp; ring
  have e7 : mE1 hn (3 * x, y / 3) = (3 * x, y / 3) :=
    hExp_of_far hn cp_E0 (by simp only; rw [abs_sub_comm, le_abs]; left; linarith)
  have e8 : mEg hn (3 * x, y / 3) = (3 * x, y / 3) :=
    hExp_of_far hn cp_Eg (by simp only; rw [abs_sub_comm, le_abs]; left; linarith)
  rw [model_apply, e1, e2, e3, e4, e5, e6, e7, e8]

lemma model_right {x y : ℝ} (hx0 : 2 / 3 - 1 / 100 ≤ x) (hx1 : x ≤ 1 + 1 / 100) (hy0 : -1 / 4 ≤ y)
    (hy1 : y ≤ 5 / 4) : model hn γ hγ hγ1 (x, y) = (3 * x - 2, (y + 2) / 3) := by
  have e1 : mC0 hn (x, y) = (x, y) :=
    vContr_of_far hn cp_C0 (by simp only; rw [le_abs]; left; linarith)
  have e2 : mC1 hn (x, y) = (x, (y + 2) / 3) := by
    rw [mC1, vContr_apply hn cp_C0 (by simp only; rw [abs_le]; constructor <;> linarith)
      (by simp only; rw [abs_le]; constructor <;> linarith)]
    ext <;> simp only; ring
  have e3 : mCg hn (x, (y + 2) / 3) = (x, (y + 2) / 3) :=
    vContr_of_far hn cp_Cg (by simp only; rw [le_abs]; left; linarith)
  have e4 : (mR : PlaneDiffeo n) (x, (y + 2) / 3) = (x, (y + 2) / 3) :=
    qtwist_far _ (by norm_num) (by
      unfold nsq; simp only
      nlinarith [sq_nonneg ((y + 2) / 3 - 1 / 2), mul_self_nonneg (x - 1 / 2 - 47 / 300)])
  have e5 : mSg hn hγ hγ1 (x, (y + 2) / 3) = (x, (y + 2) / 3) :=
    vContr_of_far hn (cp_Sg hγ hγ1) (by simp only; rw [le_abs]; left; linarith)
  have e6 : mE0 hn (x, (y + 2) / 3) = (x, (y + 2) / 3) :=
    hExp_of_far hn cp_E0 (by simp only; rw [le_abs]; left; linarith)
  have e7 : mE1 hn (x, (y + 2) / 3) = (3 * x - 2, (y + 2) / 3) := by
    rw [mE1, hExp_apply hn cp_E0 (by simp only; rw [abs_le]; constructor <;> linarith)
      (by simp only; rw [abs_le]; constructor <;> linarith)]
    ext <;> simp only; field_simp; ring
  have e8 : mEg hn (3 * x - 2, (y + 2) / 3) = (3 * x - 2, (y + 2) / 3) :=
    hExp_of_far hn cp_Eg (by simp only; rw [le_abs]; left; linarith)
  rw [model_apply, e1, e2, e3, e4, e5, e6, e7, e8]

lemma model_gap (hγ2 : γ ≤ 1 / 2) {x y : ℝ} (hx0 : 11 / 24 ≤ x) (hx1 : x ≤ 13 / 24)
    (hy0 : -1 / 4 ≤ y) (hy1 : y ≤ 5 / 4) :
    model hn γ hγ hγ1 (x, y) = (1 - y, 1 / 2 + γ * (x - 1 / 2)) := by
  have hg : |γ * (x - 1 / 2)| ≤ 1 / 48 := by
    rw [abs_mul, abs_of_pos hγ]
    have : |x - 1 / 2| ≤ 1 / 24 := by rw [abs_le]; constructor <;> linarith
    calc γ * |x - 1 / 2| ≤ 1 / 2 * (1 / 24) :=
          mul_le_mul hγ2 this (abs_nonneg _) (by norm_num)
      _ = 1 / 48 := by norm_num
  rw [abs_le] at hg
  set y₁ := 1 / 2 + (y - 1 / 2) / 12 with hy₁
  set x₂ := 1 / 2 - (y - 1 / 2) / 12 with hx₂
  set y₃ := 1 / 2 + γ * (x - 1 / 2) with hy₃
  have e1 : mC0 hn (x, y) = (x, y) :=
    vContr_of_far hn cp_C0 (by simp only; rw [le_abs]; left; linarith)
  have e2 : mC1 hn (x, y) = (x, y) :=
    vContr_of_far hn cp_C0 (by simp only; rw [le_abs]; right; linarith)
  have e3 : mCg hn (x, y) = (x, y₁) := by
    rw [mCg, vContr_apply hn cp_Cg (by simp only; rw [abs_le]; constructor <;> linarith)
      (by simp only; rw [abs_le]; constructor <;> linarith)]
    ext <;> simp only; rw [hy₁]; ring
  have e4 : (mR : PlaneDiffeo n) (x, y₁) = (x₂, x) := by
    rw [mR, qtwist_rot _ (by norm_num) (by
      unfold nsq; simp only [hy₁]
      nlinarith [mul_self_nonneg (x - 1 / 2), mul_self_nonneg (y - 1 / 2)])]
    ext <;> simp only [hx₂, hy₁] <;> ring
  have e5 : mSg hn hγ hγ1 (x₂, x) = (x₂, y₃) := by
    rw [mSg, vContr_apply hn (cp_Sg hγ hγ1)
      (by simp only [hx₂]; rw [abs_le]; constructor <;> linarith)
      (by simp only; rw [abs_le]; constructor <;> linarith)]
  have e6 : mE0 hn (x₂, y₃) = (x₂, y₃) :=
    hExp_of_far hn cp_E0 (by simp only [hy₃]; rw [le_abs]; left; linarith)
  have e7 : mE1 hn (x₂, y₃) = (x₂, y₃) :=
    hExp_of_far hn cp_E0 (by simp only [hy₃]; rw [le_abs]; right; linarith)
  have e8 : mEg hn (x₂, y₃) = (1 - y, y₃) := by
    rw [mEg, hExp_apply hn cp_Eg (by simp only [hy₃]; rw [abs_le]; constructor <;> linarith)
      (by simp only [hx₂]; rw [abs_le]; constructor <;> linarith)]
    ext <;> simp only [hx₂]; field_simp; ring
  rw [model_apply, e1, e2, e3, e4, e5, e6, e7, e8]

end PlaneDiffeo

end FiniteOrderMixing
