import FiniteOrderMixing.Basic

/-!
# Diffeomorphisms of the plane

A small toolkit of `C^n` diffeomorphisms of `ℝ × ℝ` (with the sup norm), used to build the
planar model of Theorem B:

* `PlaneDiffeo.ofBijective`: a bijective `C^n` map (`n ≥ 1`) with injective derivative is a
  `C^n` diffeomorphism (inverse function theorem);
* `PlaneDiffeo.vert`: the fibrewise map `(x, y) ↦ (x, y + f(x, y))`, a diffeomorphism when
  `∂_y f > -1` and `f` vanishes for large `|y|`; `PlaneDiffeo.horiz` is its transpose;
* `PlaneDiffeo.twist`: the twist map `z ↦ c + R_{θ(|z - c|²)} (z - c)`;
* `bump`, `vContr`, `hContr`: smooth contractions of a box, equal to the identity far away.
-/

open Set Filter Topology

namespace FiniteOrderMixing

/-- The plane `ℝ × ℝ`, with the sup norm. -/
abbrev P2 := ℝ × ℝ

/-- A `C^n` diffeomorphism of the plane. -/
structure PlaneDiffeo (n : ℕ∞) extends P2 ≃ P2 where
  contDiff_toFun : ContDiff ℝ n toFun
  contDiff_invFun : ContDiff ℝ n invFun

namespace PlaneDiffeo

variable {n : ℕ∞}

instance : CoeFun (PlaneDiffeo n) (fun _ => P2 → P2) := ⟨fun f => f.toFun⟩

/-- The inverse diffeomorphism. -/
protected def symm (f : PlaneDiffeo n) : PlaneDiffeo n where
  toEquiv := f.toEquiv.symm
  contDiff_toFun := f.contDiff_invFun
  contDiff_invFun := f.contDiff_toFun

/-- Composition: first `f`, then `g`. -/
protected def trans (f g : PlaneDiffeo n) : PlaneDiffeo n where
  toEquiv := f.toEquiv.trans g.toEquiv
  contDiff_toFun := g.contDiff_toFun.comp f.contDiff_toFun
  contDiff_invFun := f.contDiff_invFun.comp g.contDiff_invFun

lemma trans_apply (f g : PlaneDiffeo n) (p : P2) : f.trans g p = g (f p) := rfl

lemma symm_apply_apply (f : PlaneDiffeo n) (p : P2) : f.symm (f p) = p := f.left_inv p

lemma apply_symm_apply (f : PlaneDiffeo n) (p : P2) : f (f.symm p) = p := f.right_inv p

lemma symm_apply_eq (f : PlaneDiffeo n) {p q : P2} : f.symm p = q ↔ p = f q :=
  f.toEquiv.symm_apply_eq

lemma contDiff (f : PlaneDiffeo n) : ContDiff ℝ n f := f.contDiff_toFun

/-- Lower the regularity index without changing the map or its inverse. -/
def of_le {m : ℕ∞} (f : PlaneDiffeo n) (h : m ≤ n) : PlaneDiffeo m where
  toEquiv := f.toEquiv
  contDiff_toFun := f.contDiff_toFun.of_le (by exact_mod_cast h)
  contDiff_invFun := f.contDiff_invFun.of_le (by exact_mod_cast h)

lemma of_le_apply {m : ℕ∞} (f : PlaneDiffeo n) (h : m ≤ n) (p : P2) :
    f.of_le h p = f p := rfl

lemma injective (f : PlaneDiffeo n) : Function.Injective f := f.toEquiv.injective

lemma symm_eq_of_apply_eq (f : PlaneDiffeo n) {p : P2} (h : f p = p) : f.symm p = p :=
  (f.symm_apply_eq).2 h.symm

/-- A bijective `C^n` map of the plane, `n ≥ 1`, with injective derivative everywhere, is a `C^n`
diffeomorphism. -/
noncomputable def ofBijective (f : P2 → P2) (hf : ContDiff ℝ n f) (hn : 1 ≤ n)
    (hb : Function.Bijective f) (hd : ∀ p, Function.Injective (fderiv ℝ f p)) :
    PlaneDiffeo n :=
  let e : P2 → P2 ≃L[ℝ] P2 := fun p =>
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ f p : P2 →ₗ[ℝ] P2) (hd p)).toContinuousLinearEquiv
  have hstrict : ∀ p, HasStrictFDerivAt f (e p : P2 →L[ℝ] P2) p := fun p => by
    have := hf.contDiffAt.hasStrictFDerivAt (x := p)
      (by exact_mod_cast (zero_lt_one.trans_le hn).ne')
    convert this using 1
    exact ContinuousLinearMap.ext fun v => rfl
  let h : P2 ≃ₜ P2 := (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous
    (isOpenMap_of_hasStrictFDerivAt_equiv hstrict)
  { toEquiv := Equiv.ofBijective f hb
    contDiff_toFun := hf
    contDiff_invFun :=
      h.contDiff_symm (f₀' := e) (fun a => (hstrict a).hasFDerivAt) hf }

lemma ofBijective_apply (f : P2 → P2) (hf : ContDiff ℝ n f) (hn : 1 ≤ n)
    (hb : Function.Bijective f) (hd : ∀ p, Function.Injective (fderiv ℝ f p)) (p : P2) :
    ofBijective f hf hn hb hd p = f p := rfl

/-! ### Fibrewise maps -/

/-- `(x, y) ↦ (x, y + f(x, y))`. -/
def vertFun (f : P2 → ℝ) (p : P2) : P2 := (p.1, p.2 + f p)

lemma hasDerivAt_slice {f : P2 → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun y => f (x, y)) (fderiv ℝ f (x, y) (0, 1)) y := by
  have h1 : HasDerivAt (fun y : ℝ => ((x, y) : P2)) ((0, 1) : P2) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  exact (hf (x, y)).hasFDerivAt.comp_hasDerivAt y h1

lemma vertFun_bijective {f : P2 → ℝ} (hf : Differentiable ℝ f) {K : ℝ}
    (hK : ∀ p : P2, K ≤ |p.2| → f p = 0)
    (hpos : ∀ x y, 0 < 1 + deriv (fun y => f (x, y)) y) : Function.Bijective (vertFun f) := by
  have hmono : ∀ x, StrictMono fun y => y + f (x, y) := fun x => by
    apply strictMono_of_deriv_pos
    intro y
    have hd : HasDerivAt (fun y => y + f (x, y)) (1 + fderiv ℝ f (x, y) (0, 1)) y :=
      (hasDerivAt_id' y).add (hasDerivAt_slice hf x y)
    rw [hd.deriv, ← (hasDerivAt_slice hf x y).deriv]
    exact hpos x y
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [vertFun, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    rw [(hmono x).injective h2]
  · rintro ⟨x, t⟩
    have hc : Continuous fun y => y + f (x, y) :=
      continuous_id.add (hf.continuous.comp (continuous_const.prodMk continuous_id))
    set a := -(|t| + |K|)
    set b := |t| + |K|
    have hab : a ≤ b := by simp only [a, b]; linarith [abs_nonneg t, abs_nonneg K]
    have hKa : K ≤ |(x, a).2| := by
      simp only [a, abs_neg]
      rw [abs_of_nonneg (by positivity)]
      linarith [abs_nonneg t, le_abs_self K]
    have hKb : K ≤ |(x, b).2| := by
      simp only [b]
      rw [abs_of_nonneg (by positivity)]
      linarith [abs_nonneg t, le_abs_self K]
    have hfa : a + f (x, a) = a := by rw [hK (x, a) hKa, add_zero]
    have hfb : b + f (x, b) = b := by rw [hK (x, b) hKb, add_zero]
    obtain ⟨y, -, hy⟩ := intermediate_value_Icc hab hc.continuousOn
      (show t ∈ Icc (a + f (x, a)) (b + f (x, b)) by
        rw [hfa, hfb]; constructor <;> simp only [a, b] <;>
          linarith [neg_abs_le t, le_abs_self t, abs_nonneg K])
    exact ⟨(x, y), by simp only [vertFun, hy]⟩

lemma hasFDerivAt_vertFun {f : P2 → ℝ} (hf : Differentiable ℝ f) (p : P2) :
    HasFDerivAt (vertFun f)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ + fderiv ℝ f p)) p :=
  (hasFDerivAt_fst).prodMk (hasFDerivAt_snd.add (hf p).hasFDerivAt)

lemma fderiv_vertFun_injective {f : P2 → ℝ} (hf : Differentiable ℝ f)
    (hpos : ∀ x y, 0 < 1 + deriv (fun y => f (x, y)) y) (p : P2) :
    Function.Injective (fderiv ℝ (vertFun f) p) := by
  rw [(hasFDerivAt_vertFun hf p).fderiv, injective_iff_map_eq_zero]
  rintro ⟨u, v⟩ h
  have h1 : u = 0 := congrArg Prod.fst h
  have h2 : v + fderiv ℝ f p (u, v) = 0 := congrArg Prod.snd h
  subst h1
  have hlin : fderiv ℝ f p (0, v) = v * fderiv ℝ f p (0, 1) := by
    rw [show ((0 : ℝ), v) = v • ((0 : ℝ), (1 : ℝ)) by simp, map_smul, smul_eq_mul]
  have hd := (hasDerivAt_slice hf p.1 p.2).deriv
  have hp := hpos p.1 p.2
  rw [hd] at hp
  rw [hlin] at h2
  have hp' : 0 < 1 + fderiv ℝ f p (0, 1) := by simpa using hp
  have : v * (1 + fderiv ℝ f p (0, 1)) = 0 := by linear_combination h2
  have hv : v = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hp'.ne'
  simp [hv]

/-- The fibrewise diffeomorphism `(x, y) ↦ (x, y + f(x, y))`. -/
noncomputable def vert (f : P2 → ℝ) (hf : ContDiff ℝ n f) (hn : 1 ≤ n) (K : ℝ)
    (hK : ∀ p : P2, K ≤ |p.2| → f p = 0)
    (hpos : ∀ x y, 0 < 1 + deriv (fun y => f (x, y)) y) : PlaneDiffeo n :=
  have hd : Differentiable ℝ f :=
    hf.differentiable (by exact_mod_cast (zero_lt_one.trans_le hn).ne')
  ofBijective (vertFun f)
    (contDiff_fst.prodMk (contDiff_snd.add hf)) hn (vertFun_bijective hd hK hpos)
    (fderiv_vertFun_injective hd hpos)

lemma vert_apply (f : P2 → ℝ) (hf : ContDiff ℝ n f) (hn : 1 ≤ n) (K : ℝ)
    (hK : ∀ p : P2, K ≤ |p.2| → f p = 0)
    (hpos : ∀ x y, 0 < 1 + deriv (fun y => f (x, y)) y) (p : P2) :
    vert f hf hn K hK hpos p = (p.1, p.2 + f p) := rfl

/-- The coordinate swap. -/
def swap : PlaneDiffeo n where
  toEquiv := Equiv.prodComm ℝ ℝ
  contDiff_toFun := contDiff_snd.prodMk contDiff_fst
  contDiff_invFun := contDiff_snd.prodMk contDiff_fst

lemma swap_apply (p : P2) : (swap : PlaneDiffeo n) p = (p.2, p.1) := rfl

/-- The fibrewise diffeomorphism `(x, y) ↦ (x + f(x, y), y)`. -/
noncomputable def horiz (f : P2 → ℝ) (hf : ContDiff ℝ n f) (hn : 1 ≤ n) (K : ℝ)
    (hK : ∀ p : P2, K ≤ |p.1| → f p = 0)
    (hpos : ∀ x y, 0 < 1 + deriv (fun x => f (x, y)) x) : PlaneDiffeo n :=
  swap.trans ((vert (fun p => f (p.2, p.1)) (hf.comp (contDiff_snd.prodMk contDiff_fst)) hn K
    (fun p hp => hK (p.2, p.1) hp) (fun x y => hpos y x)).trans swap)

lemma horiz_apply (f : P2 → ℝ) (hf : ContDiff ℝ n f) (hn : 1 ≤ n) (K : ℝ)
    (hK : ∀ p : P2, K ≤ |p.1| → f p = 0)
    (hpos : ∀ x y, 0 < 1 + deriv (fun x => f (x, y)) x) (p : P2) :
    horiz f hf hn K hK hpos p = (p.1 + f p, p.2) := rfl

/-! ### Twist maps -/

/-- The squared Euclidean distance `|p - c|²`. -/
def nsq (c p : P2) : ℝ := (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2

/-- The twist map `z ↦ c + R_{θ(|z - c|²)} (z - c)` (Euclidean norm). -/
noncomputable def twistFun (c : P2) (θ : ℝ → ℝ) (p : P2) : P2 :=
  (c.1 + (Real.cos (θ (nsq c p)) * (p.1 - c.1) - Real.sin (θ (nsq c p)) * (p.2 - c.2)),
    c.2 + (Real.sin (θ (nsq c p)) * (p.1 - c.1) + Real.cos (θ (nsq c p)) * (p.2 - c.2)))

lemma nsq_twistFun (c : P2) (θ : ℝ → ℝ) (p : P2) : nsq c (twistFun c θ p) = nsq c p := by
  have := Real.sin_sq_add_cos_sq (θ (nsq c p))
  simp only [nsq, twistFun, add_sub_cancel_left] at this ⊢
  linear_combination ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) * this

lemma twistFun_neg (c : P2) (θ : ℝ → ℝ) (p : P2) :
    twistFun c (fun s => -θ s) (twistFun c θ p) = p := by
  have hs := nsq_twistFun c θ p
  set q := twistFun c θ p with hq
  have hq1 : q.1 - c.1 = Real.cos (θ (nsq c p)) * (p.1 - c.1) -
      Real.sin (θ (nsq c p)) * (p.2 - c.2) := by simp [hq, twistFun]
  have hq2 : q.2 - c.2 = Real.sin (θ (nsq c p)) * (p.1 - c.1) +
      Real.cos (θ (nsq c p)) * (p.2 - c.2) := by simp [hq, twistFun]
  have h1 := Real.sin_sq_add_cos_sq (θ (nsq c p))
  show (c.1 + (Real.cos (-θ (nsq c q)) * (q.1 - c.1) - Real.sin (-θ (nsq c q)) * (q.2 - c.2)),
    c.2 + (Real.sin (-θ (nsq c q)) * (q.1 - c.1) + Real.cos (-θ (nsq c q)) * (q.2 - c.2))) = p
  rw [hs, hq1, hq2, Real.cos_neg, Real.sin_neg]
  ext
  · simp only; linear_combination (p.1 - c.1) * h1
  · simp only; linear_combination (p.2 - c.2) * h1

lemma contDiff_twistFun (c : P2) {θ : ℝ → ℝ} (hθ : ContDiff ℝ n θ) :
    ContDiff ℝ n (twistFun c θ) := by
  have hs : ContDiff ℝ n fun p : P2 => nsq c p := by unfold nsq; fun_prop
  have ha := hθ.comp hs
  have hc := Real.contDiff_cos.comp ha
  have hn := Real.contDiff_sin.comp ha
  unfold twistFun
  apply ContDiff.prodMk
  · exact contDiff_const.add ((hc.mul (contDiff_fst.sub contDiff_const)).sub
      (hn.mul (contDiff_snd.sub contDiff_const)))
  · exact contDiff_const.add ((hn.mul (contDiff_fst.sub contDiff_const)).add
      (hc.mul (contDiff_snd.sub contDiff_const)))

/-- The twist diffeomorphism. -/
noncomputable def twist (c : P2) (θ : ℝ → ℝ) (hθ : ContDiff ℝ n θ) : PlaneDiffeo n where
  toFun := twistFun c θ
  invFun := twistFun c fun s => -θ s
  left_inv p := twistFun_neg c θ p
  right_inv p := by
    have := twistFun_neg c (fun s => -θ s) p
    simpa only [neg_neg] using this
  contDiff_toFun := contDiff_twistFun c hθ
  contDiff_invFun := contDiff_twistFun c hθ.neg

lemma twist_apply (c : P2) (θ : ℝ → ℝ) (hθ : ContDiff ℝ n θ) (p : P2) :
    twist c θ hθ p = twistFun c θ p := rfl

end PlaneDiffeo

/-! ### Bumps and contractions -/

/-- A smooth even bump: `1` on `[-R, R]`, `0` outside `(-R', R')`, nonincreasing in `|t|`. -/
noncomputable def bump (R R' t : ℝ) : ℝ := Real.smoothTransition ((R' ^ 2 - t ^ 2) / (R' ^ 2 - R ^ 2))

section Bump

variable {R R' : ℝ}

lemma bump_eq_one (hR : 0 ≤ R) (hRR : R < R') {t : ℝ} (ht : |t| ≤ R) : bump R R' t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hd : 0 < R' ^ 2 - R ^ 2 := by nlinarith
  rw [le_div_iff₀ hd, one_mul]
  have : t ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  linarith

lemma bump_eq_zero (hR : 0 ≤ R) (hRR : R < R') {t : ℝ} (ht : R' ≤ |t|) : bump R R' t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hd : 0 < R' ^ 2 - R ^ 2 := by nlinarith
  apply div_nonpos_of_nonpos_of_nonneg _ hd.le
  have : R' ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]; exact pow_le_pow_left₀ (by linarith) ht 2
  linarith

lemma bump_nonneg (t : ℝ) : 0 ≤ bump R R' t := Real.smoothTransition.nonneg _

lemma bump_le_one (t : ℝ) : bump R R' t ≤ 1 := Real.smoothTransition.le_one _

lemma contDiff_bump {n : ℕ∞} : ContDiff ℝ n (bump R R') := by
  unfold bump
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma mul_deriv_bump_nonpos (hRR : R ^ 2 < R' ^ 2) (t : ℝ) : t * deriv (bump R R') t ≤ 0 := by
  have hd : 0 < R' ^ 2 - R ^ 2 := by linarith
  have hq : HasDerivAt (fun t : ℝ => (R' ^ 2 - t ^ 2) / (R' ^ 2 - R ^ 2))
      ((-(2 * t)) / (R' ^ 2 - R ^ 2)) t := by
    have := ((hasDerivAt_pow 2 t).const_sub (R' ^ 2)).div_const (R' ^ 2 - R ^ 2)
    convert this using 2; push_cast; ring
  have hθ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((R' ^ 2 - t ^ 2) / (R' ^ 2 - R ^ 2)))
      ((R' ^ 2 - t ^ 2) / (R' ^ 2 - R ^ 2)) :=
    (Real.smoothTransition.contDiff (n := 1).differentiable one_ne_zero _).hasDerivAt
  have hb := hθ.comp t hq
  rw [show bump R R' = Real.smoothTransition ∘ fun t : ℝ => (R' ^ 2 - t ^ 2) / (R' ^ 2 - R ^ 2)
    from rfl, hb.deriv]
  have h0 := Real.smoothTransition.monotone.deriv_nonneg
    (x := (R' ^ 2 - t ^ 2) / (R' ^ 2 - R ^ 2))
  have : t * (-(2 * t) / (R' ^ 2 - R ^ 2)) ≤ 0 := by
    rw [mul_div_assoc', div_nonpos_iff]; right; constructor <;> nlinarith
  calc t * (deriv Real.smoothTransition ((R' ^ 2 - t ^ 2) / (R' ^ 2 - R ^ 2)) *
        (-(2 * t) / (R' ^ 2 - R ^ 2)))
      = deriv Real.smoothTransition ((R' ^ 2 - t ^ 2) / (R' ^ 2 - R ^ 2)) *
        (t * (-(2 * t) / (R' ^ 2 - R ^ 2))) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 this

end Bump

/-- The function `-(1 - s) χ(x - c₁) (y - c) κ(y - c)`, with `χ = bump R₁ R₁'` and
`κ = bump R R'`. -/
noncomputable def contrF (c₁ R₁ R₁' c s R R' : ℝ) (p : P2) : ℝ :=
  -(1 - s) * bump R₁ R₁' (p.1 - c₁) * ((p.2 - c) * bump R R' (p.2 - c))

/-- Parameters of a contraction: `0 ≤ R₁ < R₁'`, `0 ≤ R < R'`, `0 < s ≤ 1`. -/
structure ContrParams (R₁ R₁' s R R' : ℝ) : Prop where
  hR₁ : 0 ≤ R₁
  hR₁' : R₁ < R₁'
  hR : 0 ≤ R
  hR' : R < R'
  hs : 0 < s
  hs1 : s ≤ 1

section Contr

variable {c₁ R₁ R₁' c s R R' : ℝ}

lemma contDiff_contrF {n : ℕ∞} : ContDiff ℝ n (contrF c₁ R₁ R₁' c s R R') := by
  unfold contrF
  have h1 : ContDiff ℝ n fun p : P2 => bump R₁ R₁' (p.1 - c₁) :=
    contDiff_bump.comp (contDiff_fst.sub contDiff_const)
  have h2 : ContDiff ℝ n fun p : P2 => bump R R' (p.2 - c) :=
    contDiff_bump.comp (contDiff_snd.sub contDiff_const)
  exact (contDiff_const.mul h1).mul ((contDiff_snd.sub contDiff_const).mul h2)

lemma contrF_eq_zero_of_y (hP : ContrParams R₁ R₁' s R R') (p : P2) (hp : R' ≤ |p.2 - c|) :
    contrF c₁ R₁ R₁' c s R R' p = 0 := by
  simp [contrF, bump_eq_zero hP.hR hP.hR' hp]

lemma contrF_eq_zero_of_x (hP : ContrParams R₁ R₁' s R R') (p : P2) (hp : R₁' ≤ |p.1 - c₁|) :
    contrF c₁ R₁ R₁' c s R R' p = 0 := by
  simp [contrF, bump_eq_zero hP.hR₁ hP.hR₁' hp]

lemma contrF_far (hP : ContrParams R₁ R₁' s R R') (p : P2) (hp : |c| + R' ≤ |p.2|) :
    contrF c₁ R₁ R₁' c s R R' p = 0 :=
  contrF_eq_zero_of_y hP p (by
    have := abs_sub_abs_le_abs_sub p.2 c; linarith)

lemma one_add_deriv_contrF_pos (hP : ContrParams R₁ R₁' s R R') (x y : ℝ) :
    0 < 1 + deriv (fun y => contrF c₁ R₁ R₁' c s R R' (x, y)) y := by
  have hb : Differentiable ℝ (bump R R') := (contDiff_bump (n := 1)).differentiable one_ne_zero
  have hg : HasDerivAt (fun y : ℝ => (y - c) * bump R R' (y - c))
      (1 * bump R R' (y - c) + (y - c) * deriv (bump R R') (y - c)) y := by
    have h1 : HasDerivAt (fun y : ℝ => y - c) 1 y := (hasDerivAt_id y).sub_const c
    have h2 : HasDerivAt (fun y : ℝ => bump R R' (y - c)) (deriv (bump R R') (y - c)) y := by
      have := (hb (y - c)).hasDerivAt.comp y h1
      rw [mul_one] at this
      exact this
    exact h1.mul h2
  have hd : HasDerivAt (fun y => contrF c₁ R₁ R₁' c s R R' (x, y))
      (-(1 - s) * bump R₁ R₁' (x - c₁) *
        (1 * bump R R' (y - c) + (y - c) * deriv (bump R R') (y - c))) y :=
    hg.const_mul (-(1 - s) * bump R₁ R₁' (x - c₁))
  rw [hd.deriv]
  have hχ0 := bump_nonneg (R := R₁) (R' := R₁') (x - c₁)
  have hχ1 := bump_le_one (R := R₁) (R' := R₁') (x - c₁)
  have hκ0 := bump_nonneg (R := R) (R' := R') (y - c)
  have hκ1 := bump_le_one (R := R) (R' := R') (y - c)
  have hsq : R ^ 2 < R' ^ 2 := by nlinarith [hP.hR, hP.hR']
  have hk' := mul_deriv_bump_nonpos hsq (y - c)
  have hs := hP.hs
  have hs1 := hP.hs1
  have h1 : (1 - s) * bump R₁ R₁' (x - c₁) * bump R R' (y - c) ≤ 1 - s := by
    have : bump R₁ R₁' (x - c₁) * bump R R' (y - c) ≤ 1 :=
      (mul_le_of_le_one_left hκ0 hχ1).trans hκ1
    nlinarith
  have h2 : 0 ≤ (1 - s) * bump R₁ R₁' (x - c₁) * -((y - c) * deriv (bump R R') (y - c)) := by
    apply mul_nonneg (mul_nonneg (by linarith) hχ0); linarith
  nlinarith

end Contr

namespace PlaneDiffeo

variable {n : ℕ∞} {c₁ R₁ R₁' c s R R' : ℝ}

/-- The vertical contraction: `y ↦ c + s (y - c)` on the box `|x - c₁| ≤ R₁, |y - c| ≤ R`, the
identity when `|x - c₁| ≥ R₁'` or `|y - c| ≥ R'`. -/
noncomputable def vContr (hn : 1 ≤ n) (c₁ R₁ R₁' c s R R' : ℝ)
    (hP : ContrParams R₁ R₁' s R R') : PlaneDiffeo n :=
  vert (contrF c₁ R₁ R₁' c s R R') contDiff_contrF hn (|c| + R') (contrF_far hP)
    (one_add_deriv_contrF_pos hP)

lemma vContr_apply' (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') (p : P2) :
    vContr hn c₁ R₁ R₁' c s R R' hP p = (p.1, p.2 + contrF c₁ R₁ R₁' c s R R' p) := rfl

lemma vContr_fst (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') (p : P2) :
    (vContr hn c₁ R₁ R₁' c s R R' hP p).1 = p.1 := rfl

lemma vContr_of_far (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') {p : P2}
    (hp : R₁' ≤ |p.1 - c₁|) : vContr hn c₁ R₁ R₁' c s R R' hP p = p := by
  rw [vContr_apply', contrF_eq_zero_of_x hP p hp, add_zero]

lemma vContr_of_far_y (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') {p : P2}
    (hp : R' ≤ |p.2 - c|) : vContr hn c₁ R₁ R₁' c s R R' hP p = p := by
  rw [vContr_apply', contrF_eq_zero_of_y hP p hp, add_zero]

lemma vContr_apply (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') {p : P2}
    (hx : |p.1 - c₁| ≤ R₁) (hy : |p.2 - c| ≤ R) :
    vContr hn c₁ R₁ R₁' c s R R' hP p = (p.1, c + s * (p.2 - c)) := by
  rw [vContr_apply']
  simp only [contrF, bump_eq_one hP.hR₁ hP.hR₁' hx, bump_eq_one hP.hR hP.hR' hy]
  congr 1; ring

/-- The horizontal contraction: `x ↦ c + s (x - c)` on the box `|y - c₁| ≤ R₁, |x - c| ≤ R`,
the identity when `|y - c₁| ≥ R₁'` or `|x - c| ≥ R'`. -/
noncomputable def hContr (hn : 1 ≤ n) (c₁ R₁ R₁' c s R R' : ℝ)
    (hP : ContrParams R₁ R₁' s R R') : PlaneDiffeo n :=
  swap.trans ((vContr hn c₁ R₁ R₁' c s R R' hP).trans swap)

lemma hContr_apply' (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') (p : P2) :
    hContr hn c₁ R₁ R₁' c s R R' hP p = (p.1 + contrF c₁ R₁ R₁' c s R R' (p.2, p.1), p.2) := rfl

lemma hContr_snd (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') (p : P2) :
    (hContr hn c₁ R₁ R₁' c s R R' hP p).2 = p.2 := rfl

lemma hContr_of_far (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') {p : P2}
    (hp : R₁' ≤ |p.2 - c₁|) : hContr hn c₁ R₁ R₁' c s R R' hP p = p := by
  rw [hContr_apply', contrF_eq_zero_of_x hP (p.2, p.1) hp, add_zero]

lemma hContr_of_far_x (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') {p : P2}
    (hp : R' ≤ |p.1 - c|) : hContr hn c₁ R₁ R₁' c s R R' hP p = p := by
  rw [hContr_apply', contrF_eq_zero_of_y hP (p.2, p.1) hp, add_zero]

lemma hContr_apply (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') {p : P2}
    (hy : |p.2 - c₁| ≤ R₁) (hx : |p.1 - c| ≤ R) :
    hContr hn c₁ R₁ R₁' c s R R' hP p = (c + s * (p.1 - c), p.2) := by
  rw [hContr_apply']
  simp only [contrF, bump_eq_one hP.hR₁ hP.hR₁' hy, bump_eq_one hP.hR hP.hR' hx]
  congr 1; ring

/-- The horizontal expansion `x ↦ c + (x - c) / s`, the inverse of `hContr`. -/
noncomputable def hExp (hn : 1 ≤ n) (c₁ R₁ R₁' c s R R' : ℝ)
    (hP : ContrParams R₁ R₁' s R R') : PlaneDiffeo n :=
  (hContr hn c₁ R₁ R₁' c s R R' hP).symm

lemma hExp_snd (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') (p : P2) :
    (hExp hn c₁ R₁ R₁' c s R R' hP p).2 = p.2 := by
  have := hContr_snd hn hP (c₁ := c₁) (c := c) (hExp hn c₁ R₁ R₁' c s R R' hP p)
  rw [hExp, apply_symm_apply] at this
  exact this.symm

lemma hExp_of_far (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') {p : P2}
    (hp : R₁' ≤ |p.2 - c₁|) : hExp hn c₁ R₁ R₁' c s R R' hP p = p :=
  symm_eq_of_apply_eq _ (hContr_of_far hn hP hp)

lemma hExp_of_far_x (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') {p : P2}
    (hp : R' ≤ |p.1 - c|) : hExp hn c₁ R₁ R₁' c s R R' hP p = p :=
  symm_eq_of_apply_eq _ (hContr_of_far_x hn hP hp)

lemma hExp_apply (hn : 1 ≤ n) (hP : ContrParams R₁ R₁' s R R') {p : P2}
    (hy : |p.2 - c₁| ≤ R₁) (hx : |p.1 - c| ≤ s * R) :
    hExp hn c₁ R₁ R₁' c s R R' hP p = (c + (p.1 - c) / s, p.2) := by
  rw [hExp, symm_apply_eq]
  have hs := hP.hs
  have hx' : |(c + (p.1 - c) / s, p.2).1 - c| ≤ R := by
    simp only [add_sub_cancel_left, abs_div, abs_of_pos hs]
    rw [div_le_iff₀ hs]; linarith
  rw [hContr_apply hn hP (p := (c + (p.1 - c) / s, p.2)) hy hx']
  ext
  · simp only; field_simp; ring
  · rfl

end PlaneDiffeo

end FiniteOrderMixing
