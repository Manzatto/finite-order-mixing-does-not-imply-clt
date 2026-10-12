import FiniteOrderMixing.Realisation.WanderBox

/-!
# The perturbed horseshoe and the orbit of the wandering box

`T = T₀ ∘ P`, where `T₀` is the planar horseshoe model and `P` the bump perturbation with
translations `e_k` at the exits `ctr k`.  Every point of the initial box visits the box
`Box k j` at time `tt k + j`.
-/

open Set Filter Topology

namespace FiniteOrderMixing

namespace PlaneDiffeo

variable {n : ℕ∞} (hn : 1 ≤ n) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)

lemma model_strip (b : Bool) {x y : ℝ} (hx0 : 2 * bit b / 3 - 1 / 100 ≤ x)
    (hx1 : x ≤ (1 + 2 * bit b) / 3 + 1 / 100) (hy0 : -1 / 4 ≤ y) (hy1 : y ≤ 5 / 4) :
    model hn γ hγ hγ1 (x, y) = (3 * x - 2 * bit b, (y + 2 * bit b) / 3) := by
  cases b
  · simp only [bit, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_div] at hx0 hx1 ⊢
    rw [model_left hn hγ hγ1 (by linarith) (by linarith) hy0 hy1]
    simp
  · simp only [bit, ↓reduceIte, mul_one] at hx0 hx1 ⊢
    rw [model_right hn hγ hγ1 (by linarith) (by linarith) hy0 hy1]

end PlaneDiffeo

namespace Itin

variable (A : Itin)

/-- The majorant `u_k = 100^r 2^{-H₀} (k+2)^{-2}` of `|e_k| ρ_k^{-r}`. -/
noncomputable def u (k : ℕ) : ℝ := 100 ^ A.r / 2 ^ A.H₀ / ((k : ℝ) + 2) ^ 2

lemma sum_inv_sq_le (N : ℕ) :
    ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 2) ^ 2 ≤ 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : 1 / ((N : ℝ) + 2) ^ 2 ≤ 1 / (N + 1) - 1 / ((N + 1 : ℕ) + 1) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

lemma summable_inv_sq : Summable fun k : ℕ => 1 / ((k : ℝ) + 2) ^ 2 := by
  have := (summable_nat_add_iff 2).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  simpa using this

lemma tsum_inv_sq_le : ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2 ≤ 1 :=
  Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun N =>
    (sum_inv_sq_le N).trans (by
      have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith)

lemma abs_e_mul_le (k : ℕ) : |A.e k| * (ρw k)⁻¹ ^ A.r ≤ A.u k := by
  set X : ℝ := (k : ℝ) + 2 with hX
  have hXpos : 0 < X := by positivity
  set L := Nat.log 2 (k + 2)
  have hL : (X : ℝ) ≤ 2 ^ (L + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (k + 2)
    rw [hX]; exact_mod_cast this.le
  have h1 : (1 / 3 : ℝ) ^ A.hd (k + 1) ≤ (1 / 2) ^ A.hd (k + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h2 : (1 / 2 : ℝ) ^ A.hd (k + 1) ≤
      (1 / 2) ^ A.H₀ * ((1 / 2) ^ (L + 1)) ^ (2 * A.r + 2) := by
    calc (1 / 2 : ℝ) ^ A.hd (k + 1) ≤
        (1 / 2) ^ ((2 * A.r + 2) * (L + 1) + A.H₀) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by simp only [hd, L]; omega)
      _ = _ := by
        rw [pow_add, Nat.mul_comm (2 * A.r + 2) (L + 1), ← pow_mul, mul_comm]
  have h3 : ((1 / 2 : ℝ) ^ (L + 1)) ^ (2 * A.r + 2) ≤ (1 / X) ^ (2 * A.r + 2) := by
    gcongr
    rw [one_div_pow, one_div, one_div]; exact inv_anti₀ hXpos hL
  have he : |A.e k| ≤ (1 / 2) ^ A.H₀ * ((1 / X) ^ (2 * A.r + 2)) :=
    calc |A.e k| ≤ (1 / 3) ^ A.hd (k + 1) := A.abs_e_le k
      _ ≤ (1 / 2) ^ A.hd (k + 1) := h1
      _ ≤ (1 / 2) ^ A.H₀ * ((1 / 2) ^ (L + 1)) ^ (2 * A.r + 2) := h2
      _ ≤ (1 / 2) ^ A.H₀ * ((1 / X) ^ (2 * A.r + 2)) := by gcongr
  have hρ : (ρw k)⁻¹ = 100 * X ^ 2 := by unfold ρw; rw [one_div, inv_inv]
  rw [hρ]
  calc |A.e k| * (100 * X ^ 2) ^ A.r ≤ (1 / 2) ^ A.H₀ * ((1 / X) ^ (2 * A.r + 2)) *
        (100 * X ^ 2) ^ A.r := by gcongr
    _ = A.u k := by
      unfold u; rw [← hX]
      rw [mul_pow, ← pow_mul, one_div_pow, one_div_pow]
      field_simp
      ring

lemma pertHyp (hH : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀) : PertHyp A.r A.e ρw A.ctr A.u where
  ρ_pos := ρw_pos
  ρ_le k := (ρw_le k).trans (by norm_num)
  c_snd k := by
    have := A.η_mem k; simp only [ctr]; rw [abs_le]; constructor <;> linarith [this.1, this.2]
  summable := by
    have : A.u = fun k : ℕ => 100 ^ A.r / 2 ^ A.H₀ * (1 / ((k : ℝ) + 2) ^ 2) := by
      funext k; unfold u; ring
    rw [this]
    exact summable_inv_sq.mul_left _
  le_u := A.abs_e_mul_le
  small := by
    have hB := bumpBound_pos A.r
    have h1 : ∑' k, A.u k = 100 ^ A.r / 2 ^ A.H₀ * ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2 := by
      rw [← tsum_mul_left]; unfold u; congr 1; funext k; ring
    rw [h1]
    have h2 := tsum_inv_sq_le
    have h3 : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2 := tsum_nonneg fun _ => by positivity
    have h4 : bumpBound A.r * (100 ^ A.r / 2 ^ A.H₀) ≤ 1 / 4 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; linarith
    calc bumpBound A.r * (100 ^ A.r / 2 ^ A.H₀ * ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2)
        = bumpBound A.r * (100 ^ A.r / 2 ^ A.H₀) * ∑' k : ℕ, 1 / ((k : ℝ) + 2) ^ 2 := by ring
      _ ≤ 1 / 4 * 1 := by gcongr
      _ ≤ 1 / 2 := by norm_num

variable (hr : 1 ≤ A.r) (hH : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀)

lemma γ_le_one : A.γ ≤ 1 := A.γ_le.trans (by norm_num)

lemma one_le_r (h : 1 ≤ A.r) : (1 : ℕ∞) ≤ (A.r : ℕ∞) := by exact_mod_cast h

/-- The planar horseshoe model with the parameter `γ` of `A`. -/
noncomputable def T₀ (h : 1 ≤ A.r) : PlaneDiffeo A.r :=
  PlaneDiffeo.model (n := A.r) (A.one_le_r h) A.γ A.γ_pos A.γ_le_one

/-- The perturbed horseshoe `T = T₀ ∘ P`. -/
noncomputable def T (h : 1 ≤ A.r) (h' : 4 * bumpBound A.r * 100 ^ A.r ≤ 2 ^ A.H₀) :
    PlaneDiffeo A.r :=
  ((A.pertHyp h').diffeo h).trans (A.T₀ h)

lemma T_apply (z : P2) : A.T hr hH z = A.T₀ hr (z.1, z.2 + pertF A.e ρw A.ctr z) := rfl

/-- `T = T₀` off the gap strip. -/
lemma T_eq_model {z : P2} (hz : 1 / 8 ≤ |z.1 - 1 / 2|) :
    A.T hr hH z = A.T₀ hr z := by
  rw [T_apply, pertF_eq_zero (A.pertHyp hH) fun k => Or.inl ?_, add_zero]
  · have := ζw_pos k; have := ζw_le k; have := ρw_le k
    have := abs_sub_abs_le_abs_sub (z.1 - 1 / 2) (ζw k)
    rw [abs_of_pos (ζw_pos k)] at this
    rw [show z.1 - (A.ctr k).1 = z.1 - 1 / 2 - ζw k by simp [ctr]; ring]
    linarith

lemma T_far {z : P2} (hz : PlaneDiffeo.Far z) : A.T hr hH z = z := by
  have hF : pertF A.e ρw A.ctr z = 0 := by
    rcases hz with h | h
    · apply pertF_eq_zero (A.pertHyp hH); intro k; left
      have := ζw_pos k; have := ζw_le k; have := ρw_le k
      have h2 : |1 / 2 + ζw k| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have := abs_sub_abs_le_abs_sub z.1 (1 / 2 + ζw k)
      simp only [ctr]; linarith
    · exact pertF_far (A.pertHyp hH) (by linarith)
  rw [T_apply, hF, add_zero]
  exact PlaneDiffeo.model_far _ _ _ hz

/-! ### One step of the box -/

lemma step_strip {k j : ℕ} (hj : j < A.nb k) {z : P2} (hz : z ∈ A.Box k j) :
    A.T hr hH z ∈ A.Box k (j + 1) := by
  obtain ⟨x, y⟩ := z
  obtain ⟨hz1, hz2⟩ := hz
  simp only at hz1 hz2
  set b := A.word k j with hb
  have hm := A.xc_margin hj
  have hw : 3 ^ j * A.pp k ≤ 23 / 48 / 3 ^ (A.nb k - j) := by
    obtain ⟨hp, -, h3, -⟩ := A.sz_bound k
    rw [le_div_iff₀ (by positivity), mul_right_comm, ← pow_add,
      show j + (A.nb k - j) = A.nb k by omega]
    refine h3.trans ?_
    have : (1 / 5 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  rw [abs_le] at hz1 hz2
  have hy := A.yc_mem k j
  have hh := A.height_le k j
  have hpow : (1 / 5 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hx0 : 2 * bit b / 3 ≤ x := by linarith [hm.1, hz1.1, hw]
  have hx1 : x ≤ (1 + 2 * bit b) / 3 := by linarith [hm.2, hz1.2, hw]
  have hfar : 1 / 6 ≤ |(x, y).1 - 1 / 2| := by
    simp only
    rcases hbv : b with _ | _
    · rw [hbv] at hx1; simp only [bit, Bool.false_eq_true, ↓reduceIte] at hx1
      rw [abs_sub_comm, le_abs]; left; linarith
    · rw [hbv] at hx0; simp only [bit, ↓reduceIte] at hx0
      rw [le_abs]; left; linarith
  rw [A.T_eq_model hr hH (le_trans (by norm_num) hfar), T₀,
    PlaneDiffeo.model_strip _ _ _ b (by linarith) (by linarith)
    (by linarith [hy.1, hy.2, hz2.1, hz2.2]) (by linarith [hy.1, hy.2, hz2.1, hz2.2])]
  have ex : A.xc k j = (A.xc k (j + 1) + 2 * bit b) / 3 := A.xc_succ hj
  have ey : A.yc k (j + 1) = (A.yc k j + 2 * bit b) / 3 := A.yc_succ k j
  refine ⟨?_, ?_⟩
  · simp only
    rw [show 3 * x - 2 * bit b - A.xc k (j + 1) = 3 * (x - A.xc k j) by rw [ex]; ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), pow_succ]
    calc 3 * |x - A.xc k j| ≤ 3 * (3 ^ j * A.pp k) := by gcongr; exact abs_le.2 hz1
      _ = 3 ^ j * 3 * A.pp k := by ring
  · simp only
    rw [show (y + 2 * bit b) / 3 - A.yc k (j + 1) = (y - A.yc k j) / 3 by rw [ey]; ring,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3), pow_succ, ← div_div]
    gcongr
    rw [abs_le]; constructor <;> linarith

lemma step_gap {k : ℕ} {z : P2} (hz : z ∈ A.Box k (A.nb k)) : A.T hr hH z ∈ A.Box (k + 1) 0 := by
  obtain ⟨x, y⟩ := z
  obtain ⟨hz1, hz2⟩ := hz
  simp only at hz1 hz2
  rw [A.xc_nb] at hz1
  change |y - A.η k| ≤ A.qq k / 3 ^ A.nb k at hz2
  have hw := A.width_le (k := k) (j := A.nb k) le_rfl
  have hh := A.height_le k (A.nb k)
  have hρ := eps_le_ρw k
  have hζ := ζw_pos k; have hζ' := ζw_le k; have hρk := ρw_le k
  have hη := A.η_mem k
  have hη0 := hη.1
  have hη1 := hη.2
  have hρ0 := ρw_pos k
  have hpow : (1 / 5 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he := A.abs_e_le k
  have he3 : (1 / 3 : ℝ) ^ A.hd (k + 1) ≤ 1 / 81 := by
    have : 4 ≤ A.hd (k + 1) := by simp only [hd]; nlinarith [Nat.zero_le (Nat.log 2 (k + 2))]
    calc (1 / 3 : ℝ) ^ A.hd (k + 1) ≤ (1 / 3) ^ 4 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) this
      _ = 1 / 81 := by norm_num
  have hF : pertF A.e ρw A.ctr (x, y) = A.e k := by
    apply pertF_eq (A.pertHyp hH)
    · simp only [ctr]; linarith
    · simp only [ctr]; linarith
    · intro i hi
      left
      have hs := ρw_add_le hi
      have := abs_sub_abs_le_abs_sub (ζw i - ζw k) (x - (1 / 2 + ζw k))
      simp only [ctr]
      rw [show x - (1 / 2 + ζw i) = -((ζw i - ζw k) - (x - (1 / 2 + ζw k))) by ring, abs_neg]
      linarith
  rw [T_apply, hF]
  simp only
  rw [abs_le] at hz1 hz2 he
  rw [T₀, PlaneDiffeo.model_gap _ _ _ (A.γ_le.trans (by norm_num)) (by linarith) (by linarith)
    (by linarith) (by linarith)]
  refine ⟨?_, ?_⟩
  · simp only [pow_zero, one_mul]
    rw [show A.xc (k + 1) 0 = 1 - A.η k - A.e k by unfold e; ring]
    change |1 - (y + A.e k) - (1 - A.η k - A.e k)| ≤ A.qq k / 3 ^ A.nb k
    rw [show 1 - (y + A.e k) - (1 - A.η k - A.e k) = -(y - A.η k) by ring, abs_neg, abs_le]
    exact ⟨by linarith, by linarith⟩
  · simp only [pow_zero, div_one]
    change |1 / 2 + A.γ * (x - 1 / 2) - (1 / 2 + A.γ * ζw k)| ≤ A.γ * 3 ^ A.nb k * A.pp k
    rw [show 1 / 2 + A.γ * (x - 1 / 2) - (1 / 2 + A.γ * ζw k) = A.γ * (x - (1 / 2 + ζw k)) by ring,
      abs_mul, abs_of_pos A.γ_pos, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) A.γ_pos.le

/-- The orbit of the initial box. -/
lemma orbit_box {z : P2} (hz : z ∈ A.Box 0 0) (k j : ℕ) (hj : j ≤ A.nb k) :
    (A.T hr hH)^[A.tt k + j] z ∈ A.Box k j := by
  induction k generalizing j with
  | zero =>
    induction j with
    | zero => simpa [tt] using hz
    | succ j ih =>
      rw [show A.tt 0 + (j + 1) = (A.tt 0 + j) + 1 by ring, Function.iterate_succ_apply']
      exact A.step_strip hr hH (by omega) (ih (by omega))
  | succ k ihk =>
    induction j with
    | zero =>
      rw [add_zero, tt_succ, Function.iterate_succ_apply']
      exact A.step_gap hr hH (ihk _ le_rfl)
    | succ j ih =>
      rw [show A.tt (k + 1) + (j + 1) = (A.tt (k + 1) + j) + 1 by ring, Function.iterate_succ_apply']
      exact A.step_strip hr hH (by omega) (ih (by omega))

/-! ### The horseshoe -/

lemma T_pcod (ω : Config) : A.T hr hH (pcod ω) = pcod (shift ω) := by
  have hx := codX_eq ω
  have hX := codX_mem (shift ω)
  have hY := codY_mem ω
  have hs := phi_strip (ω 0) (δ := 0) (z := codX (shift ω)) (by linarith [hX.1]) (by linarith [hX.2])
  rw [← hx] at hs
  have hbit0 := bit_nonneg (ω 0); have hbit1 := bit_le_one (ω 0)
  have hfar : 1 / 6 ≤ |(pcod ω).1 - 1 / 2| := by
    simp only [pcod]
    rcases hb : ω 0 with _ | _
    · rw [hb] at hs; simp only [bit, Bool.false_eq_true, ↓reduceIte] at hs
      rw [abs_sub_comm, le_abs]; left; linarith [hs.2]
    · rw [hb] at hs; simp only [bit, ↓reduceIte] at hs
      rw [le_abs]; left; linarith [hs.1]
  rw [A.T_eq_model hr hH (le_trans (by norm_num) hfar), T₀]
  simp only [pcod]
  rw [PlaneDiffeo.model_strip _ _ _ (ω 0) (by linarith [hs.1]) (by linarith [hs.2])
    (by linarith [hY.1]) (by linarith [hY.2]), codY_shift]
  ext
  · simp only; rw [hx, phi]; ring
  · simp only [phi]

lemma horseshoeCoding : HorseshoeCoding (A.T hr hH) pcod where
  continuous := continuous_pcod
  injective := pcod_injective
  conj ω := (A.T_pcod hr hH ω).symm
  holder := ⟨1, 1 / 3, by norm_num, by norm_num, dist_pcod_le⟩

end Itin

end FiniteOrderMixing
