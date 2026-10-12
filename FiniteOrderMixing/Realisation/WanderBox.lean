import FiniteOrderMixing.Realisation.Itinerary
import FiniteOrderMixing.Realisation.PlanePerturb

/-!
# Positions and sizes of the wandering box

The box of block `k` at step `j` is centred at `(xc k j, yc k j)`, with half-sides
`3^j pp k` and `qq k / 3^j`.  At the end of block `k` it is centred at
`ctr k = (1/2 + ζ_k, η_k)` in the gap strip, where the `k`-th bump translates it by `(0, e_k)`.
-/

open Set Filter Topology

namespace FiniteOrderMixing

/-- The horizontal offsets `ζ_k` of the exits. -/
noncomputable def ζw (k : ℕ) : ℝ := 1 / (48 * ((k : ℝ) + 1))

/-- The radii `ρ_k` of the bumps. -/
noncomputable def ρw (k : ℕ) : ℝ := 1 / (100 * ((k : ℝ) + 2) ^ 2)

lemma ζw_pos (k : ℕ) : 0 < ζw k := by unfold ζw; positivity

lemma ζw_le (k : ℕ) : ζw k ≤ 1 / 48 := by
  unfold ζw
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma ρw_pos (k : ℕ) : 0 < ρw k := by unfold ρw; positivity

lemma ρw_le (k : ℕ) : ρw k ≤ 1 / 400 := by
  unfold ρw
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma ρw_add_le_of_lt {j k : ℕ} (h : j < k) : ρw j + ρw k ≤ ζw j - ζw k := by
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hρ : ρw k ≤ ρw j := by
    unfold ρw
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hζ : ζw j - ζw (j + 1) ≤ ζw j - ζw k := by
    have : ζw k ≤ ζw (j + 1) := by
      unfold ζw
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; nlinarith
    linarith
  refine le_trans ?_ hζ
  have e1 : ζw j - ζw (j + 1) = 1 / (48 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    unfold ζw; push_cast; field_simp; ring
  rw [e1]
  calc ρw j + ρw k ≤ 2 * ρw j := by linarith
    _ = 1 / (50 * ((j : ℝ) + 2) ^ 2) := by unfold ρw; field_simp; ring
    _ ≤ 1 / (48 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
        apply one_div_le_one_div_of_le (by positivity); nlinarith

lemma ρw_add_le {j k : ℕ} (h : j ≠ k) : ρw j + ρw k ≤ |ζw j - ζw k| := by
  rcases lt_or_gt_of_ne h with h | h
  · exact (ρw_add_le_of_lt h).trans (le_abs_self _)
  · rw [abs_sub_comm, add_comm]; exact (ρw_add_le_of_lt h).trans (le_abs_self _)

lemma sq_le_five_pow (k : ℕ) : ((k : ℝ) + 2) ^ 2 ≤ 5 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h5 : (5 : ℝ) ^ (k + 1 + 1) = 5 * 5 ^ (k + 1) := by rw [pow_succ]; ring
    rw [h5]; push_cast
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith

namespace Itin

variable (A : Itin)

/-- The contraction `γ = 3^{-D}/81` of the gap map. -/
noncomputable def γ : ℝ := 1 / (81 * 3 ^ A.D)

lemma γ_pos : 0 < A.γ := by unfold γ; positivity

lemma γ_le : A.γ ≤ 1 / 81 := by
  unfold γ
  apply one_div_le_one_div_of_le (by norm_num)
  have : (1 : ℝ) ≤ 3 ^ A.D := one_le_pow₀ (by norm_num)
  linarith

/-- The initial vertical half-side `ε' = ε 3^{-D} / 15`, `ε = 1/1000`. -/
noncomputable def ε' : ℝ := 1 / 1000 / (15 * 3 ^ A.D)

/-- The centre `xc k j` (horizontal) of the box. -/
noncomputable def xc (k j : ℕ) : ℝ := phis (fun i => A.word k (j + i)) (A.nb k - j) (1 / 2 + ζw k)

/-- The entry heights `υ_k`. -/
noncomputable def υ : ℕ → ℝ
  | 0 => 1 / 2
  | k + 1 => 1 / 2 + A.γ * ζw k

/-- The centre `yc k j` (vertical) of the box. -/
noncomputable def yc (k j : ℕ) : ℝ := psis (A.word k) j (A.υ k)

/-- The exit height `η_k`. -/
noncomputable def η (k : ℕ) : ℝ := A.yc k (A.nb k)

/-- The translation `e_k` of the `k`-th bump. -/
noncomputable def e (k : ℕ) : ℝ := 1 - A.η k - A.xc (k + 1) 0

/-- The centre of the `k`-th bump. -/
noncomputable def ctr (k : ℕ) : P2 := (1 / 2 + ζw k, A.η k)

/-- The half-sides `(pp k, qq k)` of the box at the start of block `k`. -/
noncomputable def sz : ℕ → ℝ × ℝ
  | 0 => (1 / 1000 / 3 ^ A.nb 0, A.ε')
  | k + 1 => ((sz k).2 / 3 ^ A.nb k, A.γ * 3 ^ A.nb k * (sz k).1)

noncomputable def pp (k : ℕ) : ℝ := (A.sz k).1
noncomputable def qq (k : ℕ) : ℝ := (A.sz k).2

/-- The box of block `k` at step `j`. -/
def Box (k j : ℕ) : Set P2 :=
  {z | |z.1 - A.xc k j| ≤ 3 ^ j * A.pp k ∧ |z.2 - A.yc k j| ≤ A.qq k / 3 ^ j}

/-! ### Positions -/

lemma half_add_ζw_mem (k : ℕ) : 23 / 48 ≤ 1 / 2 + ζw k ∧ 1 / 2 + ζw k ≤ 1 - 23 / 48 := by
  have := ζw_pos k; have := ζw_le k; constructor <;> linarith

lemma υ_mem (k : ℕ) : A.υ k ∈ Icc (0 : ℝ) 1 := by
  rcases k with _ | k
  · simp [υ]; norm_num
  · simp only [υ]
    have := ζw_pos k; have := ζw_le k; have := A.γ_pos; have := A.γ_le
    constructor <;> nlinarith

lemma xc_mem (k j : ℕ) : A.xc k j ∈ Icc (0 : ℝ) 1 :=
  phis_mem _ _ ⟨by linarith [(half_add_ζw_mem k).1], by linarith [(half_add_ζw_mem k).2]⟩

lemma yc_mem (k j : ℕ) : A.yc k j ∈ Icc (0 : ℝ) 1 := psis_mem _ _ (A.υ_mem k)

lemma η_mem (k : ℕ) : A.η k ∈ Icc (0 : ℝ) 1 := A.yc_mem k _

lemma xc_succ {k j : ℕ} (hj : j < A.nb k) : A.xc k j = phi (A.word k j) (A.xc k (j + 1)) := by
  unfold xc
  rw [show A.nb k - j = (A.nb k - (j + 1)) + 1 by omega, phis_succ]
  simp only [add_zero]
  congr 2
  funext i; congr 1; omega

lemma yc_succ (k j : ℕ) : A.yc k (j + 1) = phi (A.word k j) (A.yc k j) := rfl

lemma xc_nb (k : ℕ) : A.xc k (A.nb k) = 1 / 2 + ζw k := by
  unfold xc; rw [Nat.sub_self]; rfl

lemma yc_zero (k : ℕ) : A.yc k 0 = A.υ k := rfl

/-- The box stays well inside the strip of its next symbol. -/
lemma xc_margin {k j : ℕ} (hj : j < A.nb k) :
    2 * bit (A.word k j) / 3 + 23 / 48 / 3 ^ (A.nb k - j) ≤ A.xc k j ∧
      A.xc k j ≤ (1 + 2 * bit (A.word k j)) / 3 - 23 / 48 / 3 ^ (A.nb k - j) := by
  rw [A.xc_succ hj]
  have hm := phis_margin (fun i => A.word k (j + 1 + i)) (A.nb k - (j + 1))
    (half_add_ζw_mem k).1 (half_add_ζw_mem k).2
  have h := phi_strip (A.word k j) hm.1 hm.2
  have e : (23 / 48 / 3 ^ (A.nb k - (j + 1)) / 3 : ℝ) = 23 / 48 / 3 ^ (A.nb k - j) := by
    rw [div_div, ← pow_succ, show A.nb k - (j + 1) + 1 = A.nb k - j by omega]
  rw [e] at h
  exact h

/-! ### Sizes -/

lemma sz_bound (k : ℕ) : 0 ≤ A.pp k ∧ 0 ≤ A.qq k ∧
    3 ^ A.nb k * A.pp k ≤ 1 / 1000 * (1 / 5) ^ k ∧ A.qq k ≤ A.ε' * (1 / 5) ^ k := by
  induction k with
  | zero =>
    simp only [pp, qq, sz, pow_zero, mul_one, le_refl, and_true]
    refine ⟨by positivity, by unfold ε'; positivity, ?_⟩
    rw [mul_div_cancel₀ _ (by positivity)]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have hγ := A.γ_pos
    have hD : (3 : ℝ) ^ A.nb (k + 1) ≤ 3 ^ A.D * 3 ^ A.nb k := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by have := A.nb_succ_le k; omega)
    simp only [pp, qq, sz] at *
    refine ⟨by positivity, by positivity, ?_, ?_⟩
    · calc 3 ^ A.nb (k + 1) * ((A.sz k).2 / 3 ^ A.nb k)
          ≤ 3 ^ A.D * 3 ^ A.nb k * ((A.sz k).2 / 3 ^ A.nb k) := by gcongr
        _ = 3 ^ A.D * (A.sz k).2 := by field_simp
        _ ≤ 3 ^ A.D * (A.ε' * (1 / 5) ^ k) := by gcongr
        _ = 1 / 1000 * (1 / 5) ^ (k + 1) * (5 / 15) := by unfold ε'; field_simp; ring
        _ ≤ 1 / 1000 * (1 / 5) ^ (k + 1) := by
          have : (0 : ℝ) ≤ 1 / 1000 * (1 / 5) ^ (k + 1) := by positivity
          nlinarith
    · calc A.γ * 3 ^ A.nb k * (A.sz k).1 = A.γ * (3 ^ A.nb k * (A.sz k).1) := by ring
        _ ≤ A.γ * (1 / 1000 * (1 / 5) ^ k) := by gcongr
        _ = A.ε' * (1 / 5) ^ (k + 1) * (75 / 81) := by unfold γ ε'; field_simp; ring
        _ ≤ A.ε' * (1 / 5) ^ (k + 1) := by
          have : (0 : ℝ) ≤ A.ε' * (1 / 5) ^ (k + 1) := by unfold ε'; positivity
          nlinarith

lemma ε'_le : A.ε' ≤ 1 / 1000 := by
  unfold ε'
  rw [div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ 3 ^ A.D := one_le_pow₀ (by norm_num)
  nlinarith

/-- The horizontal half-side of the box never exceeds `ε 5^{-k}`. -/
lemma width_le {k j : ℕ} (hj : j ≤ A.nb k) : 3 ^ j * A.pp k ≤ 1 / 1000 * (1 / 5) ^ k := by
  obtain ⟨h1, -, h3, -⟩ := A.sz_bound k
  refine le_trans ?_ h3
  gcongr
  · norm_num

/-- The vertical half-side of the box never exceeds `ε 5^{-k}`. -/
lemma height_le (k j : ℕ) : A.qq k / 3 ^ j ≤ 1 / 1000 * (1 / 5) ^ k := by
  obtain ⟨-, h2, -, h4⟩ := A.sz_bound k
  calc A.qq k / 3 ^ j ≤ A.qq k := div_le_self h2 (one_le_pow₀ (by norm_num))
    _ ≤ A.ε' * (1 / 5) ^ k := h4
    _ ≤ 1 / 1000 * (1 / 5) ^ k := by gcongr; exact A.ε'_le

lemma eps_le_ρw (k : ℕ) : 1 / 1000 * (1 / 5 : ℝ) ^ k ≤ ρw k / 2 := by
  have h := sq_le_five_pow k
  have h5 : (5 : ℝ) ^ (k + 1) = 5 * 5 ^ k := by rw [pow_succ]; ring
  have hp : (0 : ℝ) < 5 ^ k := by positivity
  unfold ρw
  rw [one_div_pow, show 1 / 1000 * (1 / 5 ^ k) = 1 / (1000 * (5 : ℝ) ^ k) by field_simp,
    div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### The translations `e_k` -/

lemma abs_e_le (k : ℕ) : |A.e k| ≤ (1 / 3) ^ A.hd (k + 1) := by
  have h1 : 1 - A.η k = phis (fun i => !A.word k (A.nb k - 1 - i)) (A.nb k) (1 - A.υ k) := by
    rw [η, yc, psis_eq_phis, one_sub_phis]
  have hυ := A.υ_mem k
  have := abs_phis_sub_phis_le (d := fun i => !A.word k (A.nb k - 1 - i))
    (d' := fun i => A.word (k + 1) (0 + i)) (h := A.hd (k + 1)) (m := A.nb k)
    (m' := A.nb (k + 1) - 0) (fun i hi => by simp only [zero_add]; rw [A.word_head hi])
    (A.hd_le_nb k) (by have := A.hd_le_nb' (k + 1); omega)
    (z := 1 - A.υ k) (z' := 1 / 2 + ζw (k + 1)) ⟨by linarith [hυ.2], by linarith [hυ.1]⟩
    ⟨by linarith [(half_add_ζw_mem (k + 1)).1], by linarith [(half_add_ζw_mem (k + 1)).2]⟩
  have hx : A.xc (k + 1) 0 =
      phis (fun i => A.word (k + 1) (0 + i)) (A.nb (k + 1) - 0) (1 / 2 + ζw (k + 1)) := rfl
  rw [show A.e k = (1 - A.η k) - A.xc (k + 1) 0 from rfl, h1, hx]
  exact this

end Itin

end FiniteOrderMixing
