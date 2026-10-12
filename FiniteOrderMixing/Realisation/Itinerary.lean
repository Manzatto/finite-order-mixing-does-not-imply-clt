import FiniteOrderMixing.Realisation.PlaneDigits
import FiniteOrderMixing.Realisation.SmoothDecay

/-!
# The itinerary of the wandering box

Given `ω ∈ Σ`, the wandering box follows blocks `k = 0, 1, 2, …` of `nb k` horseshoe steps, each
followed by one step through the gap strip.  Block `k` starts at time `tt k`; its symbols are
those of `ω` at the same times, except for a head of `hd k` symbols, which repeat the flipped
reversed tail of the previous block (this makes the return through the gap strip nearly exact).
The head lengths have a logarithmic part and an integer square-root part. They have density
zero, while the square-root part makes the perturbations smooth in every finite order.
-/

open Set Filter Topology

namespace FiniteOrderMixing

/-- The data `r` (smoothness), `H₀` (head offset) and the target sequence `ω`. -/
structure Itin where
  r : ℕ
  H₀ : ℕ
  ω : Config

namespace Itin

variable (A : Itin)

/-- Length of the head of block `k`. -/
def hd : ℕ → ℕ
  | 0 => 0
  | k + 1 => (2 * A.r + 2) * (Nat.log 2 (k + 2) + 1) + A.H₀ + Nat.sqrt (k + 2)

/-- Length of block `k` (horseshoe steps). -/
def nb (k : ℕ) : ℕ := A.hd (k + 1) + k + 1

/-- Starting time of block `k`. -/
def tt : ℕ → ℕ
  | 0 => 0
  | k + 1 => tt k + A.nb k + 1

/-- The symbols of block `k`. -/
def word : ℕ → ℕ → Bool
  | 0, i => A.ω i
  | k + 1, i => if i < A.hd (k + 1) then !(word k (A.nb k - 1 - i)) else A.ω ((A.tt (k + 1) + i : ℕ) : ℤ)

/-- The bound `D = 2r + 4` on the increments of `nb`. -/
def D : ℕ := 2 * A.r + 4

lemma hd_mono : Monotone A.hd := by
  apply monotone_nat_of_le_succ
  intro k
  rcases k with _ | k
  · exact Nat.zero_le _
  · simp only [hd]
    have := Nat.log_mono_right (b := 2) (show k + 1 + 1 ≤ k + 1 + 1 + 1 by omega)
    exact Nat.add_le_add
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right this 1)) _)
      (Nat.sqrt_le_sqrt (by omega))

lemma hd_succ_le (k : ℕ) : A.hd (k + 1 + 1) ≤ A.hd (k + 1) + (2 * A.r + 3) := by
  simp only [hd]
  have : Nat.log 2 (k + 1 + 2) ≤ Nat.log 2 (k + 2) + 1 := by
    calc Nat.log 2 (k + 1 + 2) ≤ Nat.log 2 ((k + 2) * 2) := Nat.log_mono_right (by omega)
      _ = Nat.log 2 (k + 2) + 1 := Nat.log_mul_base (by norm_num) (by omega)
  have hs : Nat.sqrt (k + 1 + 2) ≤ Nat.sqrt (k + 2) + 1 := by
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using Nat.sqrt_succ_le_succ_sqrt (k + 2)
  nlinarith

lemma nb_succ_le (k : ℕ) : A.nb (k + 1) ≤ A.nb k + A.D := by
  have := A.hd_succ_le k
  simp only [nb, D]; omega

lemma hd_le_nb (k : ℕ) : A.hd (k + 1) ≤ A.nb k := by simp only [nb]; omega

lemma hd_le_nb' (k : ℕ) : A.hd k ≤ A.nb k := by
  have := A.hd_mono (show k ≤ k + 1 by omega); have := A.hd_le_nb k; omega

lemma word_of_ge {k i : ℕ} (h : A.hd k ≤ i) : A.word k i = A.ω ((A.tt k + i : ℕ) : ℤ) := by
  rcases k with _ | k
  · simp [word, tt]
  · simp only [word, show ¬ i < A.hd (k + 1) by omega, ↓reduceIte]

lemma word_head {k i : ℕ} (h : i < A.hd (k + 1)) :
    A.word (k + 1) i = !(A.word k (A.nb k - 1 - i)) := by
  simp only [word, h, ↓reduceIte]

lemma tt_succ (k : ℕ) : A.tt (k + 1) = A.tt k + A.nb k + 1 := rfl

lemma tt_strictMono : StrictMono A.tt :=
  strictMono_nat_of_lt_succ fun k => by rw [tt_succ]; omega

lemma le_tt (k : ℕ) : k ≤ A.tt k := A.tt_strictMono.id_le k

lemma sq_le_tt (K : ℕ) : K * K ≤ 2 * A.tt K := by
  induction K with
  | zero => simp [tt]
  | succ K ih =>
    rw [tt_succ]
    have : K ≤ A.nb K := by simp only [nb]; omega
    nlinarith

/-! ### The block containing a given time -/

lemma exists_blk (t : ℕ) : ∃ k, t < A.tt (k + 1) := ⟨t, by have := A.le_tt (t + 1); omega⟩

/-- The block containing time `t`. -/
def blk (t : ℕ) : ℕ := Nat.find (A.exists_blk t)

/-- The position of time `t` in its block. -/
def pos (t : ℕ) : ℕ := t - A.tt (A.blk t)

lemma lt_tt_blk (t : ℕ) : t < A.tt (A.blk t + 1) := Nat.find_spec (A.exists_blk t)

lemma tt_blk_le (t : ℕ) : A.tt (A.blk t) ≤ t := by
  rcases h0 : A.blk t with _ | k
  · simp [tt]
  · by_contra h
    have hk : k < Nat.find (A.exists_blk t) := by unfold blk at h0; omega
    exact Nat.find_min (A.exists_blk t) hk (by omega)

lemma blk_eq {t k : ℕ} (h1 : A.tt k ≤ t) (h2 : t < A.tt (k + 1)) : A.blk t = k := by
  have a1 := A.lt_tt_blk t
  have a2 := A.tt_blk_le t
  rcases lt_trichotomy (A.blk t) k with h | h | h
  · have := A.tt_strictMono.monotone (show A.blk t + 1 ≤ k by omega); omega
  · exact h
  · have := A.tt_strictMono.monotone (show k + 1 ≤ A.blk t by omega); omega

lemma blk_tt_add {k j : ℕ} (hj : j ≤ A.nb k) : A.blk (A.tt k + j) = k :=
  A.blk_eq (by omega) (by rw [tt_succ]; omega)

lemma pos_tt_add {k j : ℕ} (hj : j ≤ A.nb k) : A.pos (A.tt k + j) = j := by
  rw [pos, A.blk_tt_add hj]; omega

lemma pos_le (t : ℕ) : A.pos t ≤ A.nb (A.blk t) := by
  have := A.lt_tt_blk t; rw [tt_succ] at this; unfold pos; omega

lemma tt_add_pos (t : ℕ) : A.tt (A.blk t) + A.pos t = t := by
  have := A.tt_blk_le t; unfold pos; omega

lemma tendsto_blk : Tendsto A.blk atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  refine ⟨A.tt K, fun t ht => ?_⟩
  by_contra h
  rw [not_le] at h
  have := A.lt_tt_blk t
  have := A.tt_strictMono.monotone (show A.blk t + 1 ≤ K by omega)
  omega

end Itin

end FiniteOrderMixing
