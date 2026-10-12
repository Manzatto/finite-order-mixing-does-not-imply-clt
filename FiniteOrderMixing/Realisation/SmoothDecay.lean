module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Nat.Sqrt

/-!
# Subexponential corrections for a smooth wandering construction

The integer square-root heads are sublinear, while their exponential corrections are
summable after multiplication by any polynomial. These two facts allow one fixed
wandering construction to have derivatives of every finite order.
-/

@[expose] public section

open Filter Topology

namespace FiniteOrderMixing

lemma tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b * b, fun n hn => Nat.le_sqrt.2 hn⟩

lemma tendsto_nat_sqrt_div :
    Tendsto (fun k : ℕ => (Nat.sqrt (k + 1) : ℝ) / k) atTop (𝓝 0) := by
  have hs : Tendsto (fun k : ℕ => Nat.sqrt (k + 1)) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp (tendsto_add_atTop_nat 1)
  have hi := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp hs
  apply squeeze_zero' (Eventually.of_forall fun k => by positivity) _ hi
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs0 : (0 : ℝ) < Nat.sqrt (k + 1) := by
    exact_mod_cast (Nat.sqrt_pos.2 (show 0 < k + 1 by omega))
  have hsq : (Nat.sqrt (k + 1) : ℝ) ^ 2 ≤ (k : ℝ) + 1 := by
    exact_mod_cast Nat.sqrt_le' (k + 1)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simp only [Function.comp_apply]
  rw [div_le_div_iff₀ hk0 hs0]
  nlinarith

lemma summable_pow_mul_third_sqrt (m : ℕ) :
    Summable (fun k : ℕ => ((k : ℝ) + 2) ^ m * (1 / 3 : ℝ) ^ Nat.sqrt (k + 2)) := by
  have hg := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (2 * (m + 2))
    (r := (1 / 3 : ℝ)) (by norm_num)
  have ht : Tendsto (fun s : ℕ => ((s : ℝ) + 1) ^ (2 * (m + 2)) * (1 / 3 : ℝ) ^ s)
      atTop (𝓝 0) := by
    have h := (hg.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)).const_mul 3
    convert h using 1
    · funext s
      simp only [Function.comp_apply]
      push_cast
      rw [pow_succ]
      ring
    · simp
  have hs : Tendsto (fun k : ℕ => Nat.sqrt (k + 2)) atTop atTop :=
    tendsto_nat_sqrt_atTop.comp (tendsto_add_atTop_nat 2)
  have he := (ht.comp hs).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hp : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2) ^ 2) := by
    have := (summable_nat_add_iff 2).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa using this
  apply hp.of_norm_bounded_eventually_nat
  filter_upwards [he] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsq : (k : ℝ) + 2 ≤ ((Nat.sqrt (k + 2) : ℝ) + 1) ^ 2 := by
    have := (Nat.lt_succ_sqrt' (k + 2)).le
    exact_mod_cast this
  have hpow : ((k : ℝ) + 2) ^ (m + 2) ≤
      ((Nat.sqrt (k + 2) : ℝ) + 1) ^ (2 * (m + 2)) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hsq _
  have hbound : ((k : ℝ) + 2) ^ (m + 2) * (1 / 3 : ℝ) ^ Nat.sqrt (k + 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hpow (by positivity)).trans hk.le
  rw [le_div_iff₀ (by positivity)]
  calc ((k : ℝ) + 2) ^ m * (1 / 3 : ℝ) ^ Nat.sqrt (k + 2) * ((k : ℝ) + 2) ^ 2
      = ((k : ℝ) + 2) ^ (m + 2) * (1 / 3 : ℝ) ^ Nat.sqrt (k + 2) := by
        rw [pow_add]; ring
    _ ≤ 1 := hbound

end FiniteOrderMixing
