module

public import Mathlib

/-!
# Even moments of the standard Gaussian

`E G^{2p} = (2p-1)!!` for `G ~ N(0,1)`, derived from Mathlib's Gamma-function evaluation of
`∫₀^∞ x^q e^{-b x^p}` and the half-integer values `Γ(k + 1/2)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set
open scoped Nat NNReal

namespace FiniteOrderMixing

/-- Even moments of the standard Gaussian: `E G^{2p} = (2p-1)!!`. -/
theorem gaussian_even_moment (p : ℕ) :
    ∫ x, x ^ (2 * p) ∂(gaussianReal 0 1) = ((2 * p - 1)‼ : ℝ) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [gaussianPDFReal, smul_eq_mul, sub_zero, NNReal.coe_one, mul_one]
  set c : ℝ := (√(2 * π))⁻¹
  have habs : ∀ x : ℝ, c * rexp (-x ^ 2 / 2) * x ^ (2 * p) =
      (fun y => c * rexp (-y ^ 2 / 2) * y ^ (2 * p)) |x| := fun x => by
    simp only [pow_mul, sq_abs]
  rw [integral_congr_ae (Filter.Eventually.of_forall habs),
    integral_comp_abs (f := fun y => c * rexp (-y ^ 2 / 2) * y ^ (2 * p))]
  have hIoi : ∫ x in Ioi (0 : ℝ), c * rexp (-x ^ 2 / 2) * x ^ (2 * p) =
      c * ∫ x in Ioi (0 : ℝ), x ^ ((2 * p : ℕ) : ℝ) * rexp (-(1 / 2) * x ^ (2 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [rpow_natCast, rpow_two]
    ring_nf
  rw [hIoi, integral_rpow_mul_exp_neg_mul_rpow two_pos
    (by have : (0 : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by positivity
        linarith) (by norm_num)]
  have hG : ((2 * p : ℕ) + 1 : ℝ) / 2 = (p : ℝ) + 1 / 2 := by push_cast; ring
  rw [hG, Gamma_nat_add_half]
  have hpow : (1 / 2 : ℝ) ^ (-((2 * p : ℕ) + 1 : ℝ) / 2) = 2 ^ p * √2 := by
    rw [show -((2 * p : ℕ) + 1 : ℝ) / 2 = -((p : ℝ) + 1 / 2) by push_cast; ring,
      rpow_neg (by norm_num), ← inv_rpow (by norm_num), one_div, inv_inv,
      rpow_add (by norm_num), rpow_natCast, sqrt_eq_rpow, one_div]
  rw [hpow]
  have hs : √(2 * π) = √2 * √π := sqrt_mul (by norm_num) π
  have h2 : (0 : ℝ) < √2 := by positivity
  have hπ : (0 : ℝ) < √π := sqrt_pos.2 pi_pos
  simp only [c, hs]
  field_simp
