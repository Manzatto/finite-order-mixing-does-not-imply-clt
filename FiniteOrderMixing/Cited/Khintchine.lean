import FiniteOrderMixing.Avg

/-!
# Khintchine's inequality for even moments with the Gaussian constant

`E(∑ a_j ξ_j)^{2q} ≤ (2q-1)!! (∑ a_j^2)^q` for independent symmetric signs `ξ_j`.

The proof adds one sign at a time.  Averaging over a new sign `ξ` with coefficient `x` kills the
odd powers of `x`, `E(xξ + X)^{2q} = ∑_k C(2q,2k) x^{2k} E X^{2(q-k)}`, and the identity
`C(2q,2k) (2(q-k)-1)!! (2k-1)!! = (2q-1)!! C(q,k)` compares this term by term with
`(2q-1)!! (x^2 + s)^q`.
-/

open Finset
open scoped Nat

namespace FiniteOrderMixing

/-- `(2n)! = 2^n n! (2n-1)!!`. -/
lemma factorial_two_mul (n : ℕ) : (2 * n)! = 2 ^ n * n ! * (2 * n - 1)‼ := by
  cases n with
  | zero => rfl
  | succ m =>
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * m + 1)
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Nat.doubleFactorial_two_mul] at h
    rw [h, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]

/-- `C(2q,2k) (2(q-k)-1)!! (2k-1)!! = (2q-1)!! C(q,k)`. -/
lemma choose_doubleFactorial {q k : ℕ} (hk : k ≤ q) :
    (2 * q).choose (2 * k) * (2 * (q - k) - 1)‼ * (2 * k - 1)‼ = (2 * q - 1)‼ * q.choose k := by
  set j := q - k
  have hq : q = k + j := by omega
  have hX : 0 < 2 ^ q * k ! * j ! := by positivity
  refine Nat.eq_of_mul_eq_mul_right hX ?_
  have h1 : (2 * q).choose (2 * k) * (2 * k)! * (2 * j)! = (2 * q)! := by
    have := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ 2 * q by omega)
    rwa [show 2 * q - 2 * k = 2 * j by omega] at this
  have h2 : q.choose k * k ! * j ! = q ! := by
    have := Nat.choose_mul_factorial_mul_factorial hk
    rwa [show q - k = j by omega] at this
  have e1 := factorial_two_mul k
  have e2 := factorial_two_mul j
  have e3 := factorial_two_mul q
  have hpow : 2 ^ q = 2 ^ k * 2 ^ j := by rw [hq, pow_add]
  calc (2 * q).choose (2 * k) * (2 * j - 1)‼ * (2 * k - 1)‼ * (2 ^ q * k ! * j !)
      = (2 * q).choose (2 * k) * (2 ^ k * k ! * (2 * k - 1)‼) * (2 ^ j * j ! * (2 * j - 1)‼) := by
        rw [hpow]; ring
    _ = (2 * q)! := by rw [← e1, ← e2, h1]
    _ = (2 * q - 1)‼ * q.choose k * (2 ^ q * k ! * j !) := by
        rw [e3, ← h2]; ring

lemma choose_doubleFactorial_le {q k : ℕ} (hk : k ≤ q) :
    ((2 * q).choose (2 * k) : ℝ) * ((2 * (q - k) - 1)‼ : ℝ) ≤ ((2 * q - 1)‼ : ℝ) * q.choose k := by
  have h := choose_doubleFactorial hk
  have hpos : 1 ≤ (2 * k - 1)‼ := Nat.one_le_iff_ne_zero.2 (Nat.doubleFactorial_pos _).ne'
  exact_mod_cast h ▸ Nat.le_mul_of_pos_right _ hpos

/-- Splitting a sum over `range (2n+1)` into even and odd indices. -/
lemma sum_range_even_odd (f : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ range (2 * n + 1), f m =
      ∑ k ∈ range (n + 1), f (2 * k) + ∑ k ∈ range n, f (2 * k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun k => f (2 * k)) (n + 1), sum_range_succ (fun k => f (2 * k + 1)) n,
      show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    ring

/-- Averaging a new sign kills the odd powers. -/
lemma sym_pow_eq (x y : ℝ) (q : ℕ) :
    ((x + y) ^ (2 * q) + (-x + y) ^ (2 * q)) / 2 =
      ∑ k ∈ range (q + 1), ((2 * q).choose (2 * k) : ℝ) * x ^ (2 * k) * y ^ (2 * (q - k)) := by
  rw [add_pow, add_pow, ← sum_add_distrib, sum_div, sum_range_even_odd]
  have hodd : ∀ k ∈ range q, (x ^ (2 * k + 1) * y ^ (2 * q - (2 * k + 1)) *
      ((2 * q).choose (2 * k + 1) : ℝ) + (-x) ^ (2 * k + 1) * y ^ (2 * q - (2 * k + 1)) *
      ((2 * q).choose (2 * k + 1) : ℝ)) / 2 = 0 := fun k _ => by
    rw [Odd.neg_pow ⟨k, rfl⟩]; ring
  rw [sum_eq_zero hodd, add_zero]
  refine sum_congr rfl fun k hk => ?_
  rw [Even.neg_pow ⟨k, by ring⟩, show 2 * q - 2 * k = 2 * (q - k) by
    have := mem_range.1 hk; omega]
  ring

lemma patch_update {B : Finset ℤ} {c : ℤ} (hc : c ∉ B) (T : Finset ℤ) (b : Bool) (ω : Config) :
    patch B T (Function.update ω c b) = Function.update (patch B T ω) c b := by
  funext j
  by_cases hj : j = c
  · subst hj; simp [patch, hc]
  · by_cases hjB : j ∈ B <;> simp [patch, hj, hjB]

lemma avgAt_update_allTrue {B : Finset ℤ} {c : ℤ} (hc : c ∉ B) (b : Bool) (F : Config → ℝ) :
    avgAt B F (Function.update allTrue c b) = avg B fun ω => F (Function.update ω c b) := by
  simp only [avg, avgAt]
  congr 1
  exact sum_congr rfl fun T _ => by rw [patch_update hc]

/-- **Khintchine's inequality** (sharp, even exponents; Haagerup). -/
theorem khintchine (B : Finset ℤ) (a : ℤ → ℝ) (q : ℕ) :
    avg B (fun ω => (∑ j ∈ B, a j * Z j ω) ^ (2 * q)) ≤
      ((2 * q - 1)‼ : ℝ) * (∑ j ∈ B, a j ^ 2) ^ q := by
  classical
  induction B using Finset.induction_on generalizing q with
  | empty =>
    simp only [sum_empty]
    rw [avg_const]
    cases q with
    | zero => simp
    | succ q => simp
  | insert c B hc ih =>
    set x := a c
    set X : Config → ℝ := fun ω => ∑ j ∈ B, a j * Z j ω
    set s := ∑ j ∈ B, a j ^ 2
    have hX : ∀ ω b, X (Function.update ω c b) = X ω := fun ω b =>
      sum_congr rfl fun j hj => by
        have : j ≠ c := fun h => hc (h ▸ hj)
        simp [Z, Function.update_of_ne this]
    have hsplit : avg (insert c B) (fun ω => (∑ j ∈ insert c B, a j * Z j ω) ^ (2 * q)) =
        avg B (fun ω => ∑ k ∈ range (q + 1),
          ((2 * q).choose (2 * k) : ℝ) * x ^ (2 * k) * X ω ^ (2 * (q - k))) := by
      have key : ∀ ω b, (∑ j ∈ insert c B, a j * Z j (Function.update ω c b)) =
          x * spin b + X ω := by
        intro ω b
        rw [sum_insert hc, ← hX ω b]
        simp [Z, x, X]
      rw [avg, avgAt_insert hc, avgAt_update_allTrue hc true, avgAt_update_allTrue hc false,
        ← avg_add, div_eq_mul_inv, mul_comm, ← avg_const_mul]
      refine avg_congr fun ω => ?_
      dsimp only [Pi.add_apply]
      rw [key, key, ← sym_pow_eq]
      simp only [spin_true, spin_false]
      ring
    rw [hsplit, avg_sum, sum_insert hc, add_pow]
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hkq : k ≤ q := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [avg_const_mul]
    have hIH := ih (q - k)
    have hs : 0 ≤ s := sum_nonneg fun j _ => sq_nonneg _
    have hx : 0 ≤ x ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) k
    have hc0 : (0 : ℝ) ≤ ((2 * q).choose (2 * k) : ℝ) * x ^ (2 * k) := by positivity
    calc ((2 * q).choose (2 * k) : ℝ) * x ^ (2 * k) * avg B (fun ω => X ω ^ (2 * (q - k)))
        ≤ ((2 * q).choose (2 * k) : ℝ) * x ^ (2 * k) *
            (((2 * (q - k) - 1)‼ : ℝ) * s ^ (q - k)) := mul_le_mul_of_nonneg_left hIH hc0
      _ = (((2 * q).choose (2 * k) : ℝ) * ((2 * (q - k) - 1)‼ : ℝ)) *
            (x ^ (2 * k) * s ^ (q - k)) := by ring
      _ ≤ (((2 * q - 1)‼ : ℝ) * q.choose k) * (x ^ (2 * k) * s ^ (q - k)) :=
          mul_le_mul_of_nonneg_right (choose_doubleFactorial_le hkq) (by positivity)
      _ = ((2 * q - 1)‼ : ℝ) * ((x ^ 2) ^ k * s ^ (q - k) * (q.choose k : ℝ)) := by
          rw [← pow_mul]; ring

end FiniteOrderMixing
