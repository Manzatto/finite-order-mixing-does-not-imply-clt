module

public import Mathlib

/-!
# The Holroyd–Liggett weights on proper words

For words over four colours define `P [] = 1` and, for a proper word `w` of length `n ≥ 1`,

`(2n + 2) P(w) = ∑_i P(w with the i-th letter removed)`,

with `P(w) = 0` for improper words (two equal adjacent letters).  This is the law of the
insertion process of Holroyd–Liggett.  The identities

* `∑_a P(a :: x) = P(x)` and `∑_a P(x ++ [a]) = P(x)` (consistency),
* `∑_a P(x ++ a :: y) = P(x) P(y)` (one-dependence; this is where four colours are needed),

are proved by induction on the length; the correction term `(q - 4) P(x ++ y)` of the general
computation vanishes exactly for `q = 4`.
-/

@[expose] public section

open Finset

namespace FiniteOrderMixing.HL

/-- Words over four colours. -/
abbrev Word := List (Fin 4)

/-- Proper words: no two equal adjacent letters. -/
def Pr (w : Word) : Prop := w.IsChain (· ≠ ·)

instance (w : Word) : Decidable (Pr w) := by unfold Pr; infer_instance

/-- The Holroyd–Liggett weight of a word. -/
noncomputable def P (w : Word) : ℝ :=
  if Pr w then
    if w.length = 0 then 1
    else (∑ i : Fin w.length, P (w.eraseIdx i)) / (2 * w.length + 2)
  else 0
termination_by w.length
decreasing_by
  have := i.2
  rw [List.length_eraseIdx_of_lt i.2]; omega

lemma P_eq (w : Word) : P w = if Pr w then
    (if w.length = 0 then 1 else (∑ i : Fin w.length, P (w.eraseIdx i)) / (2 * w.length + 2))
    else 0 := by
  rw [P]

@[simp] lemma P_nil : P [] = 1 := by rw [P_eq]; simp [Pr]

lemma P_of_not {w : Word} (h : ¬ Pr w) : P w = 0 := by rw [P_eq, ite_eq_right h]

lemma P_rec {w : Word} (h : Pr w) (hw : w ≠ []) :
    (2 * w.length + 2 : ℝ) * P w = ∑ i ∈ range w.length, P (w.eraseIdx i) := by
  rw [P_eq, ite_eq_left h, ite_eq_right (by simpa using hw),
    ← Fin.sum_univ_eq_sum_range (fun i => P (w.eraseIdx i))]
  field_simp

lemma P_nonneg (w : Word) : 0 ≤ P w := by
  induction h : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    rw [P_eq]
    split_ifs
    · norm_num
    · exact div_nonneg (sum_nonneg fun i _ =>
        ih _ (by rw [← h, List.length_eraseIdx_of_lt i.2]; have := i.2; omega) _ rfl)
        (by positivity)
    · rfl

/-! ## Properness -/

lemma P_dup (u v : Word) (b : Fin 4) : P (u ++ b :: b :: v) = 0 := by
  refine P_of_not fun h => ?_
  have := (List.isChain_append.1 h).2.1
  simp at this

lemma Pr_left {u v : Word} (h : Pr (u ++ v)) : Pr u := (List.isChain_append.1 h).1

lemma Pr_right {u v : Word} (h : Pr (u ++ v)) : Pr v := (List.isChain_append.1 h).2.1

lemma Pr_tail {a : Fin 4} {v : Word} (h : Pr (a :: v)) : Pr v := h.tail

lemma P_single (a : Fin 4) : P [a] = 1 / 4 := by
  have h := P_rec (w := [a]) (by simp [Pr]) (by simp)
  simp at h
  linarith

/-- Reindexing a sum over `Fin (p+1) → Fin 4` by the first letter. -/
lemma sum_fun_succ (p : ℕ) (F : (Fin (p + 1) → Fin 4) → ℝ) :
    ∑ f, F f = ∑ a : Fin 4, ∑ g : Fin p → Fin 4, F (Fin.cons a g) := by
  rw [← (Fin.consEquiv fun _ => Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

/-! ## Consistency -/

/-- `∑_a P(a :: x) = P(x)`. -/
theorem sum_cons (x : Word) : ∑ a : Fin 4, P (a :: x) = P x := by
  induction h : x.length generalizing x with
  | zero =>
    rw [List.length_eq_zero_iff] at h
    subst h
    simp [P_single]
  | succ m ih =>
    by_cases hx : Pr x
    swap
    · rw [P_of_not hx]; exact sum_eq_zero fun a _ => P_of_not fun h => hx (Pr_tail h)
    obtain ⟨c, x', rfl⟩ : ∃ c x', x = c :: x' := List.exists_cons_of_length_eq_add_one h
    set x := c :: x' with hxdef
    have hlen : x'.length = m := by simpa [hxdef] using h
    set F : Fin 4 → ℝ := fun a => P x + ∑ i ∈ range (m + 1), P (a :: x.eraseIdx i)
    have hterm : ∀ a, (2 * (m + 1 + 1) + 2 : ℝ) * P (a :: x) = if a = c then 0 else F a := by
      intro a
      split_ifs with hac
      · subst hac; rw [show a :: x = [] ++ a :: a :: x' from rfl, P_dup]; ring
      · have hpr : Pr (a :: x) := List.isChain_cons_cons.2 ⟨hac, hx⟩
        have := P_rec hpr (by simp)
        rw [show (a :: x).length = m + 1 + 1 by simp [hxdef, hlen]] at this
        push_cast at this
        rw [this, sum_range_succ']
        simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, F]
        ring
    have hFc : F c = 2 * P x := by
      simp only [F]
      rw [sum_range_succ']
      have : ∀ i ∈ range m, P (c :: x.eraseIdx (i + 1)) = 0 := fun i _ => by
        rw [hxdef, List.eraseIdx_cons_succ, show c :: c :: x'.eraseIdx i =
          [] ++ c :: c :: x'.eraseIdx i from rfl, P_dup]
      rw [sum_eq_zero this, hxdef, List.eraseIdx_cons_zero]
      ring
    have hsumF : ∑ a, F a = 4 * P x + (2 * (m + 1) + 2) * P x := by
      simp only [F, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [sum_comm]
      have hrec := P_rec hx (by simp [hxdef])
      rw [show x.length = m + 1 by simp [hxdef, hlen]] at hrec
      push_cast at hrec ⊢
      rw [hrec]
      congr 1
      refine sum_congr rfl fun i hi => ih _ ?_
      rw [List.length_eraseIdx_of_lt (by simp only [hxdef, List.length_cons, hlen]; exact mem_range.1 hi)]
      simp [hxdef, hlen]
    have key : (2 * (m + 1 + 1) + 2 : ℝ) * ∑ a, P (a :: x) = (2 * (m + 1 + 1) + 2) * P x := by
      rw [mul_sum, sum_congr rfl fun a _ => hterm a]
      have : ∀ a, (if a = c then (0 : ℝ) else F a) = F a - if a = c then F a else 0 := fun a => by
        split_ifs <;> ring
      rw [sum_congr rfl fun a _ => this a, sum_sub_distrib, sum_ite_eq', ite_eq_left (mem_univ _),
        hsumF, hFc]
      ring
    have hpos : (0 : ℝ) < 2 * (m + 1 + 1) + 2 := by positivity
    exact mul_left_cancel₀ hpos.ne' key

/-- `∑_a P(x ++ [a]) = P(x)`. -/
theorem sum_snoc (x : Word) : ∑ a : Fin 4, P (x ++ [a]) = P x := by
  induction h : x.length generalizing x with
  | zero =>
    rw [List.length_eq_zero_iff] at h
    subst h
    simp [P_single]
  | succ m ih =>
    by_cases hx : Pr x
    swap
    · rw [P_of_not hx]; exact sum_eq_zero fun a _ => P_of_not fun h => hx (Pr_left h)
    obtain ⟨x', c, rfl⟩ : ∃ x' c, x = x' ++ [c] := by
      rcases List.eq_nil_or_concat x with h0 | ⟨x', c, hc⟩
      · subst h0; simp at h
      · exact ⟨x', c, by rw [hc, List.concat_eq_append]⟩
    set x := x' ++ [c] with hxdef
    have hlen : x'.length = m := by simpa [hxdef] using h
    have hxl : x.length = m + 1 := by simp [hxdef, hlen]
    set F : Fin 4 → ℝ := fun a => P x + ∑ i ∈ range (m + 1), P (x.eraseIdx i ++ [a])
    have hterm : ∀ a, (2 * (m + 1 + 1) + 2 : ℝ) * P (x ++ [a]) = if a = c then 0 else F a := by
      intro a
      split_ifs with hac
      · subst hac
        rw [hxdef, List.append_assoc, List.singleton_append, P_dup]; ring
      · have hpr : Pr (x ++ [a]) := by
          refine List.isChain_append.2 ⟨hx, by simp, ?_⟩
          intro u hu v hv
          simp [hxdef] at hu hv
          rw [← hu, ← hv]; exact fun e => hac (by first | exact e | exact e.symm)
        have := P_rec hpr (by simp)
        rw [show (x ++ [a]).length = m + 1 + 1 by simp [hxl]] at this
        push_cast at this
        rw [this, sum_range_succ]
        have e1 : ∀ i ∈ range (m + 1), (x ++ [a]).eraseIdx i = x.eraseIdx i ++ [a] :=
          fun i hi => List.eraseIdx_append_of_lt_length (by rw [hxl]; exact mem_range.1 hi) _
        have e2 : (x ++ [a]).eraseIdx (m + 1) = x := by
          rw [List.eraseIdx_append_of_length_le (by rw [hxl]), hxl, Nat.sub_self]; simp
        rw [sum_congr rfl fun i hi => by rw [e1 i hi], e2]
        simp only [F]; ring
    have hFc : F c = 2 * P x := by
      simp only [F]
      rw [sum_range_succ]
      have : ∀ i ∈ range m, P (x.eraseIdx i ++ [c]) = 0 := fun i hi => by
        rw [hxdef, List.eraseIdx_append_of_lt_length (by rw [hlen]; exact mem_range.1 hi),
          List.append_assoc, List.singleton_append, P_dup]
      rw [sum_eq_zero this, hxdef, List.eraseIdx_append_of_length_le (by rw [hlen]),
        hlen, Nat.sub_self, List.eraseIdx_cons_zero, List.append_nil]
      ring
    have hsumF : ∑ a, F a = 4 * P x + (2 * (m + 1) + 2) * P x := by
      simp only [F, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [sum_comm]
      have hrec := P_rec hx (by simp [hxdef])
      rw [hxl] at hrec
      push_cast at hrec ⊢
      rw [hrec]
      congr 1
      refine sum_congr rfl fun i hi => ih _ ?_
      rw [List.length_eraseIdx_of_lt (by rw [hxl]; exact mem_range.1 hi), hxl]
      simp
    have key : (2 * (m + 1 + 1) + 2 : ℝ) * ∑ a, P (x ++ [a]) =
        (2 * (m + 1 + 1) + 2) * P x := by
      rw [mul_sum, sum_congr rfl fun a _ => hterm a]
      have : ∀ a, (if a = c then (0 : ℝ) else F a) = F a - if a = c then F a else 0 := fun a => by
        split_ifs <;> ring
      rw [sum_congr rfl fun a _ => this a, sum_sub_distrib, sum_ite_eq', ite_eq_left (mem_univ _),
        hsumF, hFc]
      ring
    have hpos : (0 : ℝ) < 2 * (m + 1 + 1) + 2 := by positivity
    exact mul_left_cancel₀ hpos.ne' key

/-! ## One-dependence -/

/-- **One-dependence**: `∑_a P(x ++ a :: y) = P(x) P(y)`. -/
theorem sum_mid (x y : Word) : ∑ a : Fin 4, P (x ++ a :: y) = P x * P y := by
  induction h : x.length + y.length generalizing x y with
  | zero =>
    have hx : x = [] := List.length_eq_zero_iff.1 (by omega)
    subst hx
    simp [sum_cons]
  | succ n ih =>
    rcases List.eq_nil_or_concat x with hx0 | ⟨x', b, hxb⟩
    · subst hx0; simp [sum_cons]
    rw [List.concat_eq_append] at hxb
    rcases y with _ | ⟨c, y'⟩
    · simp [sum_snoc]
    by_cases hx : Pr x
    swap
    · rw [P_of_not hx, zero_mul]
      exact sum_eq_zero fun a _ => P_of_not fun h => hx (Pr_left h)
    by_cases hy : Pr (c :: y')
    swap
    · rw [P_of_not hy, mul_zero]
      exact sum_eq_zero fun a _ => P_of_not fun h => hy (Pr_tail (Pr_right h))
    subst hxb
    set x := x' ++ [b] with hxdef
    set y := c :: y' with hydef
    set k := x.length with hk
    set l := y.length with hl
    have hk' : k = x'.length + 1 := by simp [hk, hxdef]
    have hl' : l = y'.length + 1 := by simp [hl, hydef]
    set A : Fin 4 → ℝ := fun a => ∑ i ∈ range k, P (x.eraseIdx i ++ a :: y)
    set C : Fin 4 → ℝ := fun a => ∑ j ∈ range l, P (x ++ a :: y.eraseIdx j)
    -- the four boundary identities
    have L1 : A b = P (x ++ y) := by
      simp only [A]
      rw [hk', sum_range_succ]
      have : ∀ i ∈ range x'.length, P (x.eraseIdx i ++ b :: y) = 0 := fun i hi => by
        rw [hxdef, List.eraseIdx_append_of_lt_length (mem_range.1 hi), List.append_assoc,
          List.singleton_append, P_dup]
      rw [sum_eq_zero this, hxdef, List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self,
        List.eraseIdx_cons_zero, List.append_nil, zero_add, List.append_assoc,
        List.singleton_append]
    have L2 : A c = 0 := sum_eq_zero fun i _ => by rw [hydef, P_dup]
    have L3 : C c = P (x ++ y) := by
      simp only [C]
      rw [hl', sum_range_succ']
      have : ∀ j ∈ range y'.length, P (x ++ c :: y.eraseIdx (j + 1)) = 0 := fun j _ => by
        rw [hydef, List.eraseIdx_cons_succ, P_dup]
      rw [sum_eq_zero this, hydef, List.eraseIdx_cons_zero, zero_add]
    have L4 : C b = 0 := sum_eq_zero fun j _ => by
      rw [hxdef, List.append_assoc, List.singleton_append, P_dup]
    -- the recursion for a good middle letter
    have hrec : ∀ a, a ≠ b → a ≠ c →
        (2 * (k + l + 1) + 2 : ℝ) * P (x ++ a :: y) = A a + P (x ++ y) + C a := by
      intro a hab hac
      have hpr : Pr (x ++ a :: y) := by
        refine List.isChain_append.2 ⟨hx, List.isChain_cons_cons.2 ⟨hac, hy⟩, ?_⟩
        intro u hu v hv
        simp [hxdef] at hu hv
        rw [← hu, ← hv]; exact Ne.symm hab
      have := P_rec hpr (by simp)
      rw [show (x ++ a :: y).length = k + (l + 1) by simp [hk, hl]] at this
      push_cast at this
      rw [show (2 * (k + l + 1) + 2 : ℝ) = 2 * (k + (l + 1)) + 2 by ring, this, sum_range_add,
        sum_range_succ']
      have e1 : ∀ i ∈ range k, (x ++ a :: y).eraseIdx i = x.eraseIdx i ++ a :: y :=
        fun i hi => List.eraseIdx_append_of_lt_length (mem_range.1 hi) _
      have e2 : ∀ j, (x ++ a :: y).eraseIdx (k + j) = x ++ (a :: y).eraseIdx j := fun j => by
        rw [List.eraseIdx_append_of_length_le (by omega)]; congr 2; omega
      rw [sum_congr rfl fun i hi => by rw [e1 i hi]]
      simp only [e2, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, A, C]
      ring
    -- a uniform formula for every middle letter
    have hall : ∀ a, (2 * (k + l + 1) + 2 : ℝ) * P (x ++ a :: y) =
        (A a - if a = b then A b else 0) + (if a ≠ b ∧ a ≠ c then P (x ++ y) else 0) +
          (C a - if a = c then C c else 0) := by
      intro a
      by_cases hab : a = b
      · rw [hab]
        have h0 : P (x ++ b :: y) = 0 := by
          rw [hxdef, List.append_assoc, List.singleton_append, P_dup]
        rw [h0, L4]
        by_cases hbc : b = c
        · rw [ite_eq_left hbc, ← hbc, L4]; simp
        · rw [ite_eq_right hbc]; simp
      by_cases hac : a = c
      · rw [hac]
        have h0 : P (x ++ c :: y) = 0 := by rw [hydef, P_dup]
        have hcb : c ≠ b := hac ▸ hab
        rw [h0, L2, ite_eq_right hcb]
        simp
      · rw [hrec a hab hac]
        simp [hab, hac]
    have hcount : ∑ a : Fin 4, (if a ≠ b ∧ a ≠ c then P (x ++ y) else 0) = 2 * P (x ++ y) := by
      by_cases hbc : b = c
      · subst hbc
        have : P (x ++ y) = 0 := by
          rw [hxdef, hydef, List.append_assoc, List.singleton_append, P_dup]
        simp [this]
      · rw [← sum_filter, sum_const, nsmul_eq_mul]
        have : (univ.filter fun a : Fin 4 => a ≠ b ∧ a ≠ c) = (univ.erase b).erase c := by
          ext a; simp [and_comm]
        rw [this, card_erase_of_mem (by simp [Ne.symm hbc]), card_erase_of_mem (mem_univ _)]
        simp
    have hA : ∑ a, A a = (2 * k + 2) * P x * P y := by
      simp only [A]
      rw [sum_comm]
      have hr := P_rec hx (by simp [hxdef])
      rw [← hk] at hr
      rw [hr, sum_mul]
      refine sum_congr rfl fun i hi => ih _ _ ?_
      rw [List.length_eraseIdx_of_lt (mem_range.1 hi)]
      omega
    have hC : ∑ a, C a = (2 * l + 2) * P x * P y := by
      simp only [C]
      rw [sum_comm]
      have hr := P_rec hy (by simp)
      rw [← hl] at hr
      rw [show (2 * (l : ℝ) + 2) * P x * P y = P x * ((2 * l + 2) * P y) by ring, hr, mul_sum]
      refine sum_congr rfl fun j hj => ih _ _ ?_
      rw [List.length_eraseIdx_of_lt (mem_range.1 hj)]
      omega
    have key : (2 * (k + l + 1) + 2 : ℝ) * ∑ a, P (x ++ a :: y) =
        (2 * (k + l + 1) + 2) * (P x * P y) := by
      rw [mul_sum, sum_congr rfl fun a _ => hall a, sum_add_distrib, sum_add_distrib,
        sum_sub_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq', ite_eq_left (mem_univ _),
        ite_eq_left (mem_univ _), hcount, hA, hC, L1, L3]
      ring
    have hpos : (0 : ℝ) < 2 * (k + l + 1) + 2 := by positivity
    exact mul_left_cancel₀ hpos.ne' key

/-! ## Summing out blocks of letters -/

/-- Summing out a block of letters on the left. -/
theorem sum_left (p : ℕ) (w : Word) :
    ∑ f : Fin p → Fin 4, P (List.ofFn f ++ w) = P w := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [sum_fun_succ, sum_comm]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.cons_append]
    rw [← ih]
    exact sum_congr rfl fun g _ => sum_cons _

/-- The weights of the words of length `n` sum to one. -/
theorem sum_all (n : ℕ) : ∑ f : Fin n → Fin 4, P (List.ofFn f) = 1 := by
  simpa using sum_left n []

/-- Summing out a nonempty block of letters between two words. -/
theorem sum_gap (t : ℕ) (u v : Word) :
    ∑ f : Fin (t + 1) → Fin 4, P (u ++ List.ofFn f ++ v) = P u * P v := by
  rw [sum_fun_succ, sum_comm]
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.cons_append, List.append_assoc]
  rw [← sum_left t v, mul_sum]
  exact sum_congr rfl fun g _ => sum_mid _ _

/-- Summing out a block of letters on the right. -/
theorem sum_right (s : ℕ) (w : Word) :
    ∑ f : Fin s → Fin 4, P (w ++ List.ofFn f) = P w := by
  cases s with
  | zero => simp
  | succ s =>
    have := sum_gap s w []
    simpa using this

end FiniteOrderMixing.HL
