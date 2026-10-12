import FiniteOrderMixing.Limit

/-!
# The marker selection rule (Section `subsec:markers`, deterministic part)

Given the old markers `o : ℤ → Bool` and a colouring `v : ℤ → Fin q` of their enumeration, the
new markers are `sel o v N`.  The enumeration index of an old marker `t` is the signed number
`idx o t` of old markers in `(0, t]` (so that `t_0 ≤ 0 < t_1` receive the indices `0` and `1`); its
colour is `v (idx o t)`.

The sets `A_a` of `eq:marker-selection` are `inA o v N a`.

Main results:
* `sel_sub`, `sel_maximal` — `𝓜_k ⊆ 𝓜_{k-1}` is an `N`-net of `𝓜_{k-1}`;
* `sel_sep` — `𝓜_k` is `N`-separated when the colouring is proper at range `N`;
* `sel_shift` — translation equivariance;
* `sel_local` — Lemma `lem:local-selection`.
-/

open Finset

namespace FiniteOrderMixing

/-! ## Signed counts of markers -/

/-- The number of markers in `(a, b]`. -/
def ncount (o : ℤ → Bool) (a b : ℤ) : ℕ := ((Finset.Ioc a b).filter fun u => o u = true).card

/-- Signed number of markers between `a` and `b`. -/
def cnt (o : ℤ → Bool) (a b : ℤ) : ℤ := (ncount o a b : ℤ) - ncount o b a

/-- The enumeration index of a marker. -/
def idx (o : ℤ → Bool) (t : ℤ) : ℤ := cnt o 0 t

lemma ncount_empty (o : ℤ → Bool) {a b : ℤ} (h : b ≤ a) : ncount o a b = 0 := by
  simp [ncount, Finset.Ioc_eq_empty_of_le h]

lemma ncount_split (o : ℤ → Bool) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    ncount o a c = ncount o a b + ncount o b c := by
  simp only [ncount]
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hab hbc, Finset.filter_union,
    Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.disjoint_left.2 fun x hx hx' => by
    simp only [Finset.mem_Ioc] at hx hx'; omega)

lemma cnt_of_le (o : ℤ → Bool) {a b : ℤ} (h : a ≤ b) : cnt o a b = ncount o a b := by
  simp [cnt, ncount_empty o h]

lemma cnt_of_ge (o : ℤ → Bool) {a b : ℤ} (h : b ≤ a) : cnt o a b = -(ncount o b a : ℤ) := by
  simp [cnt, ncount_empty o h]

lemma cnt_add (o : ℤ → Bool) (a b c : ℤ) : cnt o a c = cnt o a b + cnt o b c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · rw [cnt_of_le o (hab.trans hbc), cnt_of_le o hab, cnt_of_le o hbc, ncount_split o hab hbc]
      push_cast; ring
    · rcases le_total a c with hac | hca
      · rw [cnt_of_le o hac, cnt_of_le o hab, cnt_of_ge o hcb, ncount_split o hac hcb]
        push_cast; ring
      · rw [cnt_of_ge o hca, cnt_of_le o hab, cnt_of_ge o hcb, ncount_split o hca hab]
        push_cast; ring
  · rcases le_total b c with hbc | hcb
    · rcases le_total a c with hac | hca
      · rw [cnt_of_le o hac, cnt_of_ge o hba, cnt_of_le o hbc, ncount_split o hba hac]
        push_cast; ring
      · rw [cnt_of_ge o hca, cnt_of_ge o hba, cnt_of_le o hbc, ncount_split o hbc hca]
        push_cast; ring
    · rw [cnt_of_ge o (hcb.trans hba), cnt_of_ge o hba, cnt_of_ge o hcb, ncount_split o hcb hba]
      push_cast; ring

lemma idx_sub (o : ℤ → Bool) {t t' : ℤ} (h : t ≤ t') : idx o t' - idx o t = ncount o t t' := by
  simp only [idx]
  rw [cnt_add o 0 t t', cnt_of_le o h]; ring

lemma ncount_shift (o : ℤ → Bool) (m a b : ℤ) :
    ncount (fun x => o (x + m)) a b = ncount o (a + m) (b + m) := by
  simp only [ncount]
  rw [← Finset.map_add_right_Ioc, Finset.filter_map, Finset.card_map]
  rfl

lemma cnt_shift (o : ℤ → Bool) (m a b : ℤ) :
    cnt (fun x => o (x + m)) a b = cnt o (a + m) (b + m) := by
  simp [cnt, ncount_shift]

lemma idx_shift (o : ℤ → Bool) (m t : ℤ) :
    idx (fun x => o (x + m)) t + idx o m = idx o (t + m) := by
  simp only [idx, cnt_shift, zero_add]
  rw [cnt_add o 0 m (t + m)]; ring

lemma ncount_le (o : ℤ → Bool) (a b : ℤ) : (ncount o a b : ℤ) ≤ max (b - a) 0 := by
  have := Finset.card_filter_le (Finset.Ioc a b) (fun u => o u = true)
  simp only [ncount, Int.card_Ioc] at this ⊢
  omega

lemma abs_idx_le (o : ℤ → Bool) (t : ℤ) : |idx o t| ≤ |t| := by
  simp only [idx]
  rcases le_total 0 t with h | h
  · rw [cnt_of_le o h]; have := ncount_le o 0 t
    rw [abs_of_nonneg (by positivity), abs_of_nonneg h]; omega
  · rw [cnt_of_ge o h]; have := ncount_le o t 0
    rw [abs_of_nonpos (by simp), abs_of_nonpos h]; omega

/-! ## The selection rule -/

variable {q : ℕ}

/-- The colour of the old marker `t`. -/
def col (o : ℤ → Bool) (v : ℤ → Fin q) (t : ℤ) : ℕ := (v (idx o t)).val

/-- The sets `A_a` of the selection rule `eq:marker-selection`. -/
def inA (o : ℤ → Bool) (v : ℤ → Fin q) (N : ℕ) : ℕ → ℤ → Bool
  | 0, _ => false
  | a + 1, t => inA o v N a t ||
      (o t && decide (col o v t = a) &&
        decide (∀ u ∈ Finset.Icc (t - N) (t + N), inA o v N a u = false))

/-- The new markers `𝓜_k = A_q`. -/
def sel (o : ℤ → Bool) (v : ℤ → Fin q) (N : ℕ) : ℤ → Bool := inA o v N q

lemma inA_iff (o : ℤ → Bool) (v : ℤ → Fin q) (N : ℕ) (a : ℕ) (t : ℤ) :
    inA o v N a t = true ↔ o t = true ∧ col o v t < a ∧
      ∀ u ∈ Finset.Icc (t - N) (t + N), inA o v N (col o v t) u = false := by
  induction a generalizing t with
  | zero => simp [inA]
  | succ a ih =>
    simp only [inA, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨h1, by omega, h3⟩
      · exact ⟨h1, by omega, h2 ▸ h3⟩
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
      · exact Or.inl ⟨h1, h, h3⟩
      · exact Or.inr ⟨⟨h1, h⟩, h ▸ h3⟩

lemma col_lt (o : ℤ → Bool) (v : ℤ → Fin q) (t : ℤ) : col o v t < q := (v _).isLt

lemma sel_iff (o : ℤ → Bool) (v : ℤ → Fin q) (N : ℕ) (t : ℤ) :
    sel o v N t = true ↔ o t = true ∧
      ∀ u ∈ Finset.Icc (t - N) (t + N), inA o v N (col o v t) u = false := by
  rw [sel, inA_iff]
  exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, col_lt o v t, h3⟩⟩

lemma sel_sub {o : ℤ → Bool} {v : ℤ → Fin q} {N : ℕ} {t : ℤ} (h : sel o v N t = true) :
    o t = true := ((sel_iff o v N t).1 h).1

/-- Maximality: every old marker is within distance `N` of a new marker. -/
lemma sel_maximal {o : ℤ → Bool} (v : ℤ → Fin q) (N : ℕ) {t : ℤ} (ht : o t = true) :
    ∃ u, |t - u| ≤ N ∧ sel o v N u = true := by
  by_cases hs : sel o v N t = true
  · exact ⟨t, by simp, hs⟩
  · rw [sel_iff] at hs
    push Not at hs
    obtain ⟨u, hu, hAu⟩ := hs ht
    have hAu' : inA o v N (col o v t) u = true := by simpa using hAu
    rw [inA_iff] at hAu'
    clear hAu
    have hAu := hAu'
    refine ⟨u, ?_, (sel_iff o v N u).2 ⟨hAu.1, hAu.2.2⟩⟩
    simp only [Finset.mem_Icc] at hu
    rw [abs_le]; constructor <;> omega

/-- Separation: if nearby old markers have different colours, the new markers are
`N`-separated. -/
lemma sel_sep {o : ℤ → Bool} {v : ℤ → Fin q} {N : ℕ}
    (hprop : ∀ t t', o t = true → o t' = true → t ≠ t' → |t - t'| ≤ N → col o v t ≠ col o v t')
    {t t' : ℤ} (ht : sel o v N t = true) (ht' : sel o v N t' = true) (hne : t ≠ t') :
    (N : ℤ) < |t - t'| := by
  by_contra hle
  push Not at hle
  have hc := hprop t t' (sel_sub ht) (sel_sub ht') hne hle
  have key : ∀ s s', sel o v N s = true → sel o v N s' = true → |s - s'| ≤ N →
      col o v s < col o v s' → False := by
    intro s s' hs hs' hss' hlt
    have h1 := ((sel_iff o v N s').1 hs').2 s (by
      simp only [Finset.mem_Icc]; rw [abs_le] at hss'; constructor <;> omega)
    have h2 : inA o v N (col o v s') s = true :=
      (inA_iff o v N _ s).2 ⟨sel_sub hs, hlt, ((sel_iff o v N s).1 hs).2⟩
    simp [h1] at h2
  rcases lt_or_gt_of_ne hc with h | h
  · exact key t t' ht ht' hle h
  · exact key t' t ht' ht (by rw [abs_sub_comm]; exact hle) h

/-! ## Translation equivariance -/

lemma inA_shift (o : ℤ → Bool) (v : ℤ → Fin q) (N : ℕ) (m : ℤ) (a : ℕ) (t : ℤ) :
    inA (fun x => o (x + m)) (fun i => v (i + idx o m)) N a t = inA o v N a (t + m) := by
  induction a generalizing t with
  | zero => rfl
  | succ a ih =>
    simp only [inA, ih]
    congr 2
    · simp only [col, idx_shift]; rfl
    · apply decide_eq_decide.2
      constructor
      · intro h u hu
        have := h (u - m) (by simp only [Finset.mem_Icc] at hu ⊢; omega)
        rwa [sub_add_cancel] at this
      · intro h u hu
        exact h (u + m) (by simp only [Finset.mem_Icc] at hu ⊢; omega)

/-- Translation equivariance of the selection rule. -/
lemma sel_shift (o : ℤ → Bool) (v : ℤ → Fin q) (N : ℕ) (m : ℤ) (t : ℤ) :
    sel (fun x => o (x + m)) (fun i => v (i + idx o m)) N t = sel o v N (t + m) :=
  inA_shift o v N m q t

/-! ## Locality (Lemma `lem:local-selection`) -/

/-- The window `I^{+r}` around a finite set. -/
def thicken (I : Finset ℤ) (r : ℕ) : Finset ℤ := I.biUnion fun i => Finset.Icc (i - r) (i + r)

lemma mem_thicken {I : Finset ℤ} {r : ℕ} {x : ℤ} :
    x ∈ thicken I r ↔ ∃ i ∈ I, |x - i| ≤ r := by
  simp only [thicken, Finset.mem_biUnion, Finset.mem_Icc, abs_le]
  constructor <;> rintro ⟨i, hi, h1, h2⟩ <;> exact ⟨i, hi, by omega, by omega⟩

lemma thicken_mono {I : Finset ℤ} {r s : ℕ} (h : r ≤ s) : thicken I r ⊆ thicken I s :=
  fun x hx => by
    obtain ⟨i, hi, hx⟩ := mem_thicken.1 hx
    exact mem_thicken.2 ⟨i, hi, hx.trans (by exact_mod_cast h)⟩

/-- **Lemma `lem:local-selection`.** -/
lemma inA_local {o o' : ℤ → Bool} {v v' : ℤ → Fin q} {N : ℕ} {I : Finset ℤ}
    (ho : ∀ u ∈ thicken I (q * N), o u = o' u)
    (hv : ∀ u ∈ thicken I (q * N), o u = true → col o v u = col o' v' u) :
    ∀ a ≤ q, ∀ u ∈ thicken I ((q - a) * N), inA o v N a u = inA o' v' N a u := by
  intro a
  induction a with
  | zero => intro _ _ _; rfl
  | succ a ih =>
    intro ha u hu
    have hsub : thicken I ((q - (a + 1)) * N) ⊆ thicken I ((q - a) * N) :=
      thicken_mono (Nat.mul_le_mul_right _ (by omega))
    have hall : thicken I ((q - a) * N) ⊆ thicken I (q * N) :=
      thicken_mono (Nat.mul_le_mul_right _ (by omega))
    have hwin : ∀ w ∈ Finset.Icc (u - N) (u + N), w ∈ thicken I ((q - a) * N) := by
      intro w hw
      obtain ⟨i, hi, hui⟩ := mem_thicken.1 hu
      refine mem_thicken.2 ⟨i, hi, ?_⟩
      simp only [Finset.mem_Icc] at hw
      have : ((q - a) * N : ℕ) = ((q - (a + 1)) * N : ℕ) + N := by
        rw [show q - a = q - (a + 1) + 1 by omega, add_mul, one_mul]
      rw [abs_le] at hui ⊢
      push_cast [this] at hui ⊢
      constructor <;> omega
    simp only [inA]
    rw [ih (by omega) u (hsub hu)]
    have hw : decide (∀ w ∈ Finset.Icc (u - N) (u + N), inA o v N a w = false) =
        decide (∀ w ∈ Finset.Icc (u - N) (u + N), inA o' v' N a w = false) :=
      decide_eq_decide.2 (forall₂_congr fun w hw => by rw [ih (by omega) w (hwin w hw)])
    have hou' := ho u (hall (hsub hu))
    by_cases hou : o u = true
    · have hc := hv u (hall (hsub hu)) hou
      rw [← hou', hc, hw]
    · rw [Bool.not_eq_true] at hou
      rw [← hou', hou]
      simp

lemma sel_local {o o' : ℤ → Bool} {v v' : ℤ → Fin q} {N : ℕ} {I : Finset ℤ}
    (ho : ∀ u ∈ thicken I (q * N), o u = o' u)
    (hv : ∀ u ∈ thicken I (q * N), o u = true → col o v u = col o' v' u) :
    ∀ u ∈ I, sel o v N u = sel o' v' N u := fun u hu =>
  inA_local ho hv q le_rfl u (mem_thicken.2 ⟨u, hu, by simp⟩)

end FiniteOrderMixing
