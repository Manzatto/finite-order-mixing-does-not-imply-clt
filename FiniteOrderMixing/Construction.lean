import FiniteOrderMixing.Selection

/-!
# Construction of the nested marker sets (Section `sec:geometry`)

We fix the stationary finitely dependent colouring of Theorem `thm:colouring`
(`HL.holroyd_liggett_colouring`) and an independent copy `ω k` of it at every level `k ≥ 1`.  The level-`k`
markers are

`mk L ω 0 = ℤ`,   `mk L ω (k+1) = sel (mk L ω k) (ω (k+1)) (4L)^{k+1}`.

This file proves Lemma `lem:geometry` (almost-sure goodness, i.e. `(H1)–(H2)`) and the
measurability of the construction.
-/

open MeasureTheory ProbabilityTheory Finset

namespace FiniteOrderMixing

variable {q : ℕ}

/-- Shift of a colouring by an integer. -/
def shiftZ (z : ℤ) (v : ℤ → Fin q) : ℤ → Fin q := fun i => v (i + z)

/-- The properties of the colouring of Theorem `thm:colouring`. -/
structure ColouringLaw (L q : ℕ) (PV : Measure (ℤ → Fin q)) : Prop where
  prob : IsProbabilityMeasure PV
  stat : MeasurePreserving (shiftZ 1) PV PV
  dep : ∀ I J : Finset ℤ, (∀ i ∈ I, ∀ j ∈ J, ((8 * L : ℕ) : ℤ) < |i - j|) →
    IndepFun (fun V : ℤ → Fin q => fun i : I => V i) (fun V => fun j : J => V j) PV
  proper : ∀ᵐ V ∂PV, ∀ i j : ℤ, 0 < |i - j| → |i - j| ≤ ((4 * L : ℕ) : ℤ) → V i ≠ V j

lemma exists_colouringLaw (L : ℕ) (hL : 1 ≤ L) :
    ∃ q, 4 ≤ q ∧ ∃ PV : Measure (ℤ → Fin q), ColouringLaw L q PV := by
  obtain ⟨q, PV, hq, hprob, hstat, hdep, hprop⟩ :=
    HL.holroyd_liggett_colouring (m := 4 * L) (by omega)
  refine ⟨q, hq, PV, hprob, hstat, fun I J h => hdep I J fun i hi j hj => ?_, hprop⟩
  have := h i hi j hj
  push_cast at this ⊢
  linarith

/-- A colouring proper at range `4L`. -/
def Proper (L : ℕ) (V : ℤ → Fin q) : Prop :=
  ∀ i j : ℤ, 0 < |i - j| → |i - j| ≤ ((4 * L : ℕ) : ℤ) → V i ≠ V j

variable (L : ℕ)

/-- The level-`k` markers. -/
def mk (ω : ℕ → ℤ → Fin q) : ℕ → ℤ → Bool
  | 0 => fun _ => true
  | k + 1 => sel (mk ω k) (ω (k + 1)) (sc L (k + 1))

/-- The nested marker sets. -/
def Mh (ω : ℕ → ℤ → Fin q) : Hspace := fun k => mk L ω k

variable {L}

/-! ## Counting separated markers -/

lemma card_sep_le (G : ℕ) (a : ℤ) : ∀ (S : Finset ℤ) (b : ℤ),
    (∀ x ∈ S, ∀ y ∈ S, x < y → x + G < y) → (∀ x ∈ S, a ≤ x ∧ x ≤ b) → S.Nonempty →
    ((S.card : ℤ) - 1) * (G + 1) ≤ b - a := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro _ _ _ h; exact absurd h (by simp)
  | insert M s hM ih =>
    intro b hsep hab _
    have hMs : M ∉ s := fun h => lt_irrefl M (hM M h)
    rw [Finset.card_insert_of_notMem hMs]
    have hMab := hab M (Finset.mem_insert_self M s)
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs; simp; omega
    · have := ih (M - G - 1) (fun x hx y hy hxy => hsep x (Finset.mem_insert_of_mem hx) y
        (Finset.mem_insert_of_mem hy) hxy) (fun x hx => ⟨(hab x (Finset.mem_insert_of_mem hx)).1,
          by have := hsep x (Finset.mem_insert_of_mem hx) M (Finset.mem_insert_self M s)
               (hM x hx); omega⟩) hs
      push_cast
      nlinarith

lemma ncount_lt_of_sep {o : ℤ → Bool} {G : ℕ}
    (hsep : ∀ u v, o u = true → o v = true → u < v → u + G < v) {t t' : ℤ} (ht : o t = true)
    (htt' : t ≤ t') : (ncount o t t' : ℤ) * (G + 1) ≤ t' - t := by
  classical
  set S := insert t ((Finset.Ioc t t').filter fun u => o u = true)
  have htS : t ∉ (Finset.Ioc t t').filter fun u => o u = true := by simp
  have hcard : S.card = ncount o t t' + 1 := by
    simp only [S, Finset.card_insert_of_notMem htS, ncount]
  have := card_sep_le G t S t' (fun x hx y hy hxy => by
      simp only [S, Finset.mem_insert, Finset.mem_filter] at hx hy
      exact hsep x y (hx.elim (· ▸ ht) (·.2)) (hy.elim (· ▸ ht) (·.2)) hxy)
    (fun x hx => by
      simp only [S, Finset.mem_insert, Finset.mem_filter, Finset.mem_Ioc] at hx
      rcases hx with rfl | ⟨⟨h1, h2⟩, _⟩ <;> constructor <;> omega) ⟨t, Finset.mem_insert_self _ _⟩
  rw [hcard] at this; push_cast at this; linarith

lemma ncount_pos {o : ℤ → Bool} {t t' : ℤ} (ht' : o t' = true) (h : t < t') :
    1 ≤ ncount o t t' := by
  unfold ncount
  exact Finset.card_pos.2 ⟨t', by simp [ht', h]⟩

lemma ncount_true (a b : ℤ) : ncount (fun _ => true) a b = (b - a).toNat := by
  simp [ncount]

/-- Many markers in a long interval (from density). -/
lemma ncount_ge_of_dense {o : ℤ → Bool} {G : ℕ}
    (hdense : ∀ i : ℤ, ∃ j, i ≤ j ∧ j < i + G ∧ o j = true) :
    ∀ (n : ℕ) (a b : ℤ), a + n * G ≤ b → n ≤ ncount o a b := by
  intro n
  induction n with
  | zero => intro _ _ _; exact Nat.zero_le _
  | succ n ih =>
    intro a b hab
    obtain ⟨j, hj1, hj2, hj⟩ := hdense (a + 1)
    have h1 := ih j b (by push_cast at hab ⊢; nlinarith)
    have hsplit := ncount_split o (show a ≤ j by omega) (show j ≤ b by push_cast at hab; nlinarith)
    have := ncount_pos (o := o) hj (show a < j by omega)
    omega

/-! ## Goodness (Lemma `lem:geometry`) -/

variable {ω : ℕ → ℤ → Fin q}

lemma col_ne_of_proper {o : ℤ → Bool} {V : ℤ → Fin q} (hV : Proper L V) {t t' : ℤ}
    (h1 : 0 < |idx o t - idx o t'|) (h2 : |idx o t - idx o t'| ≤ ((4 * L : ℕ) : ℤ)) :
    col o V t ≠ col o V t' := fun h => hV _ _ h1 h2 (Fin.ext h)

lemma sep_dense (hL : 1 ≤ L) (hω : ∀ k, Proper L (ω (k + 1))) : ∀ k : ℕ,
    (1 ≤ k → ∀ u v : ℤ, mk L ω k u = true → mk L ω k v = true → u < v → u + sc L k < v) ∧
    (∀ i : ℤ, ∃ j, i ≤ j ∧ j < i + 3 * sc L k ∧ mk L ω k j = true) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun h => absurd h (by omega), fun i => ⟨i, le_rfl, ?_, rfl⟩⟩
    simp [sc]
  | succ k ih =>
    obtain ⟨ihsep, ihdense⟩ := ih
    have hsc : sc L (k + 1) = 4 * L * sc L k := by simp only [sc]; ring
    have hsck := Nat.one_le_pow k (4 * L) (by omega)
    -- the colouring separates nearby old markers
    have hprop : ∀ t t', mk L ω k t = true → mk L ω k t' = true → t ≠ t' →
        |t - t'| ≤ sc L (k + 1) → col (mk L ω k) (ω (k + 1)) t ≠ col (mk L ω k) (ω (k + 1)) t' := by
      intro t t' ht ht' hne hd
      have key : ∀ s s', mk L ω k s = true → mk L ω k s' = true → s < s' →
          s' - s ≤ sc L (k + 1) → 0 < idx (mk L ω k) s' - idx (mk L ω k) s ∧
            idx (mk L ω k) s' - idx (mk L ω k) s ≤ ((4 * L : ℕ) : ℤ) := by
        intro s s' hs hs' hlt hd'
        rw [idx_sub _ hlt.le]
        refine ⟨by exact_mod_cast ncount_pos hs' hlt, ?_⟩
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          have e1 : sc L (0 + 1) = 4 * L := by simp [sc]
          rw [e1] at hd'
          simp only [mk, ncount_true]
          push_cast at hd' ⊢; omega
        · have := ncount_lt_of_sep (ihsep hk0) hs hlt.le
          rw [hsc] at hd'
          push_cast at hd' this ⊢
          by_contra hcon
          push Not at hcon
          have : (4 * L : ℤ) * (sc L k + 1) ≤ (ncount (mk L ω k) s s' : ℤ) * (sc L k + 1) :=
            mul_le_mul_of_nonneg_right hcon.le (by positivity)
          nlinarith
      rcases lt_or_gt_of_ne hne with h | h
      · obtain ⟨h1, h2⟩ := key t t' ht ht' h (by rw [abs_sub_comm, abs_of_pos (by omega)] at hd; exact hd)
        exact col_ne_of_proper (hω k) (by rw [abs_sub_comm, abs_of_pos h1]; exact h1)
          (by rw [abs_sub_comm, abs_of_pos h1]; exact h2)
      · obtain ⟨h1, h2⟩ := key t' t ht' ht h (by rw [abs_of_pos (by omega)] at hd; exact hd)
        exact col_ne_of_proper (hω k) (by rw [abs_of_pos h1]; exact h1)
          (by rw [abs_of_pos h1]; exact h2)
    refine ⟨fun _ u v hu hv huv => ?_, fun i => ?_⟩
    · have := sel_sep hprop hu hv huv.ne
      rw [abs_of_neg (by omega)] at this
      omega
    · obtain ⟨t, ht1, ht2, ht⟩ := ihdense (i + sc L (k + 1))
      obtain ⟨u, hu, hsel⟩ := sel_maximal (ω (k + 1)) (sc L (k + 1)) ht
      refine ⟨u, ?_, ?_, hsel⟩ <;> rw [abs_le] at hu
      · omega
      · rw [hsc] at ht2 hu ⊢; push_cast at ht2 hu ⊢
        have : (4 * L : ℤ) * sc L k * 2 + 3 * sc L k ≤ 3 * (4 * L * sc L k) := by nlinarith
        omega

/-- **Lemma `lem:geometry`**: proper colourings give good marker sets. -/
theorem good_Mh (hL : 1 ≤ L) (hω : ∀ k, Proper L (ω (k + 1))) : Good L (Mh L ω) where
  base := fun _ => rfl
  nested := fun _ _ h => sel_sub h
  sep := fun k hk => (sep_dense hL hω k).1 hk
  dense := fun k => (sep_dense hL hω k).2

/-! ## Measurability -/

lemma idx_congr {o o' : ℤ → Bool} {u : ℤ} (h : ∀ x, |x| ≤ |u| → o x = o' x) :
    idx o u = idx o' u := by
  have hn : ∀ a b, (∀ x ∈ Finset.Ioc a b, o x = o' x) → ncount o a b = ncount o' a b :=
    fun a b hab => by
      unfold ncount; congr 1; exact Finset.filter_congr fun x hx => by rw [hab x hx]
  have h1 : ∀ x ∈ Finset.Ioc 0 u, o x = o' x := fun x hx => by
    simp only [Finset.mem_Ioc] at hx
    exact h x (by rw [abs_of_pos hx.1, abs_of_pos (by omega)]; exact hx.2)
  have h2 : ∀ x ∈ Finset.Ioc u 0, o x = o' x := fun x hx => by
    simp only [Finset.mem_Ioc] at hx
    rcases hx.2.lt_or_eq with hlt | heq
    · exact h x (by rw [abs_of_neg hlt, abs_of_neg (by omega)]; omega)
    · exact h x (by rw [heq]; simp)
  simp only [idx, cnt]
  rw [hn 0 u h1, hn u 0 h2]

/-- A function of finitely many coordinates of a pair of configurations is measurable. -/
lemma measurable_of_window {α β : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {γ : Type*} [MeasurableSpace γ] (a0 : α) (b0 : β) {f : (ℤ → α) × (ℤ → β) → γ}
    (W : Finset ℤ) (hf : ∀ x y, (∀ i ∈ W, x.1 i = y.1 i) → (∀ i ∈ W, x.2 i = y.2 i) → f x = f y) :
    Measurable f := by
  classical
  let r : (ℤ → α) × (ℤ → β) → (W → α) × (W → β) := fun x => (fun i => x.1 i, fun i => x.2 i)
  let ext : (W → α) × (W → β) → (ℤ → α) × (ℤ → β) := fun y =>
    (fun i => if h : i ∈ W then y.1 ⟨i, h⟩ else a0, fun i => if h : i ∈ W then y.2 ⟨i, h⟩ else b0)
  have hr : Measurable r := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.mpr fun i => (measurable_pi_apply _).comp measurable_fst
    · exact measurable_pi_iff.mpr fun i => (measurable_pi_apply _).comp measurable_snd
  have hfe : f = (f ∘ ext) ∘ r := funext fun x =>
    hf _ _ (fun i hi => by simp [ext, r, hi]) (fun i hi => by simp [ext, r, hi])
  rw [hfe]
  exact (measurable_of_countable _).comp hr

variable (L) in
lemma measurable_mk (hq : 1 ≤ q) (k : ℕ) : Measurable (fun ω : ℕ → ℤ → Fin q => mk L ω k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    refine measurable_pi_iff.mpr fun t => ?_
    have hF : Measurable (fun x : (ℤ → Bool) × (ℤ → Fin q) => sel x.1 x.2 (sc L (k + 1)) t) := by
      set B : ℕ := t.natAbs + q * sc L (k + 1)
      refine measurable_of_window true ⟨0, hq⟩ (Finset.Icc (-(B : ℤ)) B) fun x y h1 h2 => ?_
      have hB : ∀ u ∈ thicken {t} (q * sc L (k + 1)), |u| ≤ B := fun u hu => by
        obtain ⟨i, hi, hui⟩ := mem_thicken.1 hu
        rw [Finset.mem_singleton] at hi
        rw [hi] at hui
        rw [abs_le] at hui ⊢; simp only [B]; push_cast
        have h3 := le_abs_self t; have h4 := neg_abs_le t
        constructor <;> omega
      refine sel_local (I := {t}) (fun u hu => h1 u ?_) (fun u hu _ => ?_) t (Finset.mem_singleton_self t)
      · have := hB u hu; simp only [Finset.mem_Icc]; rw [abs_le] at this; exact this
      · have hidx : idx x.1 u = idx y.1 u := idx_congr fun z hz => h1 z (by
          have := hz.trans (hB u hu); simp only [Finset.mem_Icc]; rw [abs_le] at this; exact this)
        simp only [col]
        rw [hidx, h2 _ (by
          have := (abs_idx_le y.1 u).trans (hB u hu)
          simp only [Finset.mem_Icc]; rw [abs_le] at this; exact this)]
    exact hF.comp (ih.prodMk (measurable_pi_apply (k + 1)))

variable (L) in
lemma measurable_Mh (hq : 1 ≤ q) : Measurable (Mh L : (ℕ → ℤ → Fin q) → Hspace) :=
  measurable_pi_iff.mpr fun k => measurable_mk L hq k

end FiniteOrderMixing
