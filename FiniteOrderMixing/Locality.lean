import FiniteOrderMixing.LevelExp

/-!
# Translation equivariance and locality of the block data

* `Eh_shiftH` — translating the marker sets translates the finite-level laws (used for
  stationarity of `ν`);
* `Eh_local` — `Eh L h ℓ W F` depends on `h` only through the marker indicators of levels `≤ ℓ` in
  a window of size `O((4L)^ℓ)` around `W` (Step 1 of Lemma `lem:finite-output`);
* `measurable_of_agreeOn` — functions of finitely many marker indicators are measurable.
-/

open Finset MeasureTheory

namespace FiniteOrderMixing

/-- Translation of the marker sets: `(h + m)` has markers `𝓜_k - m`. -/
def shiftH (m : ℤ) (h : Hspace) : Hspace := fun k j => h k (j + m)

@[fun_prop]
lemma measurable_shiftH (m : ℤ) : Measurable (shiftH m) :=
  measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun j =>
    (measurable_pi_apply (j + m)).comp (measurable_pi_apply k)

lemma dite_find_congr {α β : Type*} {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    [Decidable (∃ d, P d)] [Decidable (∃ d, Q d)] (hPQ : ∀ d, P d ↔ Q d)
    (g : α → β) (f₁ : ℕ → α) (f₂ : ℕ → β) (b₁ : α) (b₂ : β) (hf : ∀ n, g (f₁ n) = f₂ n)
    (hb : g b₁ = b₂) :
    g (if hp : ∃ d, P d then f₁ (Nat.find hp) else b₁) =
      (if hq : ∃ d, Q d then f₂ (Nat.find hq) else b₂) := by
  by_cases hp : ∃ d, P d
  · have hq : ∃ d, Q d := let ⟨d, hd⟩ := hp; ⟨d, (hPQ d).1 hd⟩
    rw [dite_eq_left hp, dite_eq_left hq, hf, Nat.find_congr' (hPQ _)]
  · have hq : ¬ ∃ d, Q d := fun ⟨d, hd⟩ => hp ⟨d, (hPQ d).2 hd⟩
    rw [dite_eq_right hp, dite_eq_right hq, hb]

lemma dite_find_congr' {α : Type*} {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    [Decidable (∃ d, P d)] [Decidable (∃ d, Q d)] (hPQ : ∀ d, P d ↔ Q d) (f : ℕ → α) (b : α) :
    (if hp : ∃ d, P d then f (Nat.find hp) else b) =
      (if hq : ∃ d, Q d then f (Nat.find hq) else b) :=
  dite_find_congr hPQ id f f b b (fun _ => rfl) rfl

variable {L : ℕ}

/-! ## Translation equivariance -/

section Shift

variable (m : ℤ) (h : Hspace)

lemma nxt_shiftH (k : ℕ) (a : ℤ) : nxt L (shiftH m h) k a + m = nxt L h k (a + m) := by
  classical
  unfold nxt
  exact dite_find_congr (fun d => by simp only [shiftH]; rw [add_right_comm])
    (· + m) (fun n => a + n) (fun n => a + m + n) (a + 1) (a + m + 1)
    (fun n => by ring) (by ring)

lemma prv_shiftH (k : ℕ) (i : ℤ) : prv L (shiftH m h) k i + m = prv L h k (i + m) := by
  classical
  unfold prv
  exact dite_find_congr (fun d => by simp only [shiftH]; rw [sub_add_eq_add_sub])
    (· + m) (fun n => i - n) (fun n => i + m - n) i (i + m)
    (fun n => by ring) rfl

lemma blk_shiftH (k : ℕ) (a : ℤ) : blk L (shiftH m h) k a = tr (-m) (blk L h k (a + m)) := by
  ext j
  have := nxt_shiftH (L := L) m h k a
  simp only [blk, mem_tr, Finset.mem_Ico, sub_neg_eq_add]
  omega

lemma ch_shiftH (k : ℕ) (a : ℤ) : ch L (shiftH m h) k a = tr (-m) (ch L h k (a + m)) := by
  ext j
  simp only [ch, Finset.mem_filter, blk_shiftH, mem_tr, sub_neg_eq_add, shiftH]

lemma firstOf_tr (S : Finset ℤ) (n : ℤ) : firstOf L (tr n S) = tr n (firstOf L S) := by
  ext j
  simp only [firstOf, Finset.mem_filter, mem_tr]
  apply and_congr_right
  intro _
  have : (tr n S).filter (· < j) = tr n (S.filter (· < j - n)) := by
    ext x; simp only [Finset.mem_filter, mem_tr]; constructor <;> rintro ⟨h1, h2⟩ <;>
      exact ⟨h1, by omega⟩
  rw [this, card_tr]

lemma firstL_shiftH (k : ℕ) (a : ℤ) :
    firstL L (shiftH m h) k a = tr (-m) (firstL L h k (a + m)) := by
  simp only [firstL, ch_shiftH, firstOf_tr]

lemma prod_tr {n : ℤ} (S : Finset ℤ) (f : ℤ → ℝ) : ∏ c ∈ tr n S, f c = ∏ c ∈ S, f (c + n) := by
  simp [tr, Finset.prod_map]

lemma psi_shiftH_of {k : ℕ}
    (hk : ∀ a ω, rho L (shiftH m h) k a ω = rho L h k (a + m) (transl (-m) ω)) (c : ℤ)
    (ω : Config) : psi L (shiftH m h) k c ω = psi L h k (c + m) (transl (-m) ω) := by
  simp only [psi, psiOf]
  have e1 : tr (-c) (blk L (shiftH m h) k c) = tr (-(c + m)) (blk L h k (c + m)) := by
    rw [blk_shiftH, tr_tr]; congr 1; ring
  have e2 : (fun y => rho L (shiftH m h) k c (transl (-c) y)) =
      fun y => rho L h k (c + m) (transl (-(c + m)) y) := by
    funext y; rw [hk, transl_transl]; congr 2; ring
  rw [e1, e2, transl_transl]
  congr 2; ring

lemma rho_shiftH (k : ℕ) : ∀ a ω, rho L (shiftH m h) k a ω = rho L h k (a + m) (transl (-m) ω) := by
  induction k with
  | zero => intro a ω; rfl
  | succ k ih =>
    intro a ω
    rw [rho_succ, rho_succ, firstL_shiftH, ch_shiftH, prod_tr, prod_tr]
    simp only [psi_shiftH_of m h ih, ih, neg_add_cancel_right]

lemma starts_shiftH (k : ℕ) (W : Finset ℤ) :
    starts L (shiftH m h) k W = tr (-m) (starts L h k (tr m W)) := by
  ext j
  simp only [starts, Finset.mem_image, mem_tr, sub_neg_eq_add]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i + m, by simpa using hi, by rw [← prv_shiftH]⟩
  · rintro ⟨i, hi, hij⟩
    refine ⟨i - m, hi, ?_⟩
    have := prv_shiftH (L := L) m h k (i - m)
    rw [sub_add_cancel, hij] at this
    omega

lemma cover_shiftH (k : ℕ) (W : Finset ℤ) :
    cover L (shiftH m h) k W = tr (-m) (cover L h k (tr m W)) := by
  ext j
  simp only [cover, starts_shiftH, Finset.mem_biUnion, mem_tr, sub_neg_eq_add, blk_shiftH]
  constructor
  · rintro ⟨a, ha, hj⟩; exact ⟨a + m, ha, hj⟩
  · rintro ⟨b, hb, hj⟩; exact ⟨b - m, by simpa using hb, by simpa using hj⟩

/-- Translating the marker sets translates the finite-level laws. -/
theorem Eh_shiftH (ℓ : ℕ) (W : Finset ℤ) (F : Config → ℝ) :
    Eh L (shiftH m h) ℓ W F = Eh L h ℓ (tr m W) (fun ω => F (transl m ω)) := by
  simp only [Eh]
  rw [cover_shiftH, starts_shiftH]
  have e : ∀ ω, (∏ a ∈ tr (-m) (starts L h ℓ (tr m W)), rho L (shiftH m h) ℓ a ω) * F ω =
      (fun ω' => (∏ a ∈ starts L h ℓ (tr m W), rho L h ℓ a ω') * F (transl m ω'))
        (transl (-m) ω) := fun ω => by
    simp only [prod_tr, rho_shiftH, neg_add_cancel_right, transl_transl, add_neg_cancel,
      transl_zero]
  rw [avg_congr e]
  exact avg_transl (-m) (cover L h ℓ (tr m W))
    (fun ω' => (∏ a ∈ starts L h ℓ (tr m W), rho L h ℓ a ω') * F (transl m ω'))

end Shift

/-! ## Locality -/

/-- `h` and `h'` have the same markers of levels `≤ K` in `I`. -/
def AgreeOn (K : ℕ) (I : Finset ℤ) (h h' : Hspace) : Prop :=
  ∀ k ≤ K, ∀ j ∈ I, h k j = h' k j

lemma AgreeOn.mono {K K' : ℕ} {I I' : Finset ℤ} {h h' : Hspace} (hA : AgreeOn K I h h')
    (hK : K' ≤ K) (hI : I' ⊆ I) : AgreeOn K' I' h h' := fun k hk j hj =>
  hA k (hk.trans hK) j (hI hj)

lemma sc_pos (hL : 1 ≤ L) (k : ℕ) : 1 ≤ sc L k := Nat.one_le_pow _ _ (by omega)

lemma sc_succ (k : ℕ) : sc L (k + 1) = 4 * L * sc L k := by simp only [sc]; ring

variable {h h' : Hspace}

lemma nxt_local {K k : ℕ} (hk : k ≤ K) {a : ℤ}
    (hA : AgreeOn K (Finset.Icc (a + 1) (a + 3 * sc L k)) h h') : nxt L h k a = nxt L h' k a := by
  classical
  unfold nxt
  exact dite_find_congr' (fun d => by
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, h2, ?_⟩
      · rw [← hA k hk _ (by simp only [Finset.mem_Icc]; omega)]; exact h3
      · rw [hA k hk _ (by simp only [Finset.mem_Icc]; omega)]; exact h3)
    (fun n : ℕ => a + (n : ℤ)) (a + 1)

lemma prv_local {K k : ℕ} (hk : k ≤ K) {i : ℤ}
    (hA : AgreeOn K (Finset.Icc (i - 3 * sc L k + 1) i) h h') : prv L h k i = prv L h' k i := by
  classical
  unfold prv
  exact dite_find_congr' (fun d => by
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
      · rw [← hA k hk _ (by simp only [Finset.mem_Icc]; omega)]; exact h2
      · rw [hA k hk _ (by simp only [Finset.mem_Icc]; omega)]; exact h2)
    (fun n : ℕ => i - (n : ℤ)) i

lemma lt_nxt_any (h : Hspace) (k : ℕ) (a : ℤ) : a < nxt L h k a := by
  classical
  unfold nxt
  split_ifs with hex
  · have := (Nat.find_spec hex).1; omega
  · omega

lemma nxt_le_any (hL : 1 ≤ L) (h : Hspace) (k : ℕ) (a : ℤ) : nxt L h k a ≤ a + 3 * sc L k := by
  classical
  unfold nxt
  split_ifs with hex
  · have := (Nat.find_spec hex).2.1; omega
  · have := sc_pos hL k; omega

lemma prv_le_any (h : Hspace) (k : ℕ) (i : ℤ) : prv L h k i ≤ i := by
  classical
  unfold prv; split_ifs <;> omega

lemma prv_gt_any (hL : 1 ≤ L) (h : Hspace) (k : ℕ) (i : ℤ) : i - 3 * sc L k < prv L h k i := by
  classical
  unfold prv
  split_ifs with hex
  · have := (Nat.find_spec hex).1; omega
  · have := sc_pos hL k
    omega

lemma blk_local {K k : ℕ} (hk : k ≤ K) {a : ℤ}
    (hA : AgreeOn K (Finset.Icc (a + 1) (a + 3 * sc L k)) h h') : blk L h k a = blk L h' k a := by
  simp only [blk, nxt_local hk hA]

lemma ch_local (hL : 1 ≤ L) {k : ℕ} {a : ℤ}
    (hA : AgreeOn (k + 1) (Finset.Icc a (a + 3 * sc L (k + 1))) h h') :
    ch L h k a = ch L h' k a := by
  have hb : blk L h (k + 1) a = blk L h' (k + 1) a :=
    blk_local le_rfl (hA.mono le_rfl (Finset.Icc_subset_Icc (by omega) le_rfl))
  simp only [ch, ← hb]
  refine Finset.filter_congr fun c hc => ?_
  have := nxt_le_any hL h (k + 1) a
  simp only [blk, Finset.mem_Ico] at hc
  rw [hA k (Nat.le_succ k) c (by simp only [Finset.mem_Icc]; omega)]

lemma rho_local (hL : 1 ≤ L) (k : ℕ) :
    ∀ a, AgreeOn k (Finset.Icc a (a + 4 * sc L k)) h h' → rho L h k a = rho L h' k a := by
  induction k with
  | zero => intro a _; rfl
  | succ k ih =>
    intro a hA
    have h4 : 4 * sc L k ≤ sc L (k + 1) := by
      rw [sc_succ]; exact Nat.mul_le_mul_right _ (by omega)
    have hch := ch_local hL (hA.mono le_rfl (Finset.Icc_subset_Icc le_rfl (by omega)))
    have hc : ∀ c ∈ ch L h k a, AgreeOn k (Finset.Icc c (c + 4 * sc L k)) h h' := by
      intro c hc
      have := nxt_le_any hL h (k + 1) a
      simp only [ch, blk, Finset.mem_filter, Finset.mem_Ico] at hc
      refine hA.mono (Nat.le_succ k) (Finset.Icc_subset_Icc hc.1.1 ?_)
      omega
    funext ω
    rw [rho_succ, rho_succ, firstL, firstL, ← hch]
    congr 1
    · congr 2
      refine Finset.prod_congr rfl fun c hcf => ?_
      have hc' := hc c (firstOf_subset L _ hcf)
      have hs := sc_pos hL k
      simp only [psi]
      rw [ih c hc', blk_local le_rfl (hc'.mono le_rfl (Finset.Icc_subset_Icc (by omega)
        (by omega)))]
    · exact Finset.prod_congr rfl fun c hcc => by rw [ih c (hc c hcc)]

lemma starts_local {ℓ : ℕ} {W : Finset ℤ} {lo hi : ℤ} (hW : ∀ i ∈ W, lo ≤ i ∧ i ≤ hi)
    (hA : AgreeOn ℓ (Finset.Icc (lo - 3 * sc L ℓ) hi) h h') :
    starts L h ℓ W = starts L h' ℓ W := by
  simp only [starts]
  refine Finset.image_congr fun i hi' => ?_
  have := hW i hi'
  exact prv_local le_rfl (hA.mono le_rfl (Finset.Icc_subset_Icc (by omega) this.2))

/-- **Locality** of the finite-level laws (Step 1 of Lemma `lem:finite-output`). -/
theorem Eh_local (hL : 1 ≤ L) {ℓ : ℕ} {W : Finset ℤ} {lo hi : ℤ} (hW : ∀ i ∈ W, lo ≤ i ∧ i ≤ hi)
    (hA : AgreeOn ℓ (Finset.Icc (lo - 3 * sc L ℓ) (hi + 4 * sc L ℓ)) h h') (F : Config → ℝ) :
    Eh L h ℓ W F = Eh L h' ℓ W F := by
  have hs : starts L h ℓ W = starts L h' ℓ W :=
    starts_local hW (hA.mono le_rfl (Finset.Icc_subset_Icc le_rfl (by omega)))
  have ha : ∀ a ∈ starts L h ℓ W, lo - 3 * sc L ℓ < a ∧ a ≤ hi := by
    intro a ha
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 ha
    have := hW i hi'
    have h1 := prv_le_any (L := L) h ℓ i
    have h2 := prv_gt_any hL h ℓ i
    omega
  have hr : ∀ a ∈ starts L h ℓ W, rho L h ℓ a = rho L h' ℓ a := fun a haS =>
    rho_local hL ℓ a (hA.mono le_rfl (Finset.Icc_subset_Icc (by have := ha a haS; omega)
      (by have := ha a haS; omega)))
  have hb : ∀ a ∈ starts L h ℓ W, blk L h ℓ a = blk L h' ℓ a := fun a haS =>
    blk_local le_rfl (hA.mono le_rfl (Finset.Icc_subset_Icc (by have := ha a haS; omega)
      (by have := ha a haS; have := sc_pos hL ℓ; omega)))
  simp only [Eh, cover]
  rw [← hs, Finset.biUnion_congr rfl hb]
  exact avg_congr fun ω => by rw [Finset.prod_congr rfl fun a haS => by rw [hr a haS]]

/-! ## Measurability of local functions -/

/-- A function of finitely many marker indicators is measurable. -/
theorem measurable_of_agreeOn {β : Type*} [MeasurableSpace β] {f : Hspace → β} (K : ℕ)
    (I : Finset ℤ) (hf : ∀ h h', AgreeOn K I h h' → f h = f h') : Measurable f := by
  classical
  let S := Finset.range (K + 1) ×ˢ I
  let r : Hspace → (S → Bool) := fun h p => h p.1.1 p.1.2
  let ext : (S → Bool) → Hspace := fun y k j => if hp : (k, j) ∈ S then y ⟨_, hp⟩ else false
  have hr : Measurable r := measurable_pi_iff.mpr fun p =>
    (measurable_pi_apply p.1.2).comp (measurable_pi_apply p.1.1)
  have hfe : f = (f ∘ ext) ∘ r := by
    funext h
    refine hf _ _ fun k hk j hj => ?_
    have : (k, j) ∈ S := Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), hj⟩
    simp [ext, r, this]
  rw [hfe]
  exact (measurable_of_countable _).comp hr

end FiniteOrderMixing
