import FiniteOrderMixing.Bias

/-!
# Nested marker sets and their block partitions (deterministic part of Section `sec:geometry`)

A realisation of the nested marker sets is `h : Hspace = ℕ → ℤ → Bool`, with `h k j = true` iff
`j ∈ 𝓜_k`.  The predicate `Good L h` collects the almost-sure properties used by the later
sections:

* `𝓜_0 = ℤ` and `𝓜_{k+1} ⊆ 𝓜_k`;
* level-`k` markers are `(4L)^k`-separated for `k ≥ 1`;
* every window of `3(4L)^k` consecutive integers contains a level-`k` marker.

These give property `(H1)` of Proposition `prop:hierarchy` (block lengths in
`((4L)^k, 3(4L)^k]`) and property `(H2)` (more than `4L/3 ≥ L` children).

All the block data are defined by *bounded* searches, so that they depend on finitely many
marker indicators for every `h`, good or not.
-/

open Finset

namespace FiniteOrderMixing

/-- Realisations of the nested marker sets: `h k j = true ↔ j ∈ 𝓜_k`. -/
abbrev Hspace := ℕ → ℤ → Bool

variable (L : ℕ)

/-- The block scale `(4L)^k`. -/
def sc (k : ℕ) : ℕ := (4 * L) ^ k

/-- The almost-sure structure of the nested marker sets. -/
structure Good (h : Hspace) : Prop where
  base : ∀ j, h 0 j = true
  nested : ∀ k j, h (k + 1) j = true → h k j = true
  sep : ∀ k, 1 ≤ k → ∀ u v : ℤ, h k u = true → h k v = true → u < v → u + sc L k < v
  dense : ∀ (k : ℕ) (i : ℤ), ∃ j, i ≤ j ∧ j < i + 3 * sc L k ∧ h k j = true

open Classical in
/-- The next level-`k` marker strictly after `a` (searched within distance `3(4L)^k`). -/
noncomputable def nxt (h : Hspace) (k : ℕ) (a : ℤ) : ℤ :=
  if hex : ∃ d : ℕ, 0 < d ∧ d ≤ 3 * sc L k ∧ h k (a + d) = true then a + Nat.find hex
  else a + 1

open Classical in
/-- The last level-`k` marker at or before `i`, i.e. the start of the level-`k` block of `i`. -/
noncomputable def prv (h : Hspace) (k : ℕ) (i : ℤ) : ℤ :=
  if hex : ∃ d : ℕ, d < 3 * sc L k ∧ h k (i - d) = true then i - Nat.find hex else i

/-- The level-`k` block starting at `a`. -/
noncomputable def blk (h : Hspace) (k : ℕ) (a : ℤ) : Finset ℤ := Finset.Ico a (nxt L h k a)

/-- The children of the level-`(k+1)` block at `a`: the level-`k` markers it contains. -/
noncomputable def ch (h : Hspace) (k : ℕ) (a : ℤ) : Finset ℤ :=
  (blk L h (k + 1) a).filter fun c => h k c = true

/-- The first `L` elements of a finite set of integers. -/
def firstOf (S : Finset ℤ) : Finset ℤ := S.filter fun c => (S.filter (· < c)).card < L

/-- The first `L` children. -/
noncomputable def firstL (h : Hspace) (k : ℕ) (a : ℤ) : Finset ℤ := firstOf L (ch L h k a)

/-- The starts of the level-`k` blocks meeting `W`. -/
noncomputable def starts (h : Hspace) (k : ℕ) (W : Finset ℤ) : Finset ℤ := W.image (prv L h k)

/-! ## `firstOf` has exactly `L` elements -/

lemma firstOf_subset (S : Finset ℤ) : firstOf L S ⊆ S := Finset.filter_subset _ _

lemma card_firstOf {S : Finset ℤ} (hS : L ≤ S.card) : (firstOf L S).card = L := by
  set idx : ℤ → ℕ := fun c => (S.filter (· < c)).card
  have hmono : ∀ c ∈ S, ∀ c' ∈ S, c < c' → idx c < idx c' := by
    intro c hc c' hc' hlt
    apply Finset.card_lt_card
    refine ⟨fun x hx => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt⟩
    · have := hsub (Finset.mem_filter.2 ⟨hc, hlt⟩); simp at this
  have hinj : Set.InjOn idx S := by
    intro c hc c' hc' heq
    rcases lt_trichotomy c c' with h | h | h
    · exact absurd heq (hmono c hc c' hc' h).ne
    · exact h
    · exact absurd heq (hmono c' hc' c hc h).ne'
  have hrange : S.image idx ⊆ Finset.range S.card := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_range.2 (Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩)
    have := h hc; simp at this
  have himage : S.image idx = Finset.range S.card :=
    Finset.eq_of_subset_of_card_le hrange (by rw [Finset.card_image_of_injOn hinj]; simp)
  have : (firstOf L S).image idx = Finset.range L := by
    show (S.filter fun c => idx c < L).image idx = _
    rw [← Finset.filter_image (p := fun n => n < L), himage]
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [← Finset.card_image_of_injOn (hinj.mono (firstOf_subset L S)), this, Finset.card_range]

variable {L}

/-! ## Specification of `nxt` and `prv` for good hierarchies -/

section Spec

variable {h : Hspace} (hg : Good L h)
include hg

lemma exists_nxt (k : ℕ) (a : ℤ) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 3 * sc L k ∧ h k (a + d) = true := by
  obtain ⟨j, h1, h2, h3⟩ := hg.dense k (a + 1)
  refine ⟨(j - a).toNat, by omega, by omega, ?_⟩
  rwa [show a + ((j - a).toNat : ℤ) = j by omega]

lemma nxt_eq (k : ℕ) (a : ℤ) : nxt L h k a = a + Nat.find (exists_nxt hg k a) := by
  classical
  simp only [nxt]; rw [dite_eq_left_of_eq_true (eq_true (exists_nxt hg k a))]

lemma lt_nxt (k : ℕ) (a : ℤ) : a < nxt L h k a := by
  rw [nxt_eq hg]; have := (Nat.find_spec (exists_nxt hg k a)).1; omega

lemma nxt_le (k : ℕ) (a : ℤ) : nxt L h k a ≤ a + 3 * sc L k := by
  rw [nxt_eq hg]; have := (Nat.find_spec (exists_nxt hg k a)).2.1; omega

lemma nxt_mem (k : ℕ) (a : ℤ) : h k (nxt L h k a) = true := by
  rw [nxt_eq hg]; exact (Nat.find_spec (exists_nxt hg k a)).2.2

lemma not_mem_of_lt_nxt {k : ℕ} {a j : ℤ} (h1 : a < j) (h2 : j < nxt L h k a) :
    h k j = false := by
  rw [nxt_eq hg] at h2
  by_contra hj
  rw [Bool.not_eq_false] at hj
  have hmin := Nat.find_min (exists_nxt hg k a) (m := (j - a).toNat) (by omega)
  apply hmin
  refine ⟨by omega, ?_, ?_⟩
  · have := (Nat.find_spec (exists_nxt hg k a)).2.1; omega
  · rwa [show a + ((j - a).toNat : ℤ) = j by omega]

lemma nxt_le_of_mem {k : ℕ} {a j : ℤ} (h1 : a < j) (hj : h k j = true) : nxt L h k a ≤ j := by
  by_contra hlt
  have := not_mem_of_lt_nxt hg h1 (not_le.1 hlt)
  simp [hj] at this

lemma exists_prv (k : ℕ) (i : ℤ) : ∃ d : ℕ, d < 3 * sc L k ∧ h k (i - d) = true := by
  obtain ⟨j, h1, h2, h3⟩ := hg.dense k (i - 3 * sc L k + 1)
  refine ⟨(i - j).toNat, by omega, ?_⟩
  rwa [show i - ((i - j).toNat : ℤ) = j by omega]

lemma prv_eq (k : ℕ) (i : ℤ) : prv L h k i = i - Nat.find (exists_prv hg k i) := by
  classical
  simp only [prv]; rw [dite_eq_left_of_eq_true (eq_true (exists_prv hg k i))]

lemma prv_le (k : ℕ) (i : ℤ) : prv L h k i ≤ i := by
  rw [prv_eq hg]; omega

lemma prv_gt (k : ℕ) (i : ℤ) : i - 3 * sc L k < prv L h k i := by
  rw [prv_eq hg]; have := (Nat.find_spec (exists_prv hg k i)).1; omega

lemma prv_mem (k : ℕ) (i : ℤ) : h k (prv L h k i) = true := by
  rw [prv_eq hg]; exact (Nat.find_spec (exists_prv hg k i)).2

lemma le_prv_of_mem {k : ℕ} {i j : ℤ} (hji : j ≤ i) (hj : h k j = true) : j ≤ prv L h k i := by
  rw [prv_eq hg]
  by_contra hlt
  have hmin := Nat.find_min (exists_prv hg k i) (m := (i - j).toNat) (by omega)
  apply hmin
  refine ⟨?_, ?_⟩
  · have := (Nat.find_spec (exists_prv hg k i)).1; omega
  · rwa [show i - ((i - j).toNat : ℤ) = j by omega]

lemma lt_nxt_prv (k : ℕ) (i : ℤ) : i < nxt L h k (prv L h k i) := by
  by_contra hle
  have := le_prv_of_mem hg (not_lt.1 hle) (nxt_mem hg k _)
  have := lt_nxt hg k (prv L h k i)
  omega

/-- Within a block the block start is recovered by `prv`. -/
lemma prv_eq_of_mem_blk {k : ℕ} {a i : ℤ} (ha : h k a = true) (hi : i ∈ blk L h k a) :
    prv L h k i = a := by
  simp only [blk, Finset.mem_Ico] at hi
  apply le_antisymm
  · by_contra hlt
    have h1 := prv_le hg k i
    have := not_mem_of_lt_nxt hg (not_le.1 hlt) (lt_of_le_of_lt h1 hi.2)
    simp [prv_mem hg k i] at this
  · exact le_prv_of_mem hg hi.1 ha

lemma mem_blk_prv (k : ℕ) (i : ℤ) : i ∈ blk L h k (prv L h k i) := by
  simp only [blk, Finset.mem_Ico]; exact ⟨prv_le hg k i, lt_nxt_prv hg k i⟩

lemma prv_prv (k : ℕ) (i : ℤ) : prv L h k (prv L h k i) = prv L h k i :=
  prv_eq_of_mem_blk hg (prv_mem hg k i) (by simp [blk, lt_nxt hg])

lemma start_mem_blk (k : ℕ) (a : ℤ) : a ∈ blk L h k a := by simp [blk, lt_nxt hg]

lemma blk_disjoint {k : ℕ} {a a' : ℤ} (ha : h k a = true) (ha' : h k a' = true) (hne : a ≠ a') :
    Disjoint (blk L h k a) (blk L h k a') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  exact hne ((prv_eq_of_mem_blk hg ha hi).symm.trans (prv_eq_of_mem_blk hg ha' hi'))

lemma blk_pairwiseDisjoint (k : ℕ) (S : Finset ℤ) (hS : ∀ a ∈ S, h k a = true) :
    (S : Set ℤ).PairwiseDisjoint (blk L h k) := fun a ha a' ha' hne =>
  blk_disjoint hg (hS a ha) (hS a' ha') hne

lemma card_blk (k : ℕ) (a : ℤ) : ((blk L h k a).card : ℤ) = nxt L h k a - a := by
  simp only [blk, Int.card_Ico]; have := lt_nxt hg k a; omega

lemma card_blk_le (k : ℕ) (a : ℤ) : (blk L h k a).card ≤ 3 * sc L k := by
  have := card_blk hg k a; have := nxt_le hg k a; omega

lemma card_blk_gt {k : ℕ} (hk : 1 ≤ k) {a : ℤ} (ha : h k a = true) :
    sc L k < (blk L h k a).card := by
  have := card_blk hg k a
  have := hg.sep k hk a _ ha (nxt_mem hg k a) (lt_nxt hg k a)
  omega

lemma card_blk_pos (k : ℕ) (a : ℤ) : 0 < (blk L h k a).card := by
  have := card_blk hg k a; have := lt_nxt hg k a; omega

lemma nxt_zero (a : ℤ) : nxt L h 0 a = a + 1 :=
  le_antisymm (nxt_le_of_mem hg (by omega) (hg.base _)) (by have := lt_nxt hg 0 a; omega)

lemma blk_zero (a : ℤ) : blk L h 0 a = {a} := by
  ext i; simp [blk, nxt_zero hg]; omega

lemma prv_zero (i : ℤ) : prv L h 0 i = i :=
  le_antisymm (prv_le hg 0 i) (le_prv_of_mem hg le_rfl (hg.base i))

lemma mem_of_succ {k : ℕ} {j : ℤ} (hj : h (k + 1) j = true) : h k j = true := hg.nested k j hj

lemma mem_of_le {k ℓ : ℕ} (hkℓ : k ≤ ℓ) {j : ℤ} (hj : h ℓ j = true) : h k j = true := by
  induction ℓ, hkℓ using Nat.le_induction with
  | base => exact hj
  | succ ℓ _ ih => exact ih (hg.nested ℓ j hj)

/-! ## Children -/

lemma nxt_le_nxt_succ {k : ℕ} {a c : ℤ} (hc : c ∈ blk L h (k + 1) a) :
    nxt L h k c ≤ nxt L h (k + 1) a := by
  simp only [blk, Finset.mem_Ico] at hc
  exact nxt_le_of_mem hg hc.2 (hg.nested k _ (nxt_mem hg (k + 1) a))

lemma blk_subset_of_ch {k : ℕ} {a c : ℤ} (hc : c ∈ ch L h k a) :
    blk L h k c ⊆ blk L h (k + 1) a := by
  simp only [ch, Finset.mem_filter] at hc
  have h1 := nxt_le_nxt_succ hg hc.1
  intro j hj
  simp only [blk, Finset.mem_Ico] at hc hj ⊢
  omega

omit hg in
lemma ch_mem {k : ℕ} {a c : ℤ} (hc : c ∈ ch L h k a) : h k c = true :=
  (Finset.mem_filter.1 hc).2

/-- A level-`(k+1)` block is the disjoint union of the blocks of its children. -/
lemma blk_succ_eq {k : ℕ} {a : ℤ} (ha : h (k + 1) a = true) :
    blk L h (k + 1) a = (ch L h k a).biUnion (blk L h k) := by
  ext j
  simp only [Finset.mem_biUnion]
  constructor
  · intro hj
    refine ⟨prv L h k j, ?_, mem_blk_prv hg k j⟩
    simp only [ch, Finset.mem_filter, blk, Finset.mem_Ico] at hj ⊢
    refine ⟨⟨le_prv_of_mem hg hj.1 (hg.nested k a ha), ?_⟩, prv_mem hg k j⟩
    exact lt_of_le_of_lt (prv_le hg k j) hj.2
  · rintro ⟨c, hc, hj⟩; exact blk_subset_of_ch hg hc hj

lemma ch_pairwiseDisjoint (k : ℕ) (a : ℤ) :
    ((ch L h k a : Finset ℤ) : Set ℤ).PairwiseDisjoint (blk L h k) :=
  blk_pairwiseDisjoint hg k _ fun _ hc => ch_mem hc

lemma card_blk_succ {k : ℕ} {a : ℤ} (ha : h (k + 1) a = true) :
    (blk L h (k + 1) a).card = ∑ c ∈ ch L h k a, (blk L h k c).card := by
  rw [blk_succ_eq hg ha, Finset.card_biUnion (ch_pairwiseDisjoint hg k a)]

/-- `(H2)`: every block has at least `L` children (in fact more than `4L/3`). -/
lemma card_ch_ge {k : ℕ} {a : ℤ} (ha : h (k + 1) a = true) : L ≤ (ch L h k a).card := by
  have h1 := card_blk_gt hg (Nat.succ_pos k) ha
  rw [card_blk_succ hg ha] at h1
  have h2 : ∑ c ∈ ch L h k a, (blk L h k c).card ≤ (ch L h k a).card * (3 * sc L k) := by
    have := Finset.sum_le_sum (s := ch L h k a) fun c _ => card_blk_le hg k c
    simpa using this
  have h3 : sc L (k + 1) = 4 * L * sc L k := by simp only [sc]; ring
  have hpos : 0 < sc L k ∨ L = 0 := by
    rcases Nat.eq_zero_or_pos L with h | h
    · exact Or.inr h
    · exact Or.inl (by simp only [sc]; positivity)
  rcases hpos with hpos | hL
  · by_contra hlt
    push Not at hlt
    have : (ch L h k a).card * (3 * sc L k) ≤ 4 * L * sc L k := by
      have : (ch L h k a).card * 3 ≤ 4 * L := by omega
      calc (ch L h k a).card * (3 * sc L k) = ((ch L h k a).card * 3) * sc L k := by ring
        _ ≤ 4 * L * sc L k := Nat.mul_le_mul_right _ this
    have := lt_of_lt_of_le h1 (h2.trans this)
    rw [h3] at this
    exact lt_irrefl _ this
  · simp [hL]

omit hg in
lemma firstL_subset (k : ℕ) (a : ℤ) : firstL L h k a ⊆ ch L h k a := firstOf_subset L _

lemma card_firstL {k : ℕ} {a : ℤ} (ha : h (k + 1) a = true) : (firstL L h k a).card = L :=
  card_firstOf L (card_ch_ge hg ha)

/-! ## Blocks at different levels -/

/-- The level-`(k+1)` block start of `i` is the level-`(k+1)` block start of its level-`k`
block start. -/
lemma prv_succ_prv (k : ℕ) (i : ℤ) : prv L h (k + 1) (prv L h k i) = prv L h (k + 1) i := by
  apply prv_eq_of_mem_blk hg (prv_mem hg (k + 1) i)
  have hi := mem_blk_prv hg (k + 1) i
  simp only [blk, Finset.mem_Ico] at hi ⊢
  exact ⟨le_prv_of_mem hg hi.1 (hg.nested k _ (prv_mem hg (k + 1) i)),
    lt_of_le_of_lt (prv_le hg k i) hi.2⟩

lemma starts_succ (k : ℕ) (W : Finset ℤ) :
    starts L h (k + 1) W = (starts L h k W).image (prv L h (k + 1)) := by
  simp only [starts, Finset.image_image]
  exact Finset.image_congr fun i _ => (prv_succ_prv hg k i).symm

lemma card_starts_succ_le (k : ℕ) (W : Finset ℤ) :
    (starts L h (k + 1) W).card ≤ (starts L h k W).card := by
  rw [starts_succ hg]; exact Finset.card_image_le

lemma card_starts_mono {k ℓ : ℕ} (hkℓ : k ≤ ℓ) (W : Finset ℤ) :
    (starts L h ℓ W).card ≤ (starts L h k W).card := by
  induction ℓ, hkℓ using Nat.le_induction with
  | base => exact le_rfl
  | succ ℓ _ ih => exact (card_starts_succ_le hg ℓ W).trans ih

lemma starts_mem {k : ℕ} {W : Finset ℤ} {a : ℤ} (ha : a ∈ starts L h k W) : h k a = true := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 ha; exact prv_mem hg k i

lemma subset_biUnion_starts (k : ℕ) (W : Finset ℤ) :
    W ⊆ (starts L h k W).biUnion (blk L h k) := fun i hi =>
  Finset.mem_biUnion.2 ⟨prv L h k i, Finset.mem_image_of_mem _ hi, mem_blk_prv hg k i⟩

lemma mem_starts_iff {k : ℕ} {W : Finset ℤ} {a : ℤ} (ha : h k a = true) :
    a ∈ starts L h k W ↔ ¬ Disjoint (blk L h k a) W := by
  rw [Finset.not_disjoint_iff]
  constructor
  · intro hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hs
    exact ⟨i, mem_blk_prv hg k i, hi⟩
  · rintro ⟨i, hib, hiW⟩
    rw [← prv_eq_of_mem_blk hg ha hib]; exact Finset.mem_image_of_mem _ hiW

/-- A child of a level-`(ℓ+1)` block meeting `W` is a level-`ℓ` block start of `W`. -/
lemma exists_firstL_disjoint {ℓ : ℕ} {a : ℤ} (ha : h (ℓ + 1) a = true) {W : Finset ℤ}
    (hW : (starts L h ℓ W).card < L) :
    ∃ c ∈ firstL L h ℓ a, Disjoint (blk L h ℓ c) W := by
  by_contra hcon
  push Not at hcon
  have hsub : firstL L h ℓ a ⊆ starts L h ℓ W := fun c hc =>
    (mem_starts_iff hg (ch_mem (firstL_subset ℓ a hc))).2 (hcon c hc)
  have := Finset.card_le_card hsub
  rw [card_firstL hg ha] at this
  omega

end Spec

end FiniteOrderMixing
