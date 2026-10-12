import FiniteOrderMixing.Hierarchy

/-!
# The recursive block laws (Section `sec:block-laws`)

For a realisation `h` of the nested marker sets, every level-`k` block `B = blk L h k a` carries a
density `rho L h k a` with respect to the uniform law on its coordinates:

* `rho L h 0 a = 1` (uniform sign on a singleton);
* `rho L h (k+1) a = (1 - ½ ∏_{c ∈ firstL} ψ_c) · ∏_{c ∈ ch} rho L h k c` (equation `eq:parent-law`),

where `ψ_c = psi L h k c` is the auxiliary function of Lemma `lem:bias` for the law of the child `c`.
The choice of `ψ` is made by `psiStd` for the law translated to start at `0`, so that it depends
only on the shape of the block and not on its position (this is the paper's "fix, once and for
all, one admissible function for each law").

Main results:
* `blockProps` — Lemma `lem:block-properties` (i)–(ii): `rho` is a positive, sign-symmetric law
  whose characters of `1 ≤ |K| ≤ L-1` coordinates have mean zero;
* `avg_rho_succ_chi` — the product expansion `eq:block-correlation-expansion`;
* `block_corr_nonpos`, `block_corr_val` — Lemma `lem:block-correlations`.
-/

open Finset

namespace FiniteOrderMixing

/-! ## Translation lemmas -/

lemma tr_tr (m n : ℤ) (B : Finset ℤ) : tr m (tr n B) = tr (m + n) B := by
  ext j; simp [mem_tr, sub_sub]

lemma tr_zero (B : Finset ℤ) : tr 0 B = B := by ext j; simp [mem_tr]

lemma tr_subset_tr {m : ℤ} {A B : Finset ℤ} (h : A ⊆ B) : tr m A ⊆ tr m B := fun j hj => by
  rw [mem_tr] at hj ⊢; exact h hj

lemma transl_flipOn (m : ℤ) (B : Finset ℤ) (y : Config) :
    transl m (flipOn (tr m B) y) = flipOn B (transl m y) := by
  funext j; simp [flipOn, mem_tr]

lemma chi_transl (m : ℤ) (K : Finset ℤ) (ω : Config) :
    chi K (transl m ω) = chi (tr m K) ω := by
  simp [chi, tr, Finset.prod_map, Z]

lemma Z_transl (m j : ℤ) (ω : Config) : Z j (transl m ω) = Z (j + m) ω := rfl

/-! ## The choice of `ψ` -/

open Classical in
/-- A fixed choice of an admissible `ψ` for the law `w` on `B` (zero if none exists). -/
noncomputable def psiStd (B : Finset ℤ) (w : Config → ℝ) : Config → ℝ :=
  if hex : ∃ ψ, IsBias B w ψ then Classical.choose hex else fun _ => 0

lemma psiStd_spec {B : Finset ℤ} {w : Config → ℝ} (hex : ∃ ψ, IsBias B w ψ) :
    IsBias B w (psiStd B w) := by
  classical
  simp only [psiStd, dite_eq_left_of_eq_true (eq_true hex)]
  exact Classical.choose_spec hex

/-- The auxiliary function for a law `w` on a block `B` starting at `c`: the standard choice for
the translated law, translated back. -/
noncomputable def psiOf (B : Finset ℤ) (w : Config → ℝ) (c : ℤ) : Config → ℝ :=
  fun ω => psiStd (tr (-c) B) (fun y => w (transl (-c) y)) (transl c ω)

lemma psiOf_isBias {B : Finset ℤ} {w : Config → ℝ} (c : ℤ) (hw : IsLaw B w) (he : IsEven B w)
    (hm : ∀ K ⊆ B, K.Nonempty → K.card ≤ 4 → avg B (fun ω => w ω * chi K ω) = 0) :
    IsBias B w (psiOf B w c) := by
  set B' := tr (-c) B with hB'
  set w0 : Config → ℝ := fun y => w (transl (-c) y) with hw0def
  have hBB : tr c B' = B := by rw [hB', tr_tr]; simp [tr_zero]
  have hw0 : IsLaw B' w0 :=
    ⟨hw.dep.transl (-c), fun y => hw.nonneg _, by rw [avg_transl]; exact hw.avg_eq_one⟩
  have he0 : IsEven B' w0 := fun y => by
    simp only [w0, hB', transl_flipOn]
    exact he _
  have hm0 : ∀ K ⊆ B', K.Nonempty → K.card ≤ 4 → avg B' (fun y => w0 y * chi K y) = 0 := by
    intro K hK hne hcard
    have e : ∀ y, w0 y * chi K y = (fun ω => w ω * chi (tr c K) ω) (transl (-c) y) := fun y => by
      simp only [w0, chi_transl, tr_tr, neg_add_cancel, tr_zero]
    rw [avg_congr e]
    refine (avg_transl (-c) B (fun ω => w ω * chi (tr c K) ω)).trans ?_
    refine hm _ ?_ (by simpa [tr] using hne) (by simpa using hcard)
    rw [← hBB]; exact tr_subset_tr hK
  have hψ0 := psiStd_spec (exists_bias hw0 he0 hm0)
  set ψ0 := psiStd B' w0
  refine ⟨?_, fun ω => hψ0.bound _, ?_, ?_⟩
  · have := hψ0.dep.transl c
    rw [hBB] at this
    exact this
  · intro ω
    show ψ0 (transl c (flipOn B ω)) = -ψ0 (transl c ω)
    rw [← hBB, transl_flipOn, hψ0.odd]
  · intro j hj
    show avg B (fun ω => w ω * Z j ω * ψ0 (transl c ω)) = _
    have e : ∀ ω, w ω * Z j ω * ψ0 (transl c ω) =
        (fun y => w0 y * Z (j - c) y * ψ0 y) (transl c ω) := fun ω => by
      simp only [w0, transl_transl, neg_add_cancel, transl_zero, Z_transl, sub_add_cancel]
    rw [avg_congr e, ← hBB]
    refine (avg_transl c B' (fun y => w0 y * Z (j - c) y * ψ0 y)).trans ?_
    rw [card_tr]
    exact hψ0.corr (j - c) (by rw [hB', mem_tr]; simpa using hj)

/-! ## The recursive block laws -/

variable (L : ℕ)

/-- The block laws, equation `eq:parent-law`. -/
noncomputable def rho (h : Hspace) : ℕ → ℤ → Config → ℝ
  | 0, _ => fun _ => 1
  | k + 1, a => fun ω =>
      (1 - 1 / 2 * ∏ c ∈ firstL L h k a, psiOf (blk L h k c) (rho h k c) c ω) *
        ∏ c ∈ ch L h k a, rho h k c ω

/-- The auxiliary function `ψ_c` of the level-`k` block starting at `c`. -/
noncomputable def psi (h : Hspace) (k : ℕ) (c : ℤ) : Config → ℝ :=
  psiOf (blk L h k c) (rho L h k c) c

lemma rho_zero (h : Hspace) (a : ℤ) (ω : Config) : rho L h 0 a ω = 1 := rfl

lemma rho_succ (h : Hspace) (k : ℕ) (a : ℤ) (ω : Config) :
    rho L h (k + 1) a ω =
      (1 - 1 / 2 * ∏ c ∈ firstL L h k a, psi L h k c ω) * ∏ c ∈ ch L h k a, rho L h k c ω := rfl

/-- The properties of Lemma `lem:block-properties` (i)–(ii), plus positivity. -/
structure BlockProps (B : Finset ℤ) (ρ : Config → ℝ) : Prop where
  law : IsLaw B ρ
  even : IsEven B ρ
  pos : ∀ ω, 0 < ρ ω
  mom : ∀ K ⊆ B, K.Nonempty → K.card ≤ L - 1 → avg B (fun ω => ρ ω * chi K ω) = 0

variable {L}

section Laws

variable {h : Hspace} (hg : Good L h)
include hg

/-- Characters factor along the children of a block. -/
lemma chi_eq_prod_ch {k : ℕ} {a : ℤ} (ha : h (k + 1) a = true) {J : Finset ℤ}
    (hJ : J ⊆ blk L h (k + 1) a) (ω : Config) :
    chi J ω = ∏ c ∈ ch L h k a, chi (J ∩ blk L h k c) ω := by
  classical
  have hJ' : J = (ch L h k a).biUnion fun c => J ∩ blk L h k c := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hj
      have := hJ hj
      rw [blk_succ_eq hg ha, Finset.mem_biUnion] at this
      obtain ⟨c, hc, hjc⟩ := this
      exact ⟨c, hc, hj, hjc⟩
    · rintro ⟨c, _, hj, _⟩; exact hj
  have hdisj : ((ch L h k a : Finset ℤ) : Set ℤ).PairwiseDisjoint fun c => J ∩ blk L h k c :=
    fun c hc c' hc' hne => Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right
        (ch_pairwiseDisjoint hg k a hc hc' hne))
  conv_lhs => rw [hJ']
  simp only [chi]
  rw [Finset.prod_biUnion hdisj]

lemma avg_prod_ch {k : ℕ} {a : ℤ} (ha : h (k + 1) a = true) (F : ℤ → Config → ℝ)
    (hF : ∀ c ∈ ch L h k a, Dep (F c) (blk L h k c)) :
    avg (blk L h (k + 1) a) (fun ω => ∏ c ∈ ch L h k a, F c ω) =
      ∏ c ∈ ch L h k a, avg (blk L h k c) (F c) := by
  classical
  rw [blk_succ_eq hg ha]
  exact avg_biUnion_prod _ _ (ch_pairwiseDisjoint hg k a) F hF

/-- The expansion `eq:block-correlation-expansion` of `E_{ρ_B}[χ_J]` along the children. -/
lemma avg_rho_succ_chi {k : ℕ} {a : ℤ} (ha : h (k + 1) a = true)
    (hdep : ∀ c ∈ ch L h k a, Dep (rho L h k c) (blk L h k c) ∧ Dep (psi L h k c) (blk L h k c))
    {J : Finset ℤ} (hJ : J ⊆ blk L h (k + 1) a) :
    avg (blk L h (k + 1) a) (fun ω => rho L h (k + 1) a ω * chi J ω) =
      ∏ c ∈ ch L h k a, avg (blk L h k c) (fun ω => rho L h k c ω * chi (J ∩ blk L h k c) ω) -
      1 / 2 * ∏ c ∈ ch L h k a, avg (blk L h k c) (fun ω => rho L h k c ω *
        chi (J ∩ blk L h k c) ω * (if c ∈ firstL L h k a then psi L h k c ω else 1)) := by
  classical
  have hpt : ∀ ω, rho L h (k + 1) a ω * chi J ω =
      (∏ c ∈ ch L h k a, rho L h k c ω * chi (J ∩ blk L h k c) ω) -
      1 / 2 * ∏ c ∈ ch L h k a, (rho L h k c ω * chi (J ∩ blk L h k c) ω *
        (if c ∈ firstL L h k a then psi L h k c ω else 1)) := fun ω => by
    rw [rho_succ, chi_eq_prod_ch hg ha hJ, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_ite_mem,
      Finset.inter_eq_right.2 (firstL_subset k a)]
    ring
  rw [avg_congr hpt]
  rw [show (fun ω => (∏ c ∈ ch L h k a, rho L h k c ω * chi (J ∩ blk L h k c) ω) -
      1 / 2 * ∏ c ∈ ch L h k a, (rho L h k c ω * chi (J ∩ blk L h k c) ω *
        (if c ∈ firstL L h k a then psi L h k c ω else 1))) =
      (fun ω => ∏ c ∈ ch L h k a, rho L h k c ω * chi (J ∩ blk L h k c) ω) -
      (fun ω => 1 / 2 * ∏ c ∈ ch L h k a, (rho L h k c ω * chi (J ∩ blk L h k c) ω *
        (if c ∈ firstL L h k a then psi L h k c ω else 1))) from rfl,
    avg_sub, avg_const_mul]
  have hchi : ∀ c ∈ ch L h k a, Dep (chi (J ∩ blk L h k c)) (blk L h k c) := fun c _ =>
    (dep_chi _).mono Finset.inter_subset_right
  rw [avg_prod_ch hg ha (fun c ω => rho L h k c ω * chi (J ∩ blk L h k c) ω)
      fun c hc => (hdep c hc).1.mul (hchi c hc),
    avg_prod_ch hg ha (fun c ω => rho L h k c ω * chi (J ∩ blk L h k c) ω *
      (if c ∈ firstL L h k a then psi L h k c ω else 1)) fun c hc => by
      refine ((hdep c hc).1.mul (hchi c hc)).mul ?_
      split_ifs
      · exact (hdep c hc).2
      · exact dep_const _ _]

/-- Pigeonhole: `L` indices spread over the `L` first children, one in each. -/
lemma card_inter_eq_one {k : ℕ} {a : ℤ} (ha : h (k + 1) a = true) {J : Finset ℤ}
    (hJ : J ⊆ blk L h (k + 1) a) (hcard : J.card = L)
    (hout : ∀ c ∈ ch L h k a, c ∉ firstL L h k a → J ∩ blk L h k c = ∅)
    (hin : ∀ c ∈ firstL L h k a, (J ∩ blk L h k c).Nonempty) :
    ∀ c ∈ firstL L h k a, (J ∩ blk L h k c).card = 1 := by
  classical
  have hJ' : J = (firstL L h k a).biUnion fun c => J ∩ blk L h k c := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hj
      have := hJ hj
      rw [blk_succ_eq hg ha, Finset.mem_biUnion] at this
      obtain ⟨c, hc, hjc⟩ := this
      by_cases hcf : c ∈ firstL L h k a
      · exact ⟨c, hcf, hj, hjc⟩
      · have := hout c hc hcf
        have : j ∈ J ∩ blk L h k c := Finset.mem_inter.2 ⟨hj, hjc⟩
        simp_all
    · rintro ⟨c, _, hj, _⟩; exact hj
  have hdisj : ((firstL L h k a : Finset ℤ) : Set ℤ).PairwiseDisjoint
      fun c => J ∩ blk L h k c :=
    fun c hc c' hc' hne => Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right
        (ch_pairwiseDisjoint hg k a (firstL_subset k a hc) (firstL_subset k a hc') hne))
  have hsum : ∑ c ∈ firstL L h k a, (J ∩ blk L h k c).card = ∑ _c ∈ firstL L h k a, 1 := by
    rw [← Finset.card_biUnion hdisj, ← hJ', hcard, Finset.sum_const, card_firstL hg ha,
      smul_eq_mul, mul_one]
  intro c hc
  exact ((Finset.sum_eq_sum_iff_of_le fun c hc =>
    Finset.card_pos.2 (hin c hc)).1 hsum.symm c hc).symm


variable (hL : 6 ≤ L) (hLe : Even L)
include hL hLe

/-- **Lemma `lem:block-properties`** (i)–(ii). -/
theorem blockProps (k : ℕ) : ∀ a, h k a = true → BlockProps L (blk L h k a) (rho L h k a) := by
  induction k with
  | zero =>
    intro a _
    rw [blk_zero hg]
    refine ⟨⟨dep_const _ _, fun _ => zero_le_one, avg_const _ _⟩, fun _ => rfl,
      fun _ => zero_lt_one, fun K hK hne _ => ?_⟩
    simp only [rho_zero, one_mul]
    exact avg_chi hK hne
  | succ k ih =>
    intro a ha
    have hch : ∀ c ∈ ch L h k a, BlockProps L (blk L h k c) (rho L h k c) :=
      fun c hc => ih c (ch_mem hc)
    have hbias : ∀ c ∈ ch L h k a, IsBias (blk L h k c) (rho L h k c) (psi L h k c) :=
      fun c hc => psiOf_isBias c (hch c hc).law (hch c hc).even
        fun K hK hne hcard => (hch c hc).mom K hK hne (by omega)
    have hdep : ∀ c ∈ ch L h k a,
        Dep (rho L h k c) (blk L h k c) ∧ Dep (psi L h k c) (blk L h k c) :=
      fun c hc => ⟨(hch c hc).law.dep, (hbias c hc).dep⟩
    have hsub : ∀ c ∈ ch L h k a, blk L h k c ⊆ blk L h (k + 1) a :=
      fun c hc => blk_subset_of_ch hg hc
    -- the factor of the `ψ`-term at a first child missing `J` vanishes
    have hzero : ∀ J : Finset ℤ, (∃ c0 ∈ firstL L h k a, Disjoint (blk L h k c0) J) →
        ∏ c ∈ ch L h k a, avg (blk L h k c) (fun ω => rho L h k c ω *
          chi (J ∩ blk L h k c) ω * (if c ∈ firstL L h k a then psi L h k c ω else 1)) = 0 := by
      rintro J ⟨c0, hc0, hdisj⟩
      apply Finset.prod_eq_zero (firstL_subset k a hc0)
      have : J ∩ blk L h k c0 = ∅ := by
        rw [Finset.inter_comm]; exact Finset.disjoint_iff_inter_eq_empty.1 hdisj
      rw [this]; simp only [hc0, ↓reduceIte]
      simpa using (hbias c0 (firstL_subset k a hc0)).avg_eq_zero
        (hch c0 (firstL_subset k a hc0)).even
    have hne_first : (firstL L h k a).Nonempty := by
      rw [← Finset.card_pos, card_firstL hg ha]; omega
    refine ⟨⟨?_, fun ω => ?_, ?_⟩, ?_, ?_, ?_⟩
    · -- dependence
      intro ω ω' hω
      rw [rho_succ, rho_succ]
      congr 1
      · congr 2
        exact Finset.prod_congr rfl fun c hc =>
          (hdep c (firstL_subset k a hc)).2 _ _ fun j hj =>
            hω j (hsub c (firstL_subset k a hc) hj)
      · exact Finset.prod_congr rfl fun c hc =>
          (hdep c hc).1 _ _ fun j hj => hω j (hsub c hc hj)
    · -- nonnegativity (in fact positivity, proved below)
      have hΨ : |∏ c ∈ firstL L h k a, psi L h k c ω| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
          fun c hc => (hbias c (firstL_subset k a hc)).bound ω
      have h1 : 0 ≤ 1 - 1 / 2 * ∏ c ∈ firstL L h k a, psi L h k c ω := by
        have := (abs_le.1 hΨ).2; linarith
      rw [rho_succ]
      exact mul_nonneg h1 (Finset.prod_nonneg fun c hc => ((hch c hc).pos ω).le)
    · -- total mass one
      have := avg_rho_succ_chi hg ha hdep (Finset.empty_subset _)
      rw [hzero ∅ ⟨_, hne_first.choose_spec, Finset.disjoint_empty_right _⟩, mul_zero,
        sub_zero] at this
      simp only [Finset.empty_inter, chi_empty, mul_one] at this
      rw [show (fun ω => rho L h (k + 1) a ω) = rho L h (k + 1) a from rfl] at this
      rw [this, Finset.prod_eq_one fun c hc => (hch c hc).law.avg_eq_one]
    · -- sign symmetry
      intro ω
      have hflip : ∀ c ∈ ch L h k a, ∀ F : Config → ℝ, Dep F (blk L h k c) →
          F (flipOn (blk L h (k + 1) a) ω) = F (flipOn (blk L h k c) ω) := fun c hc F hF =>
        hF _ _ fun j hj => by simp [flipOn, hj, hsub c hc hj]
      rw [rho_succ, rho_succ]
      congr 1
      · congr 2
        rw [Finset.prod_congr rfl fun c hc => by
          rw [hflip c (firstL_subset k a hc) _ (hdep c (firstL_subset k a hc)).2,
            (hbias c (firstL_subset k a hc)).odd]]
        rw [Finset.prod_neg, card_firstL hg ha, hLe.neg_one_pow, one_mul]
      · exact Finset.prod_congr rfl fun c hc => by
          rw [hflip c hc _ (hdep c hc).1, (hch c hc).even]
    · -- positivity
      intro ω
      have hΨ : |∏ c ∈ firstL L h k a, psi L h k c ω| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
          fun c hc => (hbias c (firstL_subset k a hc)).bound ω
      have h1 : 0 < 1 - 1 / 2 * ∏ c ∈ firstL L h k a, psi L h k c ω := by
        have := (abs_le.1 hΨ).2; linarith
      rw [rho_succ]
      exact mul_pos h1 (Finset.prod_pos fun c hc => (hch c hc).pos ω)
    · -- vanishing of the characters of at most `L - 1` coordinates
      intro K hK hne hcard
      rw [avg_rho_succ_chi hg ha hdep hK]
      have hstarts : (starts L h k K).card < L :=
        lt_of_le_of_lt Finset.card_image_le (by omega)
      rw [hzero K (exists_firstL_disjoint hg ha hstarts), mul_zero, sub_zero]
      obtain ⟨j, hj⟩ := hne
      have hjB := hK hj
      rw [blk_succ_eq hg ha, Finset.mem_biUnion] at hjB
      obtain ⟨c, hc, hjc⟩ := hjB
      apply Finset.prod_eq_zero hc
      exact (hch c hc).mom _ Finset.inter_subset_right ⟨j, Finset.mem_inter.2 ⟨hj, hjc⟩⟩
        ((Finset.card_le_card Finset.inter_subset_left).trans hcard)

/-! ## `L`-point correlations (Lemma `lem:block-correlations`) -/

/-- Every `L`-point correlation of a block law is nonpositive. -/
theorem block_corr_nonpos (k : ℕ) : ∀ a, h k a = true → ∀ J ⊆ blk L h k a, J.card = L →
    avg (blk L h k a) (fun ω => rho L h k a ω * chi J ω) ≤ 0 := by
  induction k with
  | zero =>
    intro a _ J hJ hcard
    rw [blk_zero hg] at hJ
    have := Finset.card_le_card hJ
    simp at this; omega
  | succ k ih =>
    intro a ha J hJ hcard
    have hch : ∀ c ∈ ch L h k a, BlockProps L (blk L h k c) (rho L h k c) :=
      fun c hc => blockProps hg hL hLe k c (ch_mem hc)
    have hbias : ∀ c ∈ ch L h k a, IsBias (blk L h k c) (rho L h k c) (psi L h k c) :=
      fun c hc => psiOf_isBias c (hch c hc).law (hch c hc).even
        fun K hK hne hcard => (hch c hc).mom K hK hne (by omega)
    have hdep : ∀ c ∈ ch L h k a,
        Dep (rho L h k c) (blk L h k c) ∧ Dep (psi L h k c) (blk L h k c) :=
      fun c hc => ⟨(hch c hc).law.dep, (hbias c hc).dep⟩
    rw [avg_rho_succ_chi hg ha hdep hJ]
    by_cases hA : ∃ c ∈ ch L h k a, J ⊆ blk L h k c
    · -- all the indices lie in one child
      obtain ⟨c, hc, hJc⟩ := hA
      have hT1 : ∏ c' ∈ ch L h k a, avg (blk L h k c')
          (fun ω => rho L h k c' ω * chi (J ∩ blk L h k c') ω) =
          avg (blk L h k c) (fun ω => rho L h k c ω * chi J ω) := by
        rw [← Finset.mul_prod_erase _ _ hc, Finset.inter_eq_left.2 hJc]
        rw [Finset.prod_eq_one fun c' hc' => ?_, mul_one]
        have hne : c' ≠ c := Finset.ne_of_mem_erase hc'
        have : J ∩ blk L h k c' = ∅ := Finset.disjoint_iff_inter_eq_empty.1
          (Finset.disjoint_of_subset_left hJc
            (ch_pairwiseDisjoint hg k a hc (Finset.mem_of_mem_erase hc') hne.symm))
        rw [this]
        simpa using (hch c' (Finset.mem_of_mem_erase hc')).law.avg_eq_one
      obtain ⟨c0, hc0, hc0ne⟩ : ∃ c0 ∈ firstL L h k a, c0 ≠ c := by
        by_contra hcon
        push Not at hcon
        have : firstL L h k a ⊆ {c} := fun x hx => by simpa using hcon x hx
        have := Finset.card_le_card this
        rw [card_firstL hg ha] at this; simp at this; omega
      have hT2 : ∏ c' ∈ ch L h k a, avg (blk L h k c') (fun ω => rho L h k c' ω *
          chi (J ∩ blk L h k c') ω * (if c' ∈ firstL L h k a then psi L h k c' ω else 1)) = 0 := by
        apply Finset.prod_eq_zero (firstL_subset k a hc0)
        have : J ∩ blk L h k c0 = ∅ := Finset.disjoint_iff_inter_eq_empty.1
          (Finset.disjoint_of_subset_left hJc
            (ch_pairwiseDisjoint hg k a hc (firstL_subset k a hc0) hc0ne.symm))
        rw [this]; simp only [hc0, ↓reduceIte]
        simpa using (hbias c0 (firstL_subset k a hc0)).avg_eq_zero
          (hch c0 (firstL_subset k a hc0)).even
      rw [hT1, hT2, mul_zero, sub_zero]
      exact ih c (ch_mem hc) J hJc hcard
    · -- the indices meet at least two children: the first product vanishes
      push Not at hA
      have hsmall : ∀ c ∈ ch L h k a, (J ∩ blk L h k c).card ≤ L - 1 := by
        intro c hc
        have hlt : (J ∩ blk L h k c).card < J.card := by
          apply Finset.card_lt_card
          refine ⟨Finset.inter_subset_left, fun hsub => hA c hc ?_⟩
          exact fun x hx => (Finset.mem_inter.1 (hsub hx)).2
        omega
      have hJne : J.Nonempty := by rw [← Finset.card_pos]; omega
      obtain ⟨j, hj⟩ := hJne
      have hjB := hJ hj
      rw [blk_succ_eq hg ha, Finset.mem_biUnion] at hjB
      obtain ⟨c1, hc1, hjc1⟩ := hjB
      have hT1 : ∏ c' ∈ ch L h k a, avg (blk L h k c')
          (fun ω => rho L h k c' ω * chi (J ∩ blk L h k c') ω) = 0 :=
        Finset.prod_eq_zero hc1 ((hch c1 hc1).mom _ Finset.inter_subset_right
          ⟨j, Finset.mem_inter.2 ⟨hj, hjc1⟩⟩ (hsmall c1 hc1))
      rw [hT1, zero_sub, neg_nonpos]
      -- the second product is nonnegative
      refine mul_nonneg (by norm_num) ?_
      by_cases hB1 : ∃ c ∈ ch L h k a, c ∉ firstL L h k a ∧ (J ∩ blk L h k c).Nonempty
      · obtain ⟨c, hc, hcf, hne⟩ := hB1
        rw [Finset.prod_eq_zero hc]
        simp only [hcf, ↓reduceIte]
        simpa using (hch c hc).mom _ Finset.inter_subset_right hne (hsmall c hc)
      by_cases hB2 : ∃ c ∈ firstL L h k a, J ∩ blk L h k c = ∅
      · obtain ⟨c, hc, he⟩ := hB2
        rw [Finset.prod_eq_zero (firstL_subset k a hc)]
        rw [he]; simp only [hc, ↓reduceIte]
        simpa using (hbias c (firstL_subset k a hc)).avg_eq_zero
          (hch c (firstL_subset k a hc)).even
      push Not at hB1 hB2
      refine Finset.prod_nonneg fun c hc => ?_
      by_cases hcf : c ∈ firstL L h k a
      · -- exactly one index in each first child
        have hone := card_inter_eq_one hg ha hJ hcard
          (fun c hc hcf => hB1 c hc hcf)
          (fun c hc => hB2 c hc) c hcf
        obtain ⟨j', hj'⟩ := Finset.card_eq_one.1 hone
        rw [hj']; simp only [hcf, ↓reduceIte]
        have := (hbias c hc).corr j' (by
          have : j' ∈ J ∩ blk L h k c := by rw [hj']; simp
          exact (Finset.mem_inter.1 this).2)
        simp only [chi, Finset.prod_singleton]
        rw [this]; positivity
      · have : J ∩ blk L h k c = ∅ := hB1 c hc hcf
        rw [this]; simp only [hcf, ↓reduceIte]
        simp only [chi_empty, mul_one]
        exact avg_nonneg fun ω => ((hch c hc).pos ω).le

/-- The value of the `L`-point correlation with one index in each of the first `L` children,
equation `eq:cross-correlation`. -/
theorem block_corr_val {k : ℕ} {a : ℤ} (ha : h (k + 1) a = true) {J : Finset ℤ}
    (hJ : J ⊆ (firstL L h k a).biUnion (blk L h k))
    (hone : ∀ c ∈ firstL L h k a, (J ∩ blk L h k c).card = 1) :
    avg (blk L h (k + 1) a) (fun ω => rho L h (k + 1) a ω * chi J ω) =
      -(1 / 2) * ∏ c ∈ firstL L h k a, 1 / Real.sqrt (3 * (blk L h k c).card) := by
  classical
  have hch : ∀ c ∈ ch L h k a, BlockProps L (blk L h k c) (rho L h k c) :=
    fun c hc => blockProps hg hL hLe k c (ch_mem hc)
  have hbias : ∀ c ∈ ch L h k a, IsBias (blk L h k c) (rho L h k c) (psi L h k c) :=
    fun c hc => psiOf_isBias c (hch c hc).law (hch c hc).even
      fun K hK hne hcard => (hch c hc).mom K hK hne (by omega)
  have hdep : ∀ c ∈ ch L h k a,
      Dep (rho L h k c) (blk L h k c) ∧ Dep (psi L h k c) (blk L h k c) :=
    fun c hc => ⟨(hch c hc).law.dep, (hbias c hc).dep⟩
  have hJB : J ⊆ blk L h (k + 1) a := fun j hj => by
    have := hJ hj
    rw [Finset.mem_biUnion] at this
    obtain ⟨c, hc, hjc⟩ := this
    exact blk_subset_of_ch hg (firstL_subset k a hc) hjc
  have hout : ∀ c ∈ ch L h k a, c ∉ firstL L h k a → J ∩ blk L h k c = ∅ := by
    intro c hc hcf
    ext j
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hj hjc
    have := hJ hj
    rw [Finset.mem_biUnion] at this
    obtain ⟨c', hc', hjc'⟩ := this
    have hne : c ≠ c' := fun h => hcf (h ▸ hc')
    exact Finset.disjoint_left.1 (ch_pairwiseDisjoint hg k a hc (firstL_subset k a hc') hne)
      hjc hjc'
  rw [avg_rho_succ_chi hg ha hdep hJB]
  obtain ⟨c1, hc1⟩ : (firstL L h k a).Nonempty := by
    rw [← Finset.card_pos, card_firstL hg ha]; omega
  have hT1 : ∏ c' ∈ ch L h k a, avg (blk L h k c')
      (fun ω => rho L h k c' ω * chi (J ∩ blk L h k c') ω) = 0 := by
    apply Finset.prod_eq_zero (firstL_subset k a hc1)
    have hn : (J ∩ blk L h k c1).Nonempty := by rw [← Finset.card_pos, hone c1 hc1]; omega
    exact (hch c1 (firstL_subset k a hc1)).mom _ Finset.inter_subset_right hn
      (by rw [hone c1 hc1]; omega)
  rw [hT1, zero_sub, neg_mul]
  congr 2
  rw [← Finset.prod_subset (firstL_subset k a) fun c hc hcf => by
    rw [hout c hc hcf]; simp only [hcf, ↓reduceIte]
    simpa using (hch c hc).law.avg_eq_one]
  refine Finset.prod_congr rfl fun c hc => ?_
  obtain ⟨j', hj'⟩ := Finset.card_eq_one.1 (hone c hc)
  rw [hj']; simp only [hc, ↓reduceIte]
  simp only [chi, Finset.prod_singleton]
  exact (hbias c (firstL_subset k a hc)).corr j' (by
    have : j' ∈ J ∩ blk L h k c := by rw [hj']; simp
    exact (Finset.mem_inter.1 this).2)

end Laws

end FiniteOrderMixing
