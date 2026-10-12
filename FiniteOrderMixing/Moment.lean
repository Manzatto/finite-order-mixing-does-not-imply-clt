import FiniteOrderMixing.Mixing

/-!
# Failure of the CLT and of higher-order exponential mixing (Section `sec:moment`)

Throughout, `L = 2m` is even and `L ≥ 6`.

* `key_h` / `key_nu` — **Proposition `prop:key-estimate`**: the sum of the `L`-point correlations
  over well separated tuples in `[0, n)` is `≤ -κ ((4L)^{k-1})^{L/2}`;
* `nu_moment` — **Corollary `cor:moment`**: `E (S_n/√n)^L ≤ (L-1)!! - δ`;
* `nu_noGaussian` — **Corollary `cor:no-gaussian`**;
* `nu_higherOrder`, `nu_not_expMixing` — **Corollary `cor:higher-order`**.
-/

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal Nat

namespace FiniteOrderMixing

variable {L : ℕ}

/-- Tuples in `[0, n)^L` whose successive gaps are at least `g`. -/
def Tgap (L n : ℕ) (g : ℤ) : Finset (Fin L → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) n).filter
    fun t => ∀ i j : Fin L, i < j → t i + g ≤ t j

lemma oddSet_of_nodup {l : List ℤ} (hl : l.Nodup) : oddSet l = l.toFinset := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [oddSet, ih hl.2, List.toFinset_cons]
    have : Disjoint ({a} : Finset ℤ) l.toFinset := by simpa using hl.1
    rw [this.symmDiff_eq_sup]; rfl

lemma oddSet_ofFn_of_injective {p : ℕ} {t : Fin p → ℤ} (ht : Function.Injective t) :
    oddSet (List.ofFn t) = Finset.univ.image t := by
  rw [oddSet_of_nodup (List.nodup_ofFn.2 ht)]
  ext x; simp [List.mem_ofFn]

lemma prod_Z_eq_chi_image {p : ℕ} {t : Fin p → ℤ} (ht : Function.Injective t) (ω : Config) :
    ∏ i, Z (t i) ω = chi (Finset.univ.image t) ω := by
  rw [chi, Finset.prod_image fun i _ j _ h => ht h]

lemma injective_of_gap {t : Fin L → ℤ} {g : ℤ} (hg : 1 ≤ g)
    (ht : ∀ i j : Fin L, i < j → t i + g ≤ t j) : Function.Injective t := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := ht i j h; omega
  · have := ht j i h; omega

lemma card_image_of_gap {t : Fin L → ℤ} {g : ℤ} (hg : 1 ≤ g)
    (ht : ∀ i j : Fin L, i < j → t i + g ≤ t j) : (Finset.univ.image t).card = L := by
  rw [Finset.card_image_of_injective _ (injective_of_gap hg ht)]; simp

/-! ## The key estimate for a fixed realisation -/

section KeyH

variable {h : Hspace} (hg : Good L h) (hL : 6 ≤ L) (hLe : Even L)
include hg hL hLe

/-- For a fixed realisation, every well separated `L`-point correlation is nonpositive. -/
lemma Eh_tuple_nonpos {W : Finset ℤ} {ℓ : ℕ} {t : Fin L → ℤ} {g : ℤ} (hg1 : 1 ≤ g)
    (ht : ∀ i j : Fin L, i < j → t i + g ≤ t j) (htW : ∀ i, t i ∈ W) :
    Eh L h ℓ W (fun ω => ∏ i, Z (t i) ω) ≤ 0 := by
  rw [Eh_congr' (prod_Z_eq_chi_image (injective_of_gap hg1 ht)),
    Eh_eq_of_superset hg hL hLe (fun x hx => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx; exact htW i) (dep_chi _)]
  exact Eh_chi_nonpos hg hL hLe ℓ (card_image_of_gap hg1 ht)

/-- **Proposition `prop:key-estimate`**, for a fixed realisation of the marker sets. -/
theorem key_h {m : ℕ} (hm : L = 2 * m) {j n ℓ : ℕ} (hjn : 6 * sc L (j + 2) ≤ n)
    (hℓ : j + 2 ≤ ℓ) :
    ∑ t ∈ Tgap L n (2 * L * sc L j), Eh L h ℓ (Finset.Ico 0 n) (fun ω => ∏ i, Z (t i) ω) ≤
      -(1 / (2 * 12 ^ m)) * (sc L (j + 1) : ℝ) ^ m := by
  classical
  have hL1 : 1 ≤ L := by omega
  set W := Finset.Ico (0 : ℤ) n
  set g : ℤ := 2 * L * sc L j
  have hsc0 : 1 ≤ sc L j := sc_pos hL1 j
  have hg1 : 1 ≤ g := by simp only [g]; nlinarith
  -- the selected level-`(j+2)` block
  set b := nxt L h (j + 2) (prv L h (j + 2) 0)
  have hb : h (j + 2) b = true := nxt_mem hg _ _
  have hb0 : 0 < b := lt_nxt_prv hg (j + 2) 0
  have hbn : nxt L h (j + 2) b ≤ n := by
    have h1 := nxt_le hg (j + 2) b
    have h2 := nxt_le hg (j + 2) (prv L h (j + 2) 0)
    have h3 := prv_le hg (j + 2) 0
    omega
  set F := firstL L h (j + 1) b
  have hF : F.card = L := card_firstL hg hb
  set e := F.orderEmbOfFin hF
  have heF : ∀ i, e i ∈ F := fun i => F.orderEmbOfFin_mem hF i
  have hech : ∀ i, e i ∈ ch L h (j + 1) b := fun i => firstL_subset _ _ (heF i)
  set q : ℕ := L * sc L j
  have hsc1 : sc L (j + 1) = 4 * q := by rw [sc_succ]; ring
  set C : ℤ → Finset ℤ := fun c => Finset.Ico (c + q) (nxt L h (j + 1) c - q)
  have hCB : ∀ c, C c ⊆ blk L h (j + 1) c := fun c x hx => by
    simp only [C, blk, Finset.mem_Ico] at hx ⊢; omega
  have hcardB : ∀ i, 4 * q < (blk L h (j + 1) (e i)).card := fun i => by
    rw [← hsc1]; exact card_blk_gt hg (Nat.succ_pos j) (ch_mem (hech i))
  have hcardC : ∀ i, ((C (e i)).card : ℝ) = (blk L h (j + 1) (e i)).card - 2 * q := by
    intro i
    have h1 := card_blk hg (j + 1) (e i)
    have h2 := hcardB i
    simp only [C, Int.card_Ico]
    have : 0 ≤ nxt L h (j + 1) (e i) - q - (e i + q) := by omega
    have hz : (((nxt L h (j + 1) (e i) - q - (e i + q)).toNat : ℕ) : ℝ) =
        ((nxt L h (j + 1) (e i) - q - (e i + q) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg this
    have h1' : ((blk L h (j + 1) (e i)).card : ℝ) = (nxt L h (j + 1) (e i) : ℝ) - (e i : ℝ) := by
      exact_mod_cast h1
    rw [hz, h1']
    push_cast; ring
  set Tφ := Fintype.piFinset fun i => C (e i)
  -- ordering of the chosen children
  have hord : ∀ i i', i < i' → nxt L h (j + 1) (e i) ≤ e i' := fun i i' hii' =>
    nxt_le_of_mem hg (e.strictMono hii') (ch_mem (hech i'))
  have hmemC : ∀ t ∈ Tφ, ∀ i, t i ∈ C (e i) := fun t ht i => Fintype.mem_piFinset.1 ht i
  have htgap : ∀ t ∈ Tφ, ∀ i i' : Fin L, i < i' → t i + g ≤ t i' := by
    intro t ht i i' hii'
    have h1 := hmemC t ht i
    have h2 := hmemC t ht i'
    have h3 := hord i i' hii'
    simp only [C, Finset.mem_Ico] at h1 h2
    simp only [g, q] at *
    push_cast at *
    linarith
  have hsub : Tφ ⊆ Tgap L n g := by
    intro t ht
    simp only [Tgap, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, htgap t ht⟩
    have h1 := hCB _ (hmemC t ht i)
    have h2 : t i ∈ blk L h (j + 2) b := blk_subset_of_ch hg (hech i) h1
    have hbdef : b = nxt L h (j + 2) (prv L h (j + 2) 0) := rfl
    simp only [blk, Finset.mem_Ico] at h2
    simp only [Finset.mem_Ico]
    omega
  -- the value of each correlation in `Tφ`
  set V : ℝ := -(1 / 2) * ∏ c ∈ F, 1 / Real.sqrt (3 * (blk L h (j + 1) c).card)
  have hval : ∀ t ∈ Tφ, Eh L h ℓ W (fun ω => ∏ i, Z (t i) ω) = V := by
    intro t ht
    have hinj := injective_of_gap hg1 (htgap t ht)
    set J := Finset.univ.image t
    have htB : ∀ i, t i ∈ blk L h (j + 1) (e i) := fun i => hCB _ (hmemC t ht i)
    have hJW : J ⊆ W := fun x hx => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact hsub ht |> fun h' => (Fintype.mem_piFinset.1 (Finset.mem_filter.1 h').1) i
    have hJb : J ⊆ blk L h (j + 2) b := fun x hx => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact blk_subset_of_ch hg (hech i) (htB i)
    have hstarts : (starts L h (j + 2) J).card ≤ L - 1 := by
      have : starts L h (j + 2) J ⊆ {b} := fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        rw [prv_eq_of_mem_blk hg hb (hJb hy)]; simp
      exact (Finset.card_le_card this).trans (by simp; omega)
    rw [Eh_congr' (prod_Z_eq_chi_image hinj), Eh_eq_of_superset hg hL hLe hJW (dep_chi J),
      Eh_stab hg hL hLe hℓ hstarts (dep_chi J), Eh_of_subset_blk hg hL hLe hb hJb (dep_chi J)]
    refine block_corr_val hg hL hLe hb (fun x hx => ?_) fun c hc => ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_biUnion.2 ⟨e i, heF i, htB i⟩
    · have hc' : c ∈ Set.range e := by rw [F.range_orderEmbOfFin hF]; exact hc
      obtain ⟨i0, rfl⟩ := hc'
      rw [Finset.card_eq_one]
      refine ⟨t i0, Finset.ext fun x => ?_⟩
      simp only [Finset.mem_inter, Finset.mem_singleton, J, Finset.mem_image, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨⟨i, rfl⟩, hx⟩
        by_contra hne
        have hii : i ≠ i0 := fun h => hne (h ▸ rfl)
        exact Finset.disjoint_left.1 (ch_pairwiseDisjoint hg (j + 1) b (hech i) (hech i0)
          (e.injective.ne hii)) (htB i) hx
      · rintro rfl; exact ⟨⟨i0, rfl⟩, htB i0⟩
  -- drop the other (nonpositive) terms
  have hdrop : ∑ t ∈ Tgap L n g, Eh L h ℓ W (fun ω => ∏ i, Z (t i) ω) ≤
      ∑ t ∈ Tφ, Eh L h ℓ W (fun ω => ∏ i, Z (t i) ω) := by
    refine Finset.sum_le_sum_of_subset_of_nonpos hsub fun t ht _ => ?_
    simp only [Tgap, Finset.mem_filter, Fintype.mem_piFinset] at ht
    exact Eh_tuple_nonpos hg hL hLe hg1 ht.2 ht.1
  refine hdrop.trans ?_
  rw [Finset.sum_congr rfl hval, Finset.sum_const, Fintype.card_piFinset, nsmul_eq_mul]
  -- lower bound for `card · |V|`
  have hFprod : ∏ c ∈ F, 1 / Real.sqrt (3 * (blk L h (j + 1) c).card) =
      ∏ i, 1 / Real.sqrt (3 * (blk L h (j + 1) (e i)).card) := by
    rw [← F.image_orderEmbOfFin_univ hF, Finset.prod_image fun i _ i' _ h => e.injective h]
  simp only [V, hFprod]
  push_cast
  have hfac : ∀ i, Real.sqrt (sc L (j + 1)) / (2 * Real.sqrt 3) ≤
      ((C (e i)).card : ℝ) * (1 / Real.sqrt (3 * (blk L h (j + 1) (e i)).card)) := by
    intro i
    set x : ℝ := ((blk L h (j + 1) (e i)).card : ℝ)
    have hx : (sc L (j + 1) : ℝ) ≤ x := by
      have := hcardB i; rw [← hsc1] at this; simp only [x]; exact_mod_cast this.le
    have hs0 : (0 : ℝ) < sc L (j + 1) := by exact_mod_cast sc_pos hL1 (j + 1)
    have hxpos : 0 < x := lt_of_lt_of_le hs0 hx
    have hC2 : x / 2 ≤ (C (e i)).card := by
      rw [hcardC i]
      have := hcardB i
      have : (4 * q : ℝ) < x := by simp only [x]; exact_mod_cast this
      linarith
    have h3 : Real.sqrt (3 * x) = Real.sqrt 3 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
    have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hxpos.le
    have hsq : Real.sqrt (sc L (j + 1)) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    have hs3 : 0 < Real.sqrt 3 := by positivity
    have hsxpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    rw [h3, div_le_iff₀ (by positivity)]
    calc Real.sqrt (sc L (j + 1)) ≤ Real.sqrt x := hsq
      _ = (x / 2) * (1 / (Real.sqrt 3 * Real.sqrt x)) * (2 * Real.sqrt 3) := by
          rw [show (x / 2) * (1 / (Real.sqrt 3 * Real.sqrt x)) * (2 * Real.sqrt 3) =
            x / Real.sqrt x by field_simp, Real.div_sqrt]
      _ ≤ (C (e i)).card * (1 / (Real.sqrt 3 * Real.sqrt x)) * (2 * Real.sqrt 3) := by gcongr
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => by positivity)
    fun i _ => hfac i
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hpow : (Real.sqrt (sc L (j + 1)) / (2 * Real.sqrt 3)) ^ L =
      (sc L (j + 1) : ℝ) ^ m / 12 ^ m := by
    rw [hm, pow_mul, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num),
      div_pow]
    norm_num
  rw [hpow] at hprod
  have : ((∏ i, ((C (e i)).card : ℝ)) * (-(1 / 2) *
      ∏ i, 1 / Real.sqrt (3 * (blk L h (j + 1) (e i)).card))) =
      -(1 / 2) * ∏ i, (((C (e i)).card : ℝ) *
        (1 / Real.sqrt (3 * (blk L h (j + 1) (e i)).card))) := by
    rw [Finset.prod_mul_distrib]; ring
  rw [this]
  calc -(1 / 2) * ∏ i, (((C (e i)).card : ℝ) * (1 / Real.sqrt (3 * (blk L h (j + 1) (e i)).card)))
      ≤ -(1 / 2) * ((sc L (j + 1) : ℝ) ^ m / 12 ^ m) := by linarith
    _ = -(1 / (2 * 12 ^ m)) * (sc L (j + 1) : ℝ) ^ m := by
        field_simp

end KeyH

lemma sc_mono (hL : 1 ≤ L) {k k' : ℕ} (h : k ≤ k') : sc L k ≤ sc L k' :=
  Nat.pow_le_pow_right (by omega) h

lemma exists_scale (hL : 1 ≤ L) {n : ℕ} (hn : 6 * sc L 2 ≤ n) :
    ∃ j, 6 * sc L (j + 2) ≤ n ∧ n < 6 * sc L (j + 3) := by
  classical
  have hex : ∃ j, n < 6 * sc L (j + 3) :=
    ⟨n, by have := lt_sc_self hL n; have := sc_mono hL (show n ≤ n + 3 by omega); omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; exact hn
  · obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
    have := Nat.find_min hex (show i < Nat.find hex by omega)
    rw [hi]; push Not at this; exact this

lemma S_eq_sum (n : ℕ) (ω : Config) : S n ω = ∑ j ∈ Finset.Ico (0 : ℤ) n, 1 * Z j ω := by
  simp only [S, one_mul]
  refine Finset.sum_nbij' (fun j : ℕ => (j : ℤ)) (fun j : ℤ => j.toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_range] at hj; simp [Finset.mem_Ico]; omega
  · intro j hj; simp only [Finset.mem_Ico] at hj; simp [Finset.mem_range]; omega
  · intro j _; simp
  · intro j hj; simp only [Finset.mem_Ico] at hj; simp; omega
  · intro j _; rfl

section Nu

variable {P : Measure Hspace} (hP : HierarchyLaw L P) (hL : 6 ≤ L) (hLe : Even L)
include hP hL hLe

lemma integral_chi_nonpos {K : Finset ℤ} (hK : K.card = L) :
    ∫ ω, chi K ω ∂(nu hP hL hLe) ≤ 0 := by
  rw [integral_nu hP hL hLe (dep_chi K)]
  refine integral_nonpos_of_ae ?_
  filter_upwards [hP.good] with h hg
  exact Eh_chi_nonpos hg hL hLe _ hK

/-- Moments of linear forms of order at most `L - 1` are those of independent signs. -/
lemma nu_linform_pow {p : ℕ} (hp : p ≤ L - 1) (B : Finset ℤ) (a : ℤ → ℝ) :
    ∫ ω, (∑ j ∈ B, a j * Z j ω) ^ p ∂(nu hP hL hLe) =
      avg B (fun ω => (∑ j ∈ B, a j * Z j ω) ^ p) := by
  simp only [linform_pow]
  rw [integral_finsetSum _ fun t _ => ((dep_chi _).integrable _).const_mul _, avg_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [integral_const_mul, avg_const_mul, integral_chi_eq_avg hP hL hLe
    (oddSet_ofFn_subset t fun i => Fintype.mem_piFinset.1 ht i)
    ((card_oddSet_ofFn t).trans hp)]

lemma integral_S_sq (n : ℕ) : ∫ ω, S n ω ^ 2 ∂(nu hP hL hLe) = n := by
  simp_rw [S_eq_sum]
  rw [nu_linform_pow hP hL hLe (by omega)]
  have := avg_mul_linform_sq (B := Finset.Ico (0 : ℤ) n) (ρ := fun _ => 1)
    (by simpa using avg_const (Finset.Ico (0 : ℤ) n) 1)
    (fun K hK hne _ => by simpa using avg_chi hK hne) (fun _ => 1)
  simp only [one_mul, one_pow, Finset.sum_const, Int.card_Ico, sub_zero, Int.toNat_natCast,
    nsmul_eq_mul, mul_one] at this
  simpa using this

lemma integral_S_four (n : ℕ) : ∫ ω, S n ω ^ 4 ∂(nu hP hL hLe) ≤ 3 * (n : ℝ) ^ 2 := by
  simp_rw [S_eq_sum]
  rw [nu_linform_pow hP hL hLe (by omega)]
  have := khintchine (Finset.Ico (0 : ℤ) n) (fun _ => 1) 2
  norm_num at this
  simpa using this

/-- **Proposition `prop:key-estimate`**, integrated over the marker sets. -/
theorem key_nu {m : ℕ} (hm : L = 2 * m) {j n : ℕ} (hjn : 6 * sc L (j + 2) ≤ n) :
    ∑ t ∈ Tgap L n (2 * L * sc L j), ∫ ω, ∏ i, Z (t i) ω ∂(nu hP hL hLe) ≤
      -(1 / (2 * 12 ^ m)) * (sc L (j + 1) : ℝ) ^ m := by
  have := hP.isProb
  set W := Finset.Ico (0 : ℤ) n
  set ℓ := kE W + (j + 2)
  have hdep : ∀ t ∈ Tgap L n (2 * L * sc L j), Dep (fun ω => ∏ i, Z (t i) ω) W := by
    intro t ht
    simp only [Tgap, Finset.mem_filter, Fintype.mem_piFinset] at ht
    exact dep_prod _ _ _ fun i _ => dep_Z_of_mem (ht.1 i)
  rw [Finset.sum_congr rfl fun t ht =>
    integral_nu' hP hL hLe (subset_refl W) (Nat.le_add_right (kE W) (j + 2)) (hdep t ht)]
  rw [← integral_finsetSum _ fun t ht => integrable_Eh hP hL hLe (hdep t ht) ℓ]
  calc ∫ h, ∑ t ∈ Tgap L n (2 * L * sc L j), Eh L h ℓ W (fun ω => ∏ i, Z (t i) ω) ∂P
      ≤ ∫ _h, -(1 / (2 * 12 ^ m)) * (sc L (j + 1) : ℝ) ^ m ∂P := by
        refine integral_mono_ae (integrable_finsetSum _ fun t ht =>
          integrable_Eh hP hL hLe (hdep t ht) ℓ) (integrable_const _) ?_
        filter_upwards [hP.good] with h hg
        exact key_h hg hL hLe hm hjn (Nat.le_add_left _ _)
    _ = _ := by simp

/-- The `L`-th moment is at most the Rademacher one plus the separated correlations. -/
lemma moment_le {m : ℕ} (hm : L = 2 * m) (n : ℕ) {g : ℤ} (hg1 : 1 ≤ g) :
    ∫ ω, S n ω ^ L ∂(nu hP hL hLe) ≤
      ((2 * m - 1)‼ : ℝ) * (n : ℝ) ^ m + ∑ t ∈ Tgap L n g, ∫ ω, ∏ i, Z (t i) ω ∂(nu hP hL hLe) := by
  set W := Finset.Ico (0 : ℤ) n
  have hS : ∀ ω, S n ω ^ L = ∑ t ∈ Fintype.piFinset (fun _ : Fin L => W),
      chi (oddSet (List.ofFn t)) ω := fun ω => by
    rw [S_eq_sum, linform_pow]; simp [W]
  have hA : avg W (fun ω => S n ω ^ L) ≤ ((2 * m - 1)‼ : ℝ) * (n : ℝ) ^ m := by
    have := khintchine W (fun _ => 1) m
    simp only [one_mul, one_pow, Finset.sum_const, Int.card_Ico, sub_zero, Int.toNat_natCast,
      nsmul_eq_mul, mul_one, W] at this
    rw [hm]
    refine le_of_eq_of_le (avg_congr fun ω => ?_) this
    rw [S_eq_sum]; simp
  set f : (Fin L → ℤ) → ℝ := fun t =>
    ∫ ω, chi (oddSet (List.ofFn t)) ω ∂(nu hP hL hLe) - avg W (chi (oddSet (List.ofFn t)))
  have hsum : ∫ ω, S n ω ^ L ∂(nu hP hL hLe) =
      avg W (fun ω => S n ω ^ L) + ∑ t ∈ Fintype.piFinset (fun _ : Fin L => W), f t := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hS),
      integral_finsetSum _ fun t _ => (dep_chi _).integrable _, avg_congr hS, avg_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by simp only [f]; ring
  have hf : ∀ t ∈ Fintype.piFinset (fun _ : Fin L => W), f t ≤ 0 := by
    intro t ht
    have hsub := oddSet_ofFn_subset t fun i => Fintype.mem_piFinset.1 ht i
    rcases Nat.lt_or_ge (oddSet (List.ofFn t)).card L with hlt | hge
    · simp only [f]
      rw [integral_chi_eq_avg hP hL hLe hsub (by omega), sub_self]
    · have hcard : (oddSet (List.ofFn t)).card = L := le_antisymm (card_oddSet_ofFn t) hge
      have hne : (oddSet (List.ofFn t)).Nonempty := by rw [← Finset.card_pos]; omega
      simp only [f]
      rw [avg_chi hsub hne, sub_zero]
      exact integral_chi_nonpos hP hL hLe hcard
  have hsub : Tgap L n g ⊆ Fintype.piFinset (fun _ : Fin L => W) := Finset.filter_subset _ _
  have hdrop := Finset.sum_le_sum_of_subset_of_nonpos hsub fun t ht _ => hf t ht
  have hT : ∀ t ∈ Tgap L n g, f t = ∫ ω, ∏ i, Z (t i) ω ∂(nu hP hL hLe) := by
    intro t ht
    simp only [Tgap, Finset.mem_filter] at ht
    have hinj := injective_of_gap hg1 ht.2
    have hne : (oddSet (List.ofFn t)).Nonempty := by
      rw [oddSet_ofFn_of_injective hinj]
      exact Finset.univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩ |>.image _
    simp only [f]
    rw [avg_chi (oddSet_ofFn_subset t fun i => Fintype.mem_piFinset.1 ht.1 i) hne, sub_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (prod_Z_eq_chi t ω).symm)
  rw [Finset.sum_congr rfl hT] at hdrop
  rw [hsum]; linarith

/-- **Corollary `cor:moment`**: a uniform deficit in the normalised `L`-th moment. -/
theorem nu_moment {m : ℕ} (hm : L = 2 * m) :
    ∃ δ > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∫ ω, (S n ω / Real.sqrt n) ^ (2 * m) ∂(nu hP hL hLe) ≤ ((2 * m - 1)‼ : ℝ) - δ := by
  have hL1 : 1 ≤ L := by omega
  refine ⟨(1 / (2 * 12 ^ m)) / (96 * (L : ℝ) ^ 2) ^ m, by positivity, 6 * sc L 2 + 1,
    fun n hn => ?_⟩
  obtain ⟨j, hj1, hj2⟩ := exists_scale hL1 (show 6 * sc L 2 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hg1 : (1 : ℤ) ≤ 2 * L * sc L j := by
    have := sc_pos hL1 j; nlinarith
  have hmom := moment_le hP hL hLe hm n hg1
  have hkey := key_nu hP hL hLe hm hj1
  -- `sc(j+1) > n / (96 L²)`
  have hsc : (n : ℝ) / (96 * (L : ℝ) ^ 2) ≤ sc L (j + 1) := by
    have : sc L (j + 3) = 16 * L ^ 2 * sc L (j + 1) := by simp only [sc]; ring
    rw [this] at hj2
    have : (n : ℝ) < 6 * (16 * (L : ℝ) ^ 2 * sc L (j + 1)) := by exact_mod_cast hj2
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hpow : ((n : ℝ) / (96 * (L : ℝ) ^ 2)) ^ m ≤ (sc L (j + 1) : ℝ) ^ m :=
    pow_le_pow_left₀ (by positivity) hsc m
  have hSL : ∀ ω, (S n ω / Real.sqrt n) ^ (2 * m) = S n ω ^ L / (n : ℝ) ^ m := fun ω => by
    rw [hm, div_pow, pow_mul (Real.sqrt n), Real.sq_sqrt hn0.le]
  rw [integral_congr_ae (Filter.Eventually.of_forall hSL), integral_div, div_le_iff₀ (by positivity)]
  have hnm : (0 : ℝ) < (n : ℝ) ^ m := by positivity
  have : ((n : ℝ) / (96 * (L : ℝ) ^ 2)) ^ m = (n : ℝ) ^ m / (96 * (L : ℝ) ^ 2) ^ m := div_pow _ _ _
  rw [this] at hpow
  have hκ : (0 : ℝ) < 1 / (2 * 12 ^ m) := by positivity
  calc ∫ ω, S n ω ^ L ∂(nu hP hL hLe)
      ≤ ((2 * m - 1)‼ : ℝ) * (n : ℝ) ^ m + -(1 / (2 * 12 ^ m)) * (sc L (j + 1) : ℝ) ^ m := by
        linarith
    _ ≤ ((2 * m - 1)‼ : ℝ) * (n : ℝ) ^ m +
          -(1 / (2 * 12 ^ m)) * ((n : ℝ) ^ m / (96 * (L : ℝ) ^ 2) ^ m) := by nlinarith
    _ = (((2 * m - 1)‼ : ℝ) - 1 / (2 * 12 ^ m) / (96 * (L : ℝ) ^ 2) ^ m) * (n : ℝ) ^ m := by
        ring

/-- **Corollary `cor:no-gaussian`**. -/
theorem nu_noGaussian {m : ℕ} (hm : L = 2 * m) : NoGaussianSubseqLimit (nu hP hL hLe) S := by
  intro nk hnk v hconv
  obtain ⟨δ, hδ, n₀, hn₀⟩ := nu_moment hP hL hLe hm
  set Y : ℕ → Config → ℝ := fun k ω => S (nk (k + n₀ + 1)) ω / Real.sqrt (nk (k + n₀ + 1))
  have hN : ∀ k, n₀ + 1 ≤ nk (k + n₀ + 1) := fun k => by
    have := hnk.id_le (k + n₀ + 1); simp at this; omega
  have hY : ∀ k, Measurable (Y k) := fun k => by
    simp only [Y]; exact (measurable_S _).div_const _
  -- Every power depends on finitely many signs, hence is bounded and integrable.
  have h_int : ∀ k q : ℕ, Integrable (fun ω => Y k ω ^ q) (nu hP hL hLe) := by
    intro k q
    refine Dep.integrable (E := Finset.Ico (0 : ℤ) (nk (k + n₀ + 1))) ?_ _
    intro ω ω' hω
    have hS : S (nk (k + n₀ + 1)) ω = S (nk (k + n₀ + 1)) ω' := by
      rw [S_eq_sum, S_eq_sum]
      exact Finset.sum_congr rfl fun j hj => by simp only [Z, hω j hj]
    simp only [Y, hS]
  have hconv' : ConvergesInDistribution (nu hP hL hLe) Y (gaussianReal 0 v) := fun u =>
    (hconv u).comp (tendsto_add_atTop_nat (n₀ + 1) |>.congr fun k => by ring_nf)
  have h2 : ∀ k, ∫ ω, Y k ω ^ 2 ∂(nu hP hL hLe) = 1 := by
    intro k
    have hpos : (0 : ℝ) < nk (k + n₀ + 1) := by exact_mod_cast (by have := hN k; omega)
    simp only [Y, div_pow, Real.sq_sqrt hpos.le]
    rw [integral_div, integral_S_sq hP hL hLe, div_self hpos.ne']
  have h4 : ∀ k, ∫ ω, Y k ω ^ 4 ∂(nu hP hL hLe) ≤ 3 := by
    intro k
    have hpos : (0 : ℝ) < nk (k + n₀ + 1) := by exact_mod_cast (by have := hN k; omega)
    have e : ∀ ω, Y k ω ^ 4 = S (nk (k + n₀ + 1)) ω ^ 4 / ((nk (k + n₀ + 1) : ℝ)) ^ 2 := fun ω => by
      simp only [Y, div_pow]
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul (Real.sqrt _), Real.sq_sqrt hpos.le]
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_div,
      div_le_iff₀ (by positivity)]
    exact integral_S_four hP hL hLe _
  have hL' : ∀ k, ∫ ω, Y k ω ^ (2 * m) ∂(nu hP hL hLe) ≤ ((2 * m - 1)‼ : ℝ) - δ := fun k =>
    hn₀ (nk (k + n₀ + 1)) (by have := hN k; omega)
  obtain ⟨-, hG⟩ := gaussian_limit_moments (nu hP hL hLe) Y hY v hconv' h2 h4
    (fun k => h_int k 4) m _ hL' (fun k => h_int k (2 * m))
  rw [gaussian_even_moment] at hG
  linarith

/-- **Corollary `cor:higher-order`**: a single separated `L`-point correlation of size
`≳ N^{-L/2}`. -/
theorem nu_higherOrder {m : ℕ} (hm : L = 2 * m) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ n : Fin L → ℕ, StrictMono n ∧ (∀ i, n i < N) ∧ Gapped n (N / C) ∧
        c * (N : ℝ) ^ (-(L : ℝ) / 2) ≤ -∫ ω, ∏ i, Z (n i) ω ∂(nu hP hL hLe) := by
  classical
  have hL1 : 1 ≤ L := by omega
  set κ : ℝ := 1 / (2 * 12 ^ m)
  have hκ : 0 < κ := by positivity
  refine ⟨κ / (96 * (L : ℝ) ^ 2) ^ m, 192 * (L : ℝ) ^ 2, by positivity, by positivity,
    6 * sc L 2 + 1, fun N hN => ?_⟩
  obtain ⟨j, hj1, hj2⟩ := exists_scale hL1 (show 6 * sc L 2 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set g : ℤ := 2 * L * sc L j
  have hsc0 := sc_pos hL1 j
  have hg1 : (1 : ℤ) ≤ g := by simp only [g]; nlinarith
  set T := Tgap L N g
  set A : ℝ := κ * (sc L (j + 1) : ℝ) ^ m
  have hA : 0 < A := by have := sc_pos hL1 (j + 1); positivity
  have hkey : ∑ t ∈ T, ∫ ω, ∏ i, Z (t i) ω ∂(nu hP hL hLe) ≤ -A := by
    have := key_nu hP hL hLe hm hj1; simp only [A, κ] at this ⊢; linarith
  have hTne : T.Nonempty := by
    by_contra hT; rw [Finset.not_nonempty_iff_eq_empty] at hT
    rw [hT, Finset.sum_empty] at hkey; linarith
  have hTcard : (T.card : ℝ) ≤ (N : ℝ) ^ L := by
    have : T.card ≤ N ^ L := by
      refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
      simp [Fintype.card_piFinset]
    exact_mod_cast this
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  obtain ⟨t, htT, ht⟩ : ∃ t ∈ T, ∫ ω, ∏ i, Z (t i) ω ∂(nu hP hL hLe) ≤ -A / T.card := by
    by_contra hcon
    push Not at hcon
    have := Finset.sum_lt_sum_of_nonempty hTne hcon
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hTpos.ne'] at this
    linarith
  simp only [T, Tgap, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Ico] at htT
  obtain ⟨hrange, hgap⟩ := htT
  refine ⟨fun i => (t i).toNat, fun i i' hii' => ?_, fun i => ?_, fun i i' hii' => ?_, ?_⟩
  · have := hgap i i' hii'; have := hrange i; have := hrange i'
    show (t i).toNat < (t i').toNat; omega
  · have := hrange i; show (t i).toNat < N; omega
  · have h1 := hgap i i' hii'
    have hc1 : ((t i).toNat : ℝ) = (t i : ℝ) := by
      have := hrange i; exact_mod_cast Int.toNat_of_nonneg this.1
    have hc2 : ((t i').toNat : ℝ) = (t i' : ℝ) := by
      have := hrange i'; exact_mod_cast Int.toNat_of_nonneg this.1
    show ((t i).toNat : ℝ) + N / (192 * (L : ℝ) ^ 2) ≤ ((t i').toNat : ℝ)
    rw [hc1, hc2]
    have h1' : (t i : ℝ) + g ≤ t i' := by exact_mod_cast h1
    have hgN : (N : ℝ) / (192 * (L : ℝ) ^ 2) ≤ g := by
      have e : sc L (j + 3) = 64 * L ^ 3 * sc L j := by simp only [sc]; ring
      rw [e] at hj2
      have : (N : ℝ) < 6 * (64 * (L : ℝ) ^ 3 * sc L j) := by exact_mod_cast hj2
      have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
      rw [div_le_iff₀ (by positivity)]
      simp only [g]; push_cast; nlinarith
    linarith
  · have hZ : ∀ ω, ∏ i, Z (((t i).toNat : ℕ) : ℤ) ω = ∏ i, Z (t i) ω := fun ω =>
      Finset.prod_congr rfl fun i _ => by rw [Int.toNat_of_nonneg (hrange i).1]
    simp only [hZ]
    have hrpow : (N : ℝ) ^ (-(L : ℝ) / 2) = ((N : ℝ) ^ m)⁻¹ := by
      rw [show -(L : ℝ) / 2 = -(m : ℝ) by rw [hm]; push_cast; ring, Real.rpow_neg hN0.le,
        Real.rpow_natCast]
    rw [hrpow]
    have hsc : (N : ℝ) / (96 * (L : ℝ) ^ 2) ≤ sc L (j + 1) := by
      have e : sc L (j + 3) = 16 * L ^ 2 * sc L (j + 1) := by simp only [sc]; ring
      rw [e] at hj2
      have : (N : ℝ) < 6 * (16 * (L : ℝ) ^ 2 * sc L (j + 1)) := by exact_mod_cast hj2
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hpow : (N : ℝ) ^ m / (96 * (L : ℝ) ^ 2) ^ m ≤ (sc L (j + 1) : ℝ) ^ m := by
      rw [← div_pow]; exact pow_le_pow_left₀ (by positivity) hsc m
    have hNL : (N : ℝ) ^ L = (N : ℝ) ^ m * (N : ℝ) ^ m := by rw [hm, two_mul, pow_add]
    have hNm : (0 : ℝ) < (N : ℝ) ^ m := by positivity
    have h1 : A / (N : ℝ) ^ L ≤ A / T.card :=
      div_le_div_of_nonneg_left hA.le hTpos hTcard
    have h2 : κ / (96 * (L : ℝ) ^ 2) ^ m * ((N : ℝ) ^ m)⁻¹ ≤ A / (N : ℝ) ^ L := by
      rw [hNL]
      have hD : (0 : ℝ) < (96 * (L : ℝ) ^ 2) ^ m := by positivity
      have : κ / (96 * (L : ℝ) ^ 2) ^ m * ((N : ℝ) ^ m)⁻¹ =
          (κ * ((N : ℝ) ^ m / (96 * (L : ℝ) ^ 2) ^ m)) / ((N : ℝ) ^ m * (N : ℝ) ^ m) := by
        field_simp
      rw [this]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hκ.le) (by positivity)
    have : -A / T.card = -(A / T.card) := neg_div _ _
    linarith

omit hP hL hLe in
lemma holderBound_Z0 {θ : ℝ} (hθ0 : 0 ≤ θ) : HolderBound θ (Z 0) 2 := by
  classical
  refine ⟨fun ω => by rw [Z, abs_spin]; norm_num, fun ω ω' => ?_⟩
  have hd0 : 0 ≤ dθ θ ω ω' := by
    unfold dθ; split_ifs <;> [exact pow_nonneg hθ0 _; exact le_rfl]
  by_cases h : ω 0 = ω' 0
  · simp only [Z, h, sub_self, abs_zero]; positivity
  · have hex : ∃ n : ℕ, ∃ j : ℤ, j.natAbs = n ∧ ω j ≠ ω' j := ⟨0, 0, rfl, h⟩
    have : dθ θ ω ω' = 1 := by
      unfold dθ
      rw [dite_eq_left hex, (Nat.find_eq_zero hex).2 ⟨0, rfl, h⟩, pow_zero]
    rw [this, mul_one]
    calc |Z 0 ω - Z 0 ω'| ≤ |Z 0 ω| + |Z 0 ω'| := abs_sub _ _
      _ = 2 := by simp [Z, abs_spin]; norm_num

/-- **Corollary `cor:higher-order`**: `(Σ, σ, ν)` is not exponentially mixing of order `L`. -/
theorem nu_not_expMixing {m : ℕ} (hm : L = 2 * m) (θ : ℝ) (hθ0 : 0 < θ) (_hθ1 : θ < 1) :
    ¬ ExpMixingOrder (nu hP hL hLe) shift (HolderBound θ) L := by
  rintro ⟨C0, c0, hc0, hmix⟩
  obtain ⟨c, C, hc, hC, N₀, hN⟩ := nu_higherOrder hP hL hLe hm
  have hZ0 : ∫ ω, Z 0 ω ∂(nu hP hL hLe) = 0 := by
    have := integral_chi_small hP hL hLe (K := {0}) (by simp) (by simp; omega)
    simpa [chi] using this
  set a := c0 / C
  have ha : 0 < a := div_pos hc0 hC
  -- the bound `c ≤ C0 2^L N^m e^{-aN}` for all large `N`
  have hbound : ∀ N ≥ max N₀ 1, c ≤ C0 * 2 ^ L * ((N : ℝ) ^ m * Real.exp (-(a * N))) := by
    intro N hN'
    obtain ⟨n, hn, -, hgap, hcorr⟩ := hN N (le_of_max_le_left hN')
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := le_of_max_le_right hN'; omega)
    have h := hmix (fun _ => Z 0) (fun _ => 2) (fun _ => holderBound_Z0 hθ0.le) n hn _ hgap
    beta_reduce at h
    rw [Finset.prod_eq_zero (i := ⟨0, by omega⟩) (Finset.mem_univ _) hZ0] at h
    simp only [sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    have hprod : ∀ x, ∏ i, Z 0 (shift^[n i] x) = ∏ i, Z (n i) x := fun x =>
      Finset.prod_congr rfl fun i _ => by rw [Z_shift_iterate, zero_add]
    simp only [hprod] at h
    have hrpow : (N : ℝ) ^ (-(L : ℝ) / 2) = ((N : ℝ) ^ m)⁻¹ := by
      rw [show -(L : ℝ) / 2 = -(m : ℝ) by rw [hm]; push_cast; ring, Real.rpow_neg hN0.le,
        Real.rpow_natCast]
    rw [hrpow] at hcorr
    have h1 : c * ((N : ℝ) ^ m)⁻¹ ≤ C0 * Real.exp (-c0 * (N / C)) * 2 ^ L :=
      hcorr.trans ((neg_le_abs _).trans h)
    have hNm : (0 : ℝ) < (N : ℝ) ^ m := by positivity
    have e : -c0 * (N / C) = -(a * N) := by simp only [a]; ring
    rw [e] at h1
    have := mul_le_mul_of_nonneg_right h1 hNm.le
    rw [mul_assoc, inv_mul_cancel₀ hNm.ne', mul_one] at this
    linarith
  -- the right-hand side tends to zero
  have htend : Tendsto (fun N : ℕ => C0 * 2 ^ L * ((N : ℝ) ^ m * Real.exp (-(a * N)))) atTop
      (nhds 0) := by
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop ha)
    have h3 := (h1.const_mul ((1 / a) ^ m)).const_mul (C0 * 2 ^ L)
    simp only [mul_zero] at h3
    refine h3.congr fun N => ?_
    simp only [Function.comp]
    rw [← mul_assoc ((1 / a) ^ m), ← mul_pow, one_div, ← mul_assoc, inv_mul_cancel_left₀ ha.ne',
      mul_assoc]
  have := ge_of_tendsto htend (Filter.eventually_atTop.2 ⟨max N₀ 1, hbound⟩)
  linarith

end Nu

end FiniteOrderMixing
