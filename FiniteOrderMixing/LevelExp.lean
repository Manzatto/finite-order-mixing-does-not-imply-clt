import FiniteOrderMixing.BlockLaws

/-!
# Finite-level laws and stabilisation (Section `sec:limit`, first part)

For a fixed realisation `h`, the finite-level law `ν_h^{(ℓ)} = ⊗_{B ∈ 𝓟_ℓ(h)} ρ_B` restricted to
the coordinates of a finite window `W` is described by

`Eh L h ℓ W F = avg_U ((∏_{a ∈ starts} rho L h ℓ a) · F)`,

where `starts` are the starts of the level-`ℓ` blocks meeting `W` and `U` is their union.

Main results:
* `Eh_eq_of_superset` — the value does not depend on the window (marginalisation);
* `Eh_succ` / `Eh_stab` — **Lemma `lem:stabilisation`**: if `W` meets at most `L - 1` level-`k`
  blocks, then `Eh ℓ W F = Eh k W F` for all `ℓ ≥ k`;
* `Eh_chi_small` — `(L-1)`-tuplewise independence with symmetric marginals;
* `Eh_chi_nonpos` — nonpositivity of the `L`-point correlations
  (Lemma `lem:correlation-classification`);
* `Eh_union_mul` — independence of windows meeting disjoint sets of blocks.
-/

open Finset

namespace FiniteOrderMixing

variable (L : ℕ)

/-- The union of the level-`ℓ` blocks meeting `W`. -/
noncomputable def cover (h : Hspace) (ℓ : ℕ) (W : Finset ℤ) : Finset ℤ :=
  (starts L h ℓ W).biUnion (blk L h ℓ)

/-- Expectation under the finite-level law `ν_h^{(ℓ)}` of a function of the coordinates in `W`. -/
noncomputable def Eh (h : Hspace) (ℓ : ℕ) (W : Finset ℤ) (F : Config → ℝ) : ℝ :=
  avg (cover L h ℓ W) (fun ω => (∏ a ∈ starts L h ℓ W, rho L h ℓ a ω) * F ω)

variable {L}

section Level

variable {h : Hspace} (hg : Good L h) (hL : 6 ≤ L) (hLe : Even L)
include hg hL hLe

omit hL hLe in
lemma subset_cover (ℓ : ℕ) (W : Finset ℤ) : W ⊆ cover L h ℓ W := subset_biUnion_starts hg ℓ W

/-- Marginalisation: any family `C` of level-`ℓ` block starts containing those of `W`
computes the same expectation. -/
lemma avg_blocks_eq_Eh {ℓ : ℕ} {W C : Finset ℤ} (hC : ∀ a ∈ C, h ℓ a = true)
    (hWC : starts L h ℓ W ⊆ C) {F : Config → ℝ} (hF : Dep F W) :
    avg (C.biUnion (blk L h ℓ)) (fun ω => (∏ a ∈ C, rho L h ℓ a ω) * F ω) = Eh L h ℓ W F := by
  classical
  set S := starts L h ℓ W
  have hU : C.biUnion (blk L h ℓ) = S.biUnion (blk L h ℓ) ∪ (C \ S).biUnion (blk L h ℓ) := by
    rw [← Finset.union_biUnion, Finset.union_sdiff_of_subset hWC]
  have hdisj : Disjoint (S.biUnion (blk L h ℓ)) ((C \ S).biUnion (blk L h ℓ)) := by
    rw [Finset.disjoint_biUnion_left]; intro a ha
    rw [Finset.disjoint_biUnion_right]; intro b hb
    exact blk_disjoint hg (hC a (hWC ha)) (hC b (Finset.mem_sdiff.1 hb).1)
      (fun h => (Finset.mem_sdiff.1 hb).2 (h ▸ ha))
  have hpt : ∀ ω, (∏ a ∈ C, rho L h ℓ a ω) * F ω =
      ((∏ a ∈ S, rho L h ℓ a ω) * F ω) * ∏ a ∈ C \ S, rho L h ℓ a ω := fun ω => by
    rw [← Finset.prod_sdiff hWC]; ring
  have hprops : ∀ a ∈ C, BlockProps L (blk L h ℓ a) (rho L h ℓ a) :=
    fun a ha => blockProps hg hL hLe ℓ a (hC a ha)
  rw [avg_congr hpt, hU]
  rw [show (fun ω => ((∏ a ∈ S, rho L h ℓ a ω) * F ω) * ∏ a ∈ C \ S, rho L h ℓ a ω) =
    (fun ω => (∏ a ∈ S, rho L h ℓ a ω) * F ω) * (fun ω => ∏ a ∈ C \ S, rho L h ℓ a ω) from rfl]
  rw [avg_union_mul hdisj, avg_biUnion_prod _ _ (blk_pairwiseDisjoint hg ℓ _ fun a ha =>
      hC a (Finset.mem_sdiff.1 ha).1) _ fun a ha =>
      (hprops a (Finset.mem_sdiff.1 ha).1).law.dep,
    Finset.prod_eq_one fun a ha => (hprops a (Finset.mem_sdiff.1 ha).1).law.avg_eq_one, mul_one]
  · rfl
  · refine (dep_prod S _ _ fun a ha => ?_).mul ?_
    · exact (hprops a (hWC ha)).law.dep.mono (Finset.subset_biUnion_of_mem _ ha)
    · exact hF.mono (subset_biUnion_starts hg ℓ W)
  · exact dep_prod _ _ _ fun a ha =>
      (hprops a (Finset.mem_sdiff.1 ha).1).law.dep.mono (Finset.subset_biUnion_of_mem _ ha)

omit hg hL hLe in
lemma starts_subset {ℓ : ℕ} {W W' : Finset ℤ} (hW : W ⊆ W') :
    starts L h ℓ W ⊆ starts L h ℓ W' := Finset.image_subset_image hW

/-- The expectation does not depend on the window. -/
lemma Eh_eq_of_superset {ℓ : ℕ} {W W' : Finset ℤ} (hWW' : W ⊆ W') {F : Config → ℝ}
    (hF : Dep F W) : Eh L h ℓ W' F = Eh L h ℓ W F :=
  avg_blocks_eq_Eh hg hL hLe (fun _ ha => starts_mem hg ha) (starts_subset hWW') hF

omit hg hL hLe in
lemma Eh_congr' {ℓ : ℕ} {W : Finset ℤ} {F G : Config → ℝ} (hFG : ∀ ω, F ω = G ω) :
    Eh L h ℓ W F = Eh L h ℓ W G := avg_congr fun ω => by rw [hFG]

omit hg hL hLe in
lemma Eh_add (ℓ : ℕ) (W : Finset ℤ) (F G : Config → ℝ) :
    Eh L h ℓ W (F + G) = Eh L h ℓ W F + Eh L h ℓ W G := by
  simp only [Eh]; rw [← avg_add]; exact avg_congr fun ω => by simp; ring

omit hg hL hLe in
lemma Eh_const_mul (ℓ : ℕ) (W : Finset ℤ) (c : ℝ) (F : Config → ℝ) :
    Eh L h ℓ W (fun ω => c * F ω) = c * Eh L h ℓ W F := by
  simp only [Eh]; rw [← avg_const_mul]; exact avg_congr fun ω => by ring

omit hg hL hLe in
lemma Eh_sum {ι : Type*} (ℓ : ℕ) (W : Finset ℤ) (S : Finset ι) (F : ι → Config → ℝ) :
    Eh L h ℓ W (fun ω => ∑ i ∈ S, F i ω) = ∑ i ∈ S, Eh L h ℓ W (F i) := by
  simp only [Eh]; rw [← avg_sum]; exact avg_congr fun ω => by rw [Finset.mul_sum]

lemma Eh_mono {ℓ : ℕ} {W : Finset ℤ} {F G : Config → ℝ} (hFG : ∀ ω, F ω ≤ G ω) :
    Eh L h ℓ W F ≤ Eh L h ℓ W G := by
  simp only [Eh]
  refine avg_mono fun ω => mul_le_mul_of_nonneg_left (hFG ω) ?_
  exact Finset.prod_nonneg fun a ha =>
    ((blockProps hg hL hLe ℓ a (starts_mem hg ha)).pos ω).le

lemma Eh_nonneg {ℓ : ℕ} {W : Finset ℤ} {F : Config → ℝ} (hF : ∀ ω, 0 ≤ F ω) :
    0 ≤ Eh L h ℓ W F := by
  have := Eh_mono hg hL hLe (ℓ := ℓ) (W := W) (F := fun _ => 0) hF
  simp only [Eh, mul_zero] at this
  rwa [avg_const] at this

lemma Eh_one (ℓ : ℕ) (W : Finset ℤ) : Eh L h ℓ W (fun _ => 1) = 1 := by
  have := Eh_eq_of_superset hg hL hLe (ℓ := ℓ) (Finset.empty_subset W) (dep_const 1 ∅)
  rw [this]; simp [Eh, starts, cover, avg_const]

/-- Positivity of cylinder probabilities (full support). -/
lemma Eh_pos {ℓ : ℕ} {W : Finset ℤ} {F : Config → ℝ} (hF : ∀ ω, 0 ≤ F ω) (hFW : Dep F W)
    (hpos : ∃ ω, 0 < F ω) : 0 < Eh L h ℓ W F := by
  obtain ⟨ω0, hω0⟩ := hpos
  simp only [Eh, avg, avgAt]
  apply div_pos _ (by positivity)
  set U := cover L h ℓ W
  set T := U.filter fun j => ω0 j = true
  apply Finset.sum_pos' (fun T _ => mul_nonneg (Finset.prod_nonneg fun a ha =>
    ((blockProps hg hL hLe ℓ a (starts_mem hg ha)).pos _).le) (hF _))
  refine ⟨T, Finset.mem_powerset.2 (Finset.filter_subset _ _), mul_pos
    (Finset.prod_pos fun a ha => (blockProps hg hL hLe ℓ a (starts_mem hg ha)).pos _) ?_⟩
  rw [hFW _ ω0 fun j hj => ?_]
  · exact hω0
  · have hjU : j ∈ U := subset_cover hg ℓ W hj
    by_cases h0 : ω0 j = true <;> simp [patch, hjU, T, h0]

/-- The expectation over a window contained in one block. -/
lemma Eh_of_subset_blk {ℓ : ℕ} {a : ℤ} (ha : h ℓ a = true) {W : Finset ℤ} (hW : W ⊆ blk L h ℓ a)
    {F : Config → ℝ} (hF : Dep F W) :
    Eh L h ℓ W F = avg (blk L h ℓ a) (fun ω => rho L h ℓ a ω * F ω) := by
  have := avg_blocks_eq_Eh hg hL hLe (C := {a}) (fun b hb => by simp at hb; subst hb; exact ha)
    (fun b hb => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
      simp [prv_eq_of_mem_blk hg ha (hW hi)]) hF
  rw [← this]; simp

/-! ## The removal step and stabilisation -/

omit hL hLe in
/-- Integrating out a first child that `G` does not see removes the interaction term of the
parent law. -/
lemma avg_rho_succ_removal {ℓ : ℕ} {a : ℤ} (_ha : h (ℓ + 1) a = true)
    (hprops : ∀ c ∈ ch L h ℓ a, BlockProps L (blk L h ℓ c) (rho L h ℓ c))
    (hbias : ∀ c ∈ ch L h ℓ a, IsBias (blk L h ℓ c) (rho L h ℓ c) (psi L h ℓ c))
    {c0 : ℤ} (hc0 : c0 ∈ firstL L h ℓ a) {U : Finset ℤ} (hU : blk L h (ℓ + 1) a ⊆ U)
    {G : Config → ℝ} (hG : Dep G (U \ blk L h ℓ c0)) :
    avg U (fun ω => rho L h (ℓ + 1) a ω * G ω) =
      avg U (fun ω => (∏ c ∈ ch L h ℓ a, rho L h ℓ c ω) * G ω) := by
  classical
  have hc0ch := firstL_subset ℓ a hc0
  set R : Config → ℝ := fun ω => (∏ c ∈ (firstL L h ℓ a).erase c0, psi L h ℓ c ω) *
    (∏ c ∈ (ch L h ℓ a).erase c0, rho L h ℓ c ω) * G ω
  have hpt : ∀ ω, rho L h (ℓ + 1) a ω * G ω =
      (∏ c ∈ ch L h ℓ a, rho L h ℓ c ω) * G ω -
        1 / 2 * ((rho L h ℓ c0 ω * psi L h ℓ c0 ω) * R ω) := fun ω => by
    rw [rho_succ, ← Finset.mul_prod_erase _ _ hc0, ← Finset.mul_prod_erase _ _ hc0ch]
    simp only [R]; ring
  rw [avg_congr hpt]
  rw [show (fun ω => (∏ c ∈ ch L h ℓ a, rho L h ℓ c ω) * G ω -
      1 / 2 * ((rho L h ℓ c0 ω * psi L h ℓ c0 ω) * R ω)) =
      (fun ω => (∏ c ∈ ch L h ℓ a, rho L h ℓ c ω) * G ω) -
      (fun ω => 1 / 2 * ((rho L h ℓ c0 ω * psi L h ℓ c0 ω) * R ω)) from rfl, avg_sub,
    avg_const_mul]
  have hsplit : U = blk L h ℓ c0 ∪ (U \ blk L h ℓ c0) :=
    (Finset.union_sdiff_of_subset ((blk_subset_of_ch hg hc0ch).trans hU)).symm
  have hsub : ∀ c ∈ ch L h ℓ a, c ≠ c0 → blk L h ℓ c ⊆ U \ blk L h ℓ c0 := fun c hc hne j hj =>
    Finset.mem_sdiff.2 ⟨hU (blk_subset_of_ch hg hc hj),
      Finset.disjoint_left.1 (ch_pairwiseDisjoint hg ℓ a hc hc0ch hne) hj⟩
  have hR : Dep R (U \ blk L h ℓ c0) := by
    refine ((dep_prod _ _ _ fun c hc => ?_).mul (dep_prod _ _ _ fun c hc => ?_)).mul hG
    · have hc' := Finset.mem_of_mem_erase hc
      exact (hbias c (firstL_subset ℓ a hc')).dep.mono
        (hsub c (firstL_subset ℓ a hc') (Finset.ne_of_mem_erase hc))
    · exact (hprops c (Finset.mem_of_mem_erase hc)).law.dep.mono
        (hsub c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc))
  have hzero : avg U (fun ω => (rho L h ℓ c0 ω * psi L h ℓ c0 ω) * R ω) = 0 := by
    rw [hsplit]
    rw [show (fun ω => (rho L h ℓ c0 ω * psi L h ℓ c0 ω) * R ω) =
      (fun ω => rho L h ℓ c0 ω * psi L h ℓ c0 ω) * R from rfl,
      avg_union_mul (F := fun ω => rho L h ℓ c0 ω * psi L h ℓ c0 ω) (G := R) Finset.disjoint_sdiff
        ((hprops c0 hc0ch).law.dep.mul (hbias c0 hc0ch).dep) hR,
      (hbias c0 hc0ch).avg_eq_zero (hprops c0 hc0ch).even, zero_mul]
  rw [hzero]; ring

/-- One step of **Lemma `lem:stabilisation`**. -/
lemma Eh_succ {ℓ : ℕ} {W : Finset ℤ} (hW : (starts L h ℓ W).card ≤ L - 1) {F : Config → ℝ}
    (hF : Dep F W) : Eh L h (ℓ + 1) W F = Eh L h ℓ W F := by
  classical
  set S := starts L h (ℓ + 1) W
  set U := cover L h (ℓ + 1) W
  have hSm : ∀ a ∈ S, h (ℓ + 1) a = true := fun a ha => starts_mem hg ha
  have hprops : ∀ a ∈ S, ∀ c ∈ ch L h ℓ a, BlockProps L (blk L h ℓ c) (rho L h ℓ c) :=
    fun a _ c hc => blockProps hg hL hLe ℓ c (ch_mem hc)
  have hbias : ∀ a ∈ S, ∀ c ∈ ch L h ℓ a, IsBias (blk L h ℓ c) (rho L h ℓ c) (psi L h ℓ c) :=
    fun a ha c hc => psiOf_isBias c (hprops a ha c hc).law (hprops a ha c hc).even
      fun K hK hne hcard => (hprops a ha c hc).mom K hK hne (by omega)
  have hprops' : ∀ a ∈ S, BlockProps L (blk L h (ℓ + 1) a) (rho L h (ℓ + 1) a) :=
    fun a ha => blockProps hg hL hLe (ℓ + 1) a (hSm a ha)
  set P : ℤ → Config → ℝ := fun a ω => ∏ c ∈ ch L h ℓ a, rho L h ℓ c ω
  have hPdep : ∀ a ∈ S, Dep (P a) (blk L h (ℓ + 1) a) := fun a ha =>
    dep_prod _ _ _ fun c hc => (hprops a ha c hc).law.dep.mono (blk_subset_of_ch hg hc)
  have hblkU : ∀ a ∈ S, blk L h (ℓ + 1) a ⊆ U := fun a ha => Finset.subset_biUnion_of_mem _ ha
  have hWU : W ⊆ U := subset_cover hg (ℓ + 1) W
  -- replace the parent laws by the products of the child laws, one block at a time
  have key : ∀ T ⊆ S, avg U (fun ω => (∏ a ∈ T, rho L h (ℓ + 1) a ω) *
      (∏ a ∈ S \ T, P a ω) * F ω) = avg U (fun ω => (∏ a ∈ S, P a ω) * F ω) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact avg_congr fun ω => by simp
    | insert b T hb ih =>
      intro hTS
      have hbS : b ∈ S := hTS (Finset.mem_insert_self b T)
      have hTS' : T ⊆ S := (Finset.subset_insert b T).trans hTS
      obtain ⟨c0, hc0, hc0W⟩ := exists_firstL_disjoint hg (hSm b hbS)
        (show (starts L h ℓ W).card < L by omega)
      have hdisjS : ∀ a ∈ S, a ≠ b → Disjoint (blk L h (ℓ + 1) a) (blk L h (ℓ + 1) b) :=
        fun a ha hne => blk_disjoint hg (hSm a ha) (hSm b hbS) hne
      have hc0b : blk L h ℓ c0 ⊆ blk L h (ℓ + 1) b :=
        blk_subset_of_ch hg (firstL_subset ℓ b hc0)
      have hout : ∀ a ∈ S, a ≠ b → blk L h (ℓ + 1) a ⊆ U \ blk L h ℓ c0 := fun a ha hne j hj =>
        Finset.mem_sdiff.2 ⟨hblkU a ha hj, fun hj' =>
          Finset.disjoint_left.1 (hdisjS a ha hne) hj (hc0b hj')⟩
      set G : Config → ℝ := fun ω => (∏ a ∈ T, rho L h (ℓ + 1) a ω) *
        (∏ a ∈ S \ insert b T, P a ω) * F ω
      have hG : Dep G (U \ blk L h ℓ c0) := by
        refine ((dep_prod _ _ _ fun a ha => ?_).mul (dep_prod _ _ _ fun a ha => ?_)).mul ?_
        · exact (hprops' a (hTS' ha)).law.dep.mono
            (hout a (hTS' ha) fun h => hb (h ▸ ha))
        · have ha' := Finset.mem_sdiff.1 ha
          exact (hPdep a ha'.1).mono (hout a ha'.1 fun h => ha'.2 (h ▸ Finset.mem_insert_self _ _))
        · intro ω ω' hω
          exact hF _ _ fun j hj => hω j (Finset.mem_sdiff.2 ⟨hWU hj,
            fun hj' => Finset.disjoint_left.1 hc0W hj' hj⟩)
      have hrem := avg_rho_succ_removal hg (hSm b hbS) (hprops b hbS) (hbias b hbS) hc0
        (hblkU b hbS) hG
      rw [← ih hTS']
      have e1 : ∀ ω, (∏ a ∈ insert b T, rho L h (ℓ + 1) a ω) * (∏ a ∈ S \ insert b T, P a ω) *
          F ω = rho L h (ℓ + 1) b ω * G ω := fun ω => by
        rw [Finset.prod_insert hb]; simp only [G]; ring
      have e2 : ∀ ω, (∏ a ∈ T, rho L h (ℓ + 1) a ω) * (∏ a ∈ S \ T, P a ω) * F ω =
          P b ω * G ω := fun ω => by
        have : S \ T = insert b (S \ insert b T) := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hx, hxT⟩; by_cases hxb : x = b
            · exact Or.inl hxb
            · exact Or.inr ⟨hx, fun h => h.elim hxb hxT⟩
          · rintro (rfl | ⟨hx, hxT⟩)
            · exact ⟨hbS, hb⟩
            · exact ⟨hx, fun h => hxT (Or.inr h)⟩
        rw [this, Finset.prod_insert (by simp)]; simp only [G]; ring
      rw [avg_congr e1, avg_congr e2]
      exact hrem
  have hmain := key S le_rfl
  simp only [Finset.sdiff_self, Finset.prod_empty, mul_one] at hmain
  -- the children of the covering blocks form a family of level-`ℓ` block starts
  set C := S.biUnion (ch L h ℓ)
  have hCdisj : (S : Set ℤ).PairwiseDisjoint (ch L h ℓ) := fun a ha b hb hne =>
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        (blk_disjoint hg (hSm a ha) (hSm b hb) hne))
  have hUC : U = C.biUnion (blk L h ℓ) := by
    simp only [U, cover, C, Finset.biUnion_biUnion]
    exact Finset.biUnion_congr rfl fun a ha => blk_succ_eq hg (hSm a ha)
  have hPC : ∀ ω, (∏ a ∈ S, P a ω) = ∏ c ∈ C, rho L h ℓ c ω := fun ω => by
    rw [Finset.prod_biUnion hCdisj]
  have hC : ∀ c ∈ C, h ℓ c = true := fun c hc => by
    obtain ⟨a, _, hca⟩ := Finset.mem_biUnion.1 hc; exact ch_mem hca
  have hWC : starts L h ℓ W ⊆ C := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
    refine Finset.mem_biUnion.2 ⟨prv L h (ℓ + 1) i, Finset.mem_image_of_mem _ hi, ?_⟩
    simp only [ch, Finset.mem_filter]
    refine ⟨?_, prv_mem hg ℓ i⟩
    have := mem_blk_prv hg (ℓ + 1) i
    simp only [blk, Finset.mem_Ico] at this ⊢
    exact ⟨le_prv_of_mem hg this.1 (hg.nested ℓ _ (prv_mem hg (ℓ + 1) i)),
      lt_of_le_of_lt (prv_le hg ℓ i) this.2⟩
  have : Eh L h (ℓ + 1) W F = avg U (fun ω => (∏ a ∈ S, rho L h (ℓ + 1) a ω) * F ω) := rfl
  rw [this, hmain, avg_congr fun ω => by rw [hPC], hUC]
  exact avg_blocks_eq_Eh hg hL hLe hC hWC hF

/-- **Lemma `lem:stabilisation`.** -/
theorem Eh_stab {k ℓ : ℕ} (hkℓ : k ≤ ℓ) {W : Finset ℤ} (hW : (starts L h k W).card ≤ L - 1)
    {F : Config → ℝ} (hF : Dep F W) : Eh L h ℓ W F = Eh L h k W F := by
  induction ℓ, hkℓ using Nat.le_induction with
  | base => rfl
  | succ ℓ hkℓ ih =>
    rw [Eh_succ hg hL hLe ((card_starts_mono hg hkℓ W).trans hW) hF, ih]

/-! ## Consequences -/

omit hL hLe in
lemma starts_zero (W : Finset ℤ) : starts L h 0 W = W := by
  have : prv L h 0 = id := funext (prv_zero hg)
  simp [starts, this]

/-- `(L-1)`-tuplewise independence: characters of `1 ≤ |K| ≤ L-1` coordinates have mean zero. -/
theorem Eh_chi_small (ℓ : ℕ) {K : Finset ℤ} (hne : K.Nonempty) (hcard : K.card ≤ L - 1) :
    Eh L h ℓ K (chi K) = 0 := by
  rw [Eh_stab hg hL hLe (Nat.zero_le ℓ) (by rw [starts_zero hg]; exact hcard) (dep_chi K)]
  simp only [Eh, cover, starts_zero hg, rho_zero, Finset.prod_const_one, one_mul]
  have : K.biUnion (blk L h 0) = K := by
    ext j; simp [blk_zero hg]
  rw [this]
  exact avg_chi le_rfl hne

omit hL hLe in
/-- Characters factor over the blocks meeting the window. -/
lemma chi_eq_prod_starts (ℓ : ℕ) (J : Finset ℤ) (ω : Config) :
    chi J ω = ∏ a ∈ starts L h ℓ J, chi (J ∩ blk L h ℓ a) ω := by
  classical
  have hJ' : J = (starts L h ℓ J).biUnion fun a => J ∩ blk L h ℓ a := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hj; exact ⟨_, Finset.mem_image_of_mem _ hj, hj, mem_blk_prv hg ℓ j⟩
    · rintro ⟨_, _, hj, _⟩; exact hj
  have hdisj : ((starts L h ℓ J : Finset ℤ) : Set ℤ).PairwiseDisjoint
      fun a => J ∩ blk L h ℓ a := fun a ha b hb hne =>
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right
        (blk_pairwiseDisjoint hg ℓ _ (fun _ hc => starts_mem hg hc) ha hb hne))
  conv_lhs => rw [hJ']
  simp only [chi]
  rw [Finset.prod_biUnion hdisj]

/-- Factorisation of the expectation over the blocks meeting the window. -/
lemma Eh_prod_starts (ℓ : ℕ) (W : Finset ℤ) (F : ℤ → Config → ℝ)
    (hF : ∀ a ∈ starts L h ℓ W, Dep (F a) (blk L h ℓ a)) :
    Eh L h ℓ W (fun ω => ∏ a ∈ starts L h ℓ W, F a ω) =
      ∏ a ∈ starts L h ℓ W, avg (blk L h ℓ a) (fun ω => rho L h ℓ a ω * F a ω) := by
  classical
  simp only [Eh, cover]
  rw [avg_congr fun ω => (Finset.prod_mul_distrib (s := starts L h ℓ W)
    (f := fun a => rho L h ℓ a ω) (g := fun a => F a ω)).symm]
  exact avg_biUnion_prod _ _ (blk_pairwiseDisjoint hg ℓ _ fun _ hc => starts_mem hg hc)
    (fun a ω => rho L h ℓ a ω * F a ω)
    fun a ha => ((blockProps hg hL hLe ℓ a (starts_mem hg ha)).law.dep.mul (hF a ha))

/-- Nonpositivity of the `L`-point correlations of `ν_h^{(ℓ)}`. -/
theorem Eh_chi_nonpos (ℓ : ℕ) {J : Finset ℤ} (hcard : J.card = L) :
    Eh L h ℓ J (chi J) ≤ 0 := by
  classical
  rw [Eh_congr' (chi_eq_prod_starts hg ℓ J),
    Eh_prod_starts hg hL hLe ℓ J _ fun a _ => (dep_chi _).mono Finset.inter_subset_right]
  have hJne : J.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨j0, hj0⟩ := hJne
  by_cases hone : starts L h ℓ J = {prv L h ℓ j0}
  · rw [hone, Finset.prod_singleton]
    have hsub : J ⊆ blk L h ℓ (prv L h ℓ j0) := fun j hj => by
      have : prv L h ℓ j ∈ starts L h ℓ J := Finset.mem_image_of_mem _ hj
      rw [hone, Finset.mem_singleton] at this
      rw [← this]; exact mem_blk_prv hg ℓ j
    rw [Finset.inter_eq_left.2 hsub]
    exact block_corr_nonpos hg hL hLe ℓ _ (prv_mem hg ℓ j0) J hsub hcard
  · -- at least two blocks: the factor of the block of `j0` vanishes
    have hmem : prv L h ℓ j0 ∈ starts L h ℓ J := Finset.mem_image_of_mem _ hj0
    obtain ⟨b, hb, hbne⟩ : ∃ b ∈ starts L h ℓ J, b ≠ prv L h ℓ j0 := by
      by_contra hcon; push Not at hcon
      exact hone (Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, hcon⟩)
    refine le_of_eq (Finset.prod_eq_zero hmem ?_)
    refine (blockProps hg hL hLe ℓ _ (prv_mem hg ℓ j0)).mom _ Finset.inter_subset_right
      ⟨j0, Finset.mem_inter.2 ⟨hj0, mem_blk_prv hg ℓ j0⟩⟩ ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
    have hlt : (J ∩ blk L h ℓ (prv L h ℓ j0)).card < J.card := by
      apply Finset.card_lt_card
      refine ⟨Finset.inter_subset_left, fun hsub => ?_⟩
      have := (Finset.mem_inter.1 (hsub hi)).2
      exact hbne (prv_eq_of_mem_blk hg (prv_mem hg ℓ j0) this)
    omega

/-- Windows meeting disjoint families of blocks are independent under `ν_h^{(ℓ)}`. -/
lemma Eh_union_mul (ℓ : ℕ) {W₁ W₂ : Finset ℤ}
    (hdisj : Disjoint (starts L h ℓ W₁) (starts L h ℓ W₂)) {F₁ F₂ : Config → ℝ}
    (hF₁ : Dep F₁ W₁) (hF₂ : Dep F₂ W₂) :
    Eh L h ℓ (W₁ ∪ W₂) (fun ω => F₁ ω * F₂ ω) = Eh L h ℓ W₁ F₁ * Eh L h ℓ W₂ F₂ := by
  classical
  have hS : starts L h ℓ (W₁ ∪ W₂) = starts L h ℓ W₁ ∪ starts L h ℓ W₂ := Finset.image_union _ _
  have hU : cover L h ℓ (W₁ ∪ W₂) = cover L h ℓ W₁ ∪ cover L h ℓ W₂ := by
    simp only [cover, hS, Finset.union_biUnion]
  have hUd : Disjoint (cover L h ℓ W₁) (cover L h ℓ W₂) := by
    simp only [cover]
    rw [Finset.disjoint_biUnion_left]; intro a ha
    rw [Finset.disjoint_biUnion_right]; intro b hb
    exact blk_disjoint hg (starts_mem hg ha) (starts_mem hg hb)
      (fun h => Finset.disjoint_left.1 hdisj ha (h ▸ hb))
  have hdep : ∀ W F, Dep F W →
      Dep (fun ω => (∏ a ∈ starts L h ℓ W, rho L h ℓ a ω) * F ω) (cover L h ℓ W) :=
    fun W F hF => (dep_prod _ _ _ fun a ha =>
      (blockProps hg hL hLe ℓ a (starts_mem hg ha)).law.dep.mono
        (Finset.subset_biUnion_of_mem _ ha)).mul (hF.mono (subset_cover hg ℓ W))
  simp only [Eh]
  rw [hU, hS]
  rw [← avg_union_mul hUd (hdep W₁ F₁ hF₁) (hdep W₂ F₂ hF₂)]
  exact avg_congr fun ω => by rw [Finset.prod_union hdisj]; simp only [Pi.mul_apply]; ring

end Level

end FiniteOrderMixing
