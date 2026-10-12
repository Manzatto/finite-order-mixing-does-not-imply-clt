import FiniteOrderMixing.Properties

/-!
# Finite-window independence and exponential mixing (Section `sec:correlations`)

* `integral_prod_local` — `(H4)` for finitely many ordered windows;
* `nu_prod_windows` — **Proposition `prop:windows`**, as a product formula;
* `nu_windows` — the same, as joint independence of the window vectors;
* `nu_expMixing` — **Proposition `prop:holder`**: exponential mixing of every order `s ≤ R`.
-/

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

namespace FiniteOrderMixing

variable {L : ℕ}

/-- The marker configuration through level `k` on `I`. -/
def rI (k : ℕ) (I : Finset ℤ) (h : Hspace) : (Finset.range (k + 1) ×ˢ I) → Bool :=
  fun p => h p.1.1 p.1.2

lemma measurable_rI (k : ℕ) (I : Finset ℤ) : Measurable (rI k I) :=
  measurable_pi_iff.mpr fun p => (measurable_pi_apply p.1.2).comp (measurable_pi_apply p.1.1)

/-- A local function factors through the marker configuration. -/
lemma factor_rI {f : Hspace → ℝ} {k : ℕ} {I : Finset ℤ}
    (hf : ∀ h h', AgreeOn k I h h' → f h = f h') :
    ∃ F : ((Finset.range (k + 1) ×ˢ I) → Bool) → ℝ, f = F ∘ rI k I := by
  classical
  refine ⟨fun y => f fun k' j => if hp : (k', j) ∈ Finset.range (k + 1) ×ˢ I then y ⟨_, hp⟩
    else false, funext fun h => hf _ _ fun k' hk' j hj => ?_⟩
  have : (k', j) ∈ Finset.range (k + 1) ×ˢ I :=
    Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), hj⟩
  simp [rI, this]

section Indep

variable {P : Measure Hspace} [IsProbabilityMeasure P] {D k : ℕ}
  (hind : ∀ I J : Finset ℤ, (∀ i ∈ I, ∀ j ∈ J, i + D * sc L k < j) →
    IndepFun (rI k I) (rI k J) P)
include hind

omit [IsProbabilityMeasure P] in
lemma integral_mul_local {f g : Hspace → ℝ} {I J : Finset ℤ}
    (hIJ : ∀ i ∈ I, ∀ j ∈ J, i + D * sc L k < j)
    (hf : ∀ h h', AgreeOn k I h h' → f h = f h') (hg : ∀ h h', AgreeOn k J h h' → g h = g h') :
    ∫ h, f h * g h ∂P = (∫ h, f h ∂P) * ∫ h, g h ∂P := by
  obtain ⟨F, rfl⟩ := factor_rI hf
  obtain ⟨G, rfl⟩ := factor_rI hg
  have hFG := (hind I J hIJ).comp (measurable_of_countable F) (measurable_of_countable G)
  exact hFG.integral_fun_mul_eq_mul_integral
    ((measurable_of_countable F).comp (measurable_rI k I)).aestronglyMeasurable
    ((measurable_of_countable G).comp (measurable_rI k J)).aestronglyMeasurable

/-- `(H4)` for finitely many ordered windows. -/
theorem integral_prod_local : ∀ (s : ℕ) (J : Fin s → Finset ℤ) (f : Fin s → Hspace → ℝ),
    (∀ i j : Fin s, i < j → ∀ x ∈ J i, ∀ y ∈ J j, x + D * sc L k < y) →
    (∀ i h h', AgreeOn k (J i) h h' → f i h = f i h') →
    ∫ h, ∏ i, f i h ∂P = ∏ i, ∫ h, f i h ∂P := by
  intro s
  induction s with
  | zero => intro J f _ _; simp
  | succ s ih =>
    intro J f hJ hf
    simp only [Fin.prod_univ_castSucc]
    classical
    rw [integral_mul_local hind (I := Finset.univ.biUnion fun i : Fin s => J i.castSucc)
      (J := J (Fin.last s)) ?_ ?_ (hf _)]
    · rw [ih (fun i => J i.castSucc) (fun i => f i.castSucc)
        (fun i j hij => hJ _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)) (fun i => hf _)]
    · intro x hx y hy
      obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.1 hx
      exact hJ _ _ (Fin.castSucc_lt_last i) x hxi y hy
    · intro h h' hA
      refine Finset.prod_congr rfl fun i _ => hf _ _ _ (hA.mono le_rfl ?_)
      exact Finset.subset_biUnion_of_mem (fun i : Fin s => J i.castSucc) (Finset.mem_univ i)

end Indep

/-! ## Products of bounded quantities -/

lemma abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (x y M : ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hx : ∀ i ∈ S, |x i| ≤ M i) (hy : ∀ i ∈ S, |y i| ≤ M i)
    (hxy : ∀ i ∈ S, |x i - y i| ≤ ε * M i) :
    |∏ i ∈ S, x i - ∏ i ∈ S, y i| ≤ S.card * ε * ∏ i ∈ S, M i := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hx' : ∀ i ∈ S, |x i| ≤ M i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hy' : ∀ i ∈ S, |y i| ≤ M i := fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hxy' : ∀ i ∈ S, |x i - y i| ≤ ε * M i := fun i hi => hxy i (Finset.mem_insert_of_mem hi)
    have hMa : 0 ≤ M a := (abs_nonneg _).trans (hx a (Finset.mem_insert_self a S))
    have hY : |∏ i ∈ S, y i| ≤ ∏ i ∈ S, M i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hy'
    have hMS : 0 ≤ ∏ i ∈ S, M i := (abs_nonneg _).trans hY
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      Finset.card_insert_of_notMem ha]
    have := ih hx' hy' hxy'
    calc |x a * ∏ i ∈ S, x i - y a * ∏ i ∈ S, y i|
        = |x a * (∏ i ∈ S, x i - ∏ i ∈ S, y i) + (x a - y a) * ∏ i ∈ S, y i| := by ring_nf
      _ ≤ |x a| * |∏ i ∈ S, x i - ∏ i ∈ S, y i| + |x a - y a| * |∏ i ∈ S, y i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ M a * (S.card * ε * ∏ i ∈ S, M i) + ε * M a * ∏ i ∈ S, M i := by
          gcongr
          · exact hx a (Finset.mem_insert_self a S)
          · exact hxy a (Finset.mem_insert_self a S)
      _ = ((S.card + 1 : ℕ) : ℝ) * ε * (M a * ∏ i ∈ S, M i) := by push_cast; ring

/-! ## Windows and mixing for `ν` -/

section Windows

variable {P : Measure Hspace} (hP : HierarchyLaw L P) (hL : 6 ≤ L) (hLe : Even L)
include hP hL hLe

/-- Integrals of cylinder functions computed at a fixed level at which the window meets at most
`L - 1` blocks. -/
lemma integral_nu_level {E W : Finset ℤ} (hEW : E ⊆ W) {k : ℕ}
    (hk : ∀ h, Good L h → (starts L h k W).card ≤ L - 1) {G : Config → ℝ} (hG : Dep G E) :
    ∫ ω, G ω ∂(nu hP hL hLe) = ∫ h, Eh L h k W G ∂P := by
  rw [integral_nu' hP hL hLe hEW (Nat.le_add_right (kE W) k) hG]
  refine integral_congr_ae ?_
  filter_upwards [hP.good] with h hg
  exact Eh_stab hg hL hLe (Nat.le_add_left k (kE W)) (hk h hg) (hG.mono hEW)

/-- **Proposition `prop:windows`** (product form): at level `k ≥ 1`, windows of length at most
`(4L)^k`, at most `(L-1)/2` of them, separated by more than `(D+7)(4L)^k`, are independent. -/
theorem nu_prod_windows {D : ℕ}
    (hD : ∀ (k : ℕ) (I J : Finset ℤ), (∀ i ∈ I, ∀ j ∈ J, i + D * sc L k < j) →
      IndepFun (rI k I) (rI k J) P)
    {k : ℕ} (hk : 1 ≤ k) (s : ℕ) (hs : 2 * s ≤ L - 1) (a b : Fin s → ℤ)
    (hlen : ∀ i, b i - a i < sc L k)
    (hsep : ∀ i j : Fin s, i < j → b i + (D + 7) * sc L k < a j)
    (G : Fin s → Config → ℝ) (hG : ∀ i, Dep (G i) (Finset.Icc (a i) (b i))) :
    ∫ ω, ∏ i, G i ω ∂(nu hP hL hLe) = ∏ i, ∫ ω, G i ω ∂(nu hP hL hLe) := by
  classical
  have := hP.isProb
  have hL1 : 1 ≤ L := by omega
  set I : Fin s → Finset ℤ := fun i => Finset.Icc (a i) (b i)
  set W := Finset.univ.biUnion I
  have hcard1 : ∀ h, Good L h → ∀ i, (starts L h k (I i)).card ≤ 2 := fun h hg i =>
    card_starts_le_two hg hk (fun x hx => Finset.mem_Icc.1 hx) (hlen i)
  have hcardW : ∀ h, Good L h → (starts L h k W).card ≤ L - 1 := by
    intro h hg
    have : starts L h k W = Finset.univ.biUnion fun i => starts L h k (I i) := by
      simp only [W, starts]
      ext x; simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨y, ⟨i, hi⟩, rfl⟩; exact ⟨i, y, hi, rfl⟩
      · rintro ⟨i, y, hi, rfl⟩; exact ⟨y, ⟨i, hi⟩, rfl⟩
    rw [this]
    calc _ ≤ ∑ i : Fin s, (starts L h k (I i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin s, 2 := Finset.sum_le_sum fun i _ => hcard1 h hg i
      _ = 2 * s := by simp [mul_comm]
      _ ≤ L - 1 := hs
  have hGW : Dep (fun ω => ∏ i, G i ω) W :=
    dep_prod _ _ _ fun i _ => (hG i).mono (Finset.subset_biUnion_of_mem I (Finset.mem_univ i))
  -- the product of expectations of the windows at level `k`
  have hfac : ∀ h, Good L h →
      Eh L h k W (fun ω => ∏ i, G i ω) = ∏ i, Eh L h k (I i) (G i) := by
    intro h hg
    -- induction on the number of windows, along `Fin.castSucc`
    suffices H : ∀ (t : ℕ) (ht : t ≤ s), Eh L h k
        ((Finset.univ.filter fun i : Fin s => i.val < t).biUnion I)
        (fun ω => ∏ i ∈ Finset.univ.filter (fun i : Fin s => i.val < t), G i ω) =
        ∏ i ∈ Finset.univ.filter (fun i : Fin s => i.val < t), Eh L h k (I i) (G i) by
      have := H s le_rfl
      simp only [Fin.is_lt] at this
      simpa [W] using this
    intro t
    induction t with
    | zero => intro _; simp [Eh_one hg hL hLe]
    | succ t ih =>
      intro ht
      have hfilt : (Finset.univ.filter fun i : Fin s => i.val < t + 1) =
          insert ⟨t, by omega⟩ (Finset.univ.filter fun i : Fin s => i.val < t) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi; by_cases hit : i.val = t
          · exact Or.inl (Fin.ext hit)
          · exact Or.inr (by omega)
        · rintro (rfl | hi) <;> simp; omega
      have hnot : (⟨t, by omega⟩ : Fin s) ∉ Finset.univ.filter fun i : Fin s => i.val < t := by
        simp
      rw [hfilt, Finset.biUnion_insert, Finset.prod_insert hnot]
      simp only [Finset.prod_insert hnot]
      rw [← ih (by omega)]
      refine Eh_union_mul hg hL hLe k ?_ (hG _) ?_
      · rw [Finset.disjoint_left]
        intro x hx' hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.1 hy
        obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.1 hx'
        have hit : i < (⟨t, by omega⟩ : Fin s) := by
          simp only [Finset.mem_filter] at hi; exact hi.2
        have h1 := prv_le hg k y
        have h2 := prv_gt hg k z
        have h3 := hsep i _ hit
        have hy' := Finset.mem_Icc.1 hyi
        have hz' := Finset.mem_Icc.1 hz
        have h4 : (3 : ℤ) * (sc L k : ℤ) ≤ ((D : ℤ) + 7) * (sc L k : ℤ) :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        omega
      · exact dep_prod _ _ _ fun i hi =>
          (hG i).mono (Finset.subset_biUnion_of_mem I hi)
  rw [integral_nu_level hP hL hLe (subset_refl W) hcardW hGW]
  rw [integral_congr_ae (g := fun h => ∏ i, Eh L h k (I i) (G i)) ?_]
  · rw [integral_prod_local (hD k) s (fun i => Finset.Icc (a i - 3 * sc L k) (b i + 4 * sc L k))
      (fun i h => Eh L h k (I i) (G i)) ?_ ?_]
    · refine Finset.prod_congr rfl fun i _ => ?_
      exact (integral_nu_level hP hL hLe (subset_refl _) (fun h hg => (hcard1 h hg i).trans
        (by omega)) (hG i)).symm
    · intro i j hij x hx y hy
      have h3 := hsep i j hij
      simp only [Finset.mem_Icc] at hx hy
      linarith
    · intro i h h' hA
      exact Eh_local hL1 (fun x hx => Finset.mem_Icc.1 hx) hA _
  · filter_upwards [hP.good] with h hg
    exact hfac h hg

/-- `ν(S) = ∫ 1_S dν`. -/
lemma nu_eq_ofReal_integral {S : Set Config} (hS : MeasurableSet S) :
    nu hP hL hLe S = ENNReal.ofReal (∫ ω, S.indicator 1 ω ∂(nu hP hL hLe)) := by
  rw [integral_indicator_one hS, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

omit hP hLe in
/-- A level `k ≥ 1` with `M ≤ (4L)^k ≤ 4L·M`. -/
lemma exists_level {M : ℕ} (hM : 1 ≤ M) : ∃ k, 1 ≤ k ∧ M ≤ sc L k ∧ sc L k ≤ 4 * L * M := by
  classical
  have hL1 : 1 ≤ L := by omega
  have hex : ∃ j, M ≤ sc L (j + 1) := ⟨M, by
    have h1 := lt_sc_self hL1 M
    have h2 : sc L M ≤ sc L (M + 1) := by
      rw [sc_succ]; exact Nat.le_mul_of_pos_left _ (by omega)
    omega⟩
  refine ⟨Nat.find hex + 1, by omega, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, zero_add, sc_succ]; simp [sc]; nlinarith
  · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    push Not at hmin
    rw [hj, sc_succ]
    exact Nat.mul_le_mul_left _ hmin.le

/-- **Proposition `prop:windows`** (product form, with a uniform separation constant). -/
theorem nu_prod_windowsK : ∃ K : ℕ, ∀ (s : ℕ), 2 * s ≤ L - 1 → ∀ (a b : Fin s → ℤ),
    WindowsSeparated K a b → ∀ (G : Fin s → Config → ℝ),
    (∀ i, Dep (G i) (Finset.Icc (a i) (b i))) →
    ∫ ω, ∏ i, G i ω ∂(nu hP hL hLe) = ∏ i, ∫ ω, G i ω ∂(nu hP hL hLe) := by
  classical
  obtain ⟨D, hD⟩ := hP.indep
  refine ⟨4 * L * (D + 8), fun s hs a b hab G hG => ?_⟩
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0; have := hP.isProb; simp
  set M := Finset.univ.sup fun l : Fin s => (b l - a l + 1).toNat
  have hMl : ∀ l, b l - a l + 1 ≤ M := fun l => by
    have := Finset.le_sup (f := fun l : Fin s => (b l - a l + 1).toNat) (Finset.mem_univ l)
    have := hab.1 l
    omega
  obtain ⟨l0, -, hl0⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty_iff.2 ⟨⟨0, hs0⟩⟩) fun l : Fin s => (b l - a l + 1).toNat
  have hM : M = (b l0 - a l0 + 1).toNat := hl0
  have hM1 : 1 ≤ M := by have := hab.1 l0; rw [hM]; omega
  obtain ⟨k, hk1, hMk, hkM⟩ := exists_level hL hM1
  refine nu_prod_windows hP hL hLe (fun k I J h => hD k I J h) hk1 s hs a b
    (fun i => by have := hMl i; omega) (fun i j hij => ?_) G hG
  have h1 := hab.2 i j l0 hij
  have h2 : (b l0 - a l0 + 1 : ℤ) = M := by
    have := hab.1 l0; rw [hM]; omega
  rw [h2] at h1
  have h3 : ((D : ℤ) + 7) * sc L k ≤ (4 * L * (D + 8) : ℕ) * (M : ℤ) := by
    have : ((D : ℤ) + 7) * sc L k ≤ ((D : ℤ) + 8) * (4 * L * M : ℕ) := by
      have : (sc L k : ℤ) ≤ (4 * L * M : ℕ) := by exact_mod_cast hkM
      nlinarith
    push_cast at this ⊢; nlinarith
  push_cast at h1 h3 ⊢
  linarith

/-- **Proposition `prop:windows`**: joint independence of separated windows. -/
theorem nu_windows : ∃ K : ℕ, ∀ (s : ℕ), 2 * s ≤ L - 1 → ∀ (a b : Fin s → ℤ),
    WindowsSeparated K a b → iIndepFun (fun i => window (a i) (b i)) (nu hP hL hLe) := by
  classical
  obtain ⟨K, hK⟩ := nu_prod_windowsK hP hL hLe
  refine ⟨K, fun s hs a b hab => ?_⟩
  have hmeas : ∀ i, Measurable (window (a i) (b i)) := fun i =>
    measurable_pi_iff.mpr fun j => measurable_pi_apply _
  refine iIndepFun_of_singleton hmeas fun y => ?_
  have hset : ∀ i, {ω | window (a i) (b i) ω = y i} = {ω | restr (Finset.Icc (a i) (b i)) ω = y i} :=
    fun i => rfl
  have hind : Set.indicator {ω : Config | ∀ i, window (a i) (b i) ω = y i} 1 =
      fun ω => ∏ i, indPat (Finset.Icc (a i) (b i)) (y i) ω := by
    funext ω
    simp only [indPat, Finset.prod_boole, Finset.mem_univ, true_implies]
    simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    rfl
  have hmS : MeasurableSet {ω : Config | ∀ i, window (a i) (b i) ω = y i} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => hmeas i (measurableSet_singleton _)
  rw [nu_eq_ofReal_integral hP hL hLe hmS, hind,
    hK s hs a b hab _ fun i => dep_indPat _ _,
    ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg fun ω => indPat_nonneg _ _ ω]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hset, integral_indPat, nu_cyl]

/-! ## Exponential mixing -/

omit hP hL hLe in
lemma dθ_le_of_agree {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {ω ω' : Config} {ℓ : ℕ}
    (h : ∀ j : ℤ, j.natAbs ≤ ℓ → ω j = ω' j) : dθ θ ω ω' ≤ θ ^ (ℓ + 1) := by
  classical
  unfold dθ
  split_ifs with hex
  · apply pow_le_pow_of_le_one hθ0 hθ1
    by_contra hlt
    push Not at hlt
    obtain ⟨j, hj, hne⟩ := Nat.find_spec hex
    exact hne (h j (by omega))
  · exact pow_nonneg hθ0 _

/-- Truncation of a configuration outside `[-ℓ, ℓ]`. -/
def trunc (ℓ : ℕ) (ω : Config) : Config := fun j => if j.natAbs ≤ ℓ then ω j else true

omit hP hL hLe in
lemma holder_trunc {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {F : Config → ℝ} {A : ℝ}
    (hF : HolderBound θ F A) (ℓ : ℕ) (ω : Config) : |F ω - F (trunc ℓ ω)| ≤ A * θ ^ (ℓ + 1) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (hF.1 ω)
  exact (hF.2 _ _).trans (mul_le_mul_of_nonneg_left
    (dθ_le_of_agree hθ0 hθ1 fun j hj => by simp [trunc, hj]) hA)

omit hP hL hLe in
lemma dep_trunc (F : Config → ℝ) (ℓ : ℕ) (n : ℤ) :
    Dep (fun ω => F (trunc ℓ (transl n ω))) (Finset.Icc (n - ℓ) (n + ℓ)) := by
  intro ω ω' h
  have : trunc ℓ (transl n ω) = trunc ℓ (transl n ω') := by
    funext j
    simp only [trunc, transl_apply]
    split_ifs with hj
    · exact h (j + n) (Finset.mem_Icc.2 (by omega))
    · rfl
  simp only [this]

omit hP hL hLe in
lemma HolderBound.measurable {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {F : Config → ℝ} {A : ℝ}
    (hF : HolderBound θ F A) : Measurable F := by
  refine measurable_of_tendsto_metrizable (f := fun ℓ ω => F (trunc ℓ ω))
    (fun ℓ => by simpa [transl_zero] using (dep_trunc F ℓ 0).measurable) ?_
  refine tendsto_pi_nhds.2 fun ω => ?_
  have h0 : Tendsto (fun ℓ : ℕ => A * θ ^ (ℓ + 1)) atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).comp (tendsto_add_atTop_nat 1)
    simpa using this.const_mul A
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun ℓ => ?_) h0
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact holder_trunc hθ0.le hθ1.le hF ℓ ω

omit hP hL hLe in
lemma shift_iterate_eq (n : ℕ) (ω : Config) : shift^[n] ω = transl n ω := by
  funext j; simp [shift_iterate_apply]

lemma integral_shift_iterate {F : Config → ℝ} (hF : Measurable F) (n : ℕ) :
    ∫ ω, F (shift^[n] ω) ∂(nu hP hL hLe) = ∫ ω, F ω ∂(nu hP hL hLe) := by
  have hmp := (nu_measurePreserving hP hL hLe).iterate n
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable]

omit hP hL hLe in
lemma abs_integral_le_of_bound {μ : Measure Config} [IsProbabilityMeasure μ] {g : Config → ℝ}
    {C : ℝ} (hg : ∀ ω, |g ω| ≤ C) : |∫ ω, g ω ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := C)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hg ω)
  simpa [Real.norm_eq_abs] using this

/-- **Proposition `prop:holder`**: exponential mixing of every order `s` with `2s ≤ L - 1`. -/
theorem nu_expMixing (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (s : ℕ) (hs : 2 * s ≤ L - 1) :
    ExpMixingOrder (nu hP hL hLe) shift (HolderBound θ) s := by
  classical
  obtain ⟨K, hK⟩ := nu_prod_windowsK hP hL hLe
  set c := |Real.log θ| / (4 * (K + 1)) with hcdef
  have hlog : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hc : 0 < c := div_pos (abs_pos.2 hlog.ne) (by positivity)
  refine ⟨(2 * s + 2) * Real.exp (c * (2 * K + 2)), c, hc, ?_⟩
  intro f A hfA n hn d hd
  set ν := nu hP hL hLe
  have hA0 : ∀ i, 0 ≤ A i := fun i => (abs_nonneg _).trans ((hfA i).1 allTrue)
  have hfm : ∀ i, Measurable (f i) := fun i => (hfA i).measurable hθ0 hθ1
  set X : Fin s → Config → ℝ := fun i ω => f i (shift^[n i] ω)
  have hXm : ∀ i, Measurable (X i) := fun i => (hfm i).comp (measurable_shift.iterate _)
  have hXb : ∀ i ω, |X i ω| ≤ A i := fun i ω => (hfA i).1 (shift^[n i] ω)
  have hPA : 0 ≤ ∏ i, A i := Finset.prod_nonneg fun i _ => hA0 i
  have hprodX : ∀ ω, |∏ i, X i ω| ≤ ∏ i, A i := fun ω => by
    rw [Finset.abs_prod]; exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => hXb i ω
  have hint : ∀ i, |∫ ω, f i ω ∂ν| ≤ A i := fun i => abs_integral_le_of_bound (hfA i).1
  have hprodI : |∏ i, ∫ ω, f i ω ∂ν| ≤ ∏ i, A i := by
    rw [Finset.abs_prod]; exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => hint i
  have hLHS : |∫ ω, ∏ i, X i ω ∂ν| ≤ ∏ i, A i := abs_integral_le_of_bound hprodX
  change |∫ x, ∏ i, X i x ∂ν - ∏ i, ∫ x, f i x ∂ν| ≤ _
  have hCpos : 0 < (2 * s + 2) * Real.exp (c * (2 * K + 2)) := by positivity
  by_cases hdK : d ≤ 2 * K + 2
  · -- the trivial bound
    have hexp : 2 ≤ (2 * s + 2) * Real.exp (c * (2 * K + 2)) * Real.exp (-c * d) := by
      rw [mul_assoc, ← Real.exp_add]
      have : 0 ≤ c * (2 * K + 2) + -c * d := by nlinarith
      have := Real.one_le_exp this
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      nlinarith
    calc |∫ x, ∏ i, X i x ∂ν - ∏ i, ∫ x, f i x ∂ν|
        ≤ |∫ x, ∏ i, X i x ∂ν| + |∏ i, ∫ x, f i x ∂ν| := abs_sub _ _
      _ ≤ 2 * ∏ i, A i := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp hPA
  · push Not at hdK
    have hd0 : 0 < d := by have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith
    set ℓ := ⌊d / (4 * (K + 1))⌋₊
    set ε := θ ^ (ℓ + 1)
    have hε0 : 0 ≤ ε := pow_nonneg hθ0.le _
    have hℓle : (ℓ : ℝ) ≤ d / (4 * (K + 1)) := Nat.floor_le (by positivity)
    have hℓlt : d / (4 * (K + 1)) < ℓ + 1 := Nat.lt_floor_add_one _
    -- truncated observables
    set Y : Fin s → Config → ℝ := fun i ω => f i (trunc ℓ (transl (n i) ω))
    have hYdep : ∀ i, Dep (Y i) (Finset.Icc ((n i : ℤ) - ℓ) (n i + ℓ)) :=
      fun i => dep_trunc (f i) ℓ (n i)
    have hXY : ∀ i ω, |X i ω - Y i ω| ≤ ε * A i := fun i ω => by
      simp only [X, Y, shift_iterate_eq]
      rw [mul_comm]; exact holder_trunc hθ0.le hθ1.le (hfA i) ℓ _
    have hYb : ∀ i ω, |Y i ω| ≤ A i := fun i ω => (hfA i).1 (trunc ℓ (transl (n i) ω))
    -- the windows are separated
    have hsep : WindowsSeparated K (fun i => (n i : ℤ) - ℓ) (fun i => (n i : ℤ) + ℓ) := by
      refine ⟨fun i => by show (n i : ℤ) - ℓ ≤ n i + ℓ; omega, fun i j l hij => ?_⟩
      have hg := hd i j hij
      have : ((n i : ℤ) + ℓ + K * ((n l + ℓ) - (n l - ℓ) + 1) : ℝ) < ((n j : ℤ) - ℓ : ℝ) := by
        push_cast
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        have : 2 * (K + 1) * (ℓ : ℝ) ≤ d / 2 := by
          have := mul_le_mul_of_nonneg_left hℓle (by positivity : (0 : ℝ) ≤ 2 * (K + 1))
          calc 2 * (K + 1) * (ℓ : ℝ) ≤ 2 * (K + 1) * (d / (4 * (K + 1))) := this
            _ = d / 2 := by field_simp; ring
        nlinarith
      exact_mod_cast this
    have hprodY : ∫ ω, ∏ i, Y i ω ∂ν = ∏ i, ∫ ω, f i (trunc ℓ ω) ∂ν := by
      rw [hK s hs _ _ hsep Y hYdep]
      refine Finset.prod_congr rfl fun i _ => ?_
      have := integral_shift_iterate hP hL hLe (F := fun ω => f i (trunc ℓ ω))
        (by simpa [transl_zero] using (dep_trunc (f i) ℓ 0).measurable) (n i)
      simp only [shift_iterate_eq] at this
      exact this
    have hYm : ∀ i, Measurable (Y i) := fun i => (hYdep i).measurable
    have hintX : Integrable (fun ω => ∏ i, X i ω) ν :=
      Integrable.of_bound (Finset.measurable_prod _ fun i _ => hXm i).aestronglyMeasurable
        (∏ i, A i) (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hprodX ω)
    have hintY : Integrable (fun ω => ∏ i, Y i ω) ν :=
      Integrable.of_bound (Finset.measurable_prod _ fun i _ => hYm i).aestronglyMeasurable
        (∏ i, A i) (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, Finset.abs_prod]
          exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => hYb i ω)
    have hstep1 : |∫ ω, ∏ i, X i ω ∂ν - ∫ ω, ∏ i, Y i ω ∂ν| ≤ s * ε * ∏ i, A i := by
      rw [← integral_sub hintX hintY]
      refine abs_integral_le_of_bound fun ω => ?_
      have := abs_prod_sub_prod_le Finset.univ (fun i => X i ω) (fun i => Y i ω) A hε0
        (fun i _ => hXb i ω) (fun i _ => hYb i ω) (fun i _ => hXY i ω)
      simpa using this
    have hstep2 : |∏ i, ∫ ω, f i (trunc ℓ ω) ∂ν - ∏ i, ∫ ω, f i ω ∂ν| ≤ s * ε * ∏ i, A i := by
      have := abs_prod_sub_prod_le Finset.univ (fun i => ∫ ω, f i (trunc ℓ ω) ∂ν)
        (fun i => ∫ ω, f i ω ∂ν) A hε0 (fun i _ => abs_integral_le_of_bound fun ω => (hfA i).1 _)
        (fun i _ => hint i) (fun i _ => by
          have hm1 : Measurable fun ω => f i (trunc ℓ ω) := by
            simpa [transl_zero] using (dep_trunc (f i) ℓ 0).measurable
          have hi1 : Integrable (fun ω => f i (trunc ℓ ω)) ν :=
            Integrable.of_bound hm1.aestronglyMeasurable (A i)
              (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact (hfA i).1 _)
          have hi2 : Integrable (f i) ν :=
            Integrable.of_bound (hfm i).aestronglyMeasurable (A i)
              (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact (hfA i).1 _)
          rw [← integral_sub hi1 hi2]
          refine abs_integral_le_of_bound fun ω => ?_
          rw [abs_sub_comm, mul_comm]
          exact holder_trunc hθ0.le hθ1.le (hfA i) ℓ ω)
      simpa using this
    have hεexp : ε ≤ Real.exp (-c * d) := by
      have hθe : θ = Real.exp (Real.log θ) := (Real.exp_log hθ0).symm
      have : ε = Real.exp (((ℓ + 1 : ℕ) : ℝ) * Real.log θ) := by
        simp only [ε]; rw [Real.exp_nat_mul, ← hθe]
      rw [this, Real.exp_le_exp]
      have habs : |Real.log θ| = -Real.log θ := abs_of_neg hlog
      have hK1 : (0 : ℝ) < 4 * (K + 1) := by positivity
      have : -c * d = (d / (4 * (K + 1))) * Real.log θ := by
        rw [hcdef, habs]; field_simp
      rw [this]
      push_cast
      exact mul_le_mul_of_nonpos_right hℓlt.le hlog.le
    have hexp1 : 1 ≤ Real.exp (c * (2 * K + 2)) := Real.one_le_exp (by positivity)
    calc |∫ x, ∏ i, X i x ∂ν - ∏ i, ∫ x, f i x ∂ν|
        = |(∫ ω, ∏ i, X i ω ∂ν - ∫ ω, ∏ i, Y i ω ∂ν) +
            (∏ i, ∫ ω, f i (trunc ℓ ω) ∂ν - ∏ i, ∫ ω, f i ω ∂ν)| := by rw [hprodY]; ring_nf
      _ ≤ s * ε * ∏ i, A i + s * ε * ∏ i, A i := (abs_add_le _ _).trans (add_le_add hstep1 hstep2)
      _ = (2 * s) * ε * ∏ i, A i := by ring
      _ ≤ (2 * s) * Real.exp (-c * d) * ∏ i, A i := by gcongr
      _ ≤ (2 * s + 2) * Real.exp (c * (2 * K + 2)) * Real.exp (-c * d) * ∏ i, A i := by
          apply mul_le_mul_of_nonneg_right _ hPA
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
          nlinarith

end Windows

end FiniteOrderMixing
