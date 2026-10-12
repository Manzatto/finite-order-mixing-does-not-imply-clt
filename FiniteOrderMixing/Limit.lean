import FiniteOrderMixing.Locality

/-!
# The stationary limiting process (Proposition `prop:limit`)

We fix a law `P` of the nested marker sets satisfying `(H1)–(H4)` (`HierarchyLaw`).  The measure
`ν` on `Σ = {-1,1}^ℤ` is obtained from the Kolmogorov extension theorem, its finite-dimensional
marginals being the stabilised finite-level laws averaged over the marker sets:

`ν(ω|_E = x) = ∫ Eh L h (kE E) E 1_{x} dP(h)`.

Main result: `integral_nu'`, which computes `∫ G dν` for any function `G` of finitely many
coordinates as `∫ Eh L h ℓ W G dP(h)` at any sufficiently high level `ℓ`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace FiniteOrderMixing

/-! ## Hierarchy laws -/

/-- A law of the nested marker sets with the properties `(H1)–(H4)` of Proposition
`prop:hierarchy`: almost surely good (`(H1)–(H2)`), stationary (`(H3)`), and with marker
configurations through level `k` that are `D(4L)^k`-dependent (`(H4)`). -/
structure HierarchyLaw (L : ℕ) (P : Measure Hspace) : Prop where
  isProb : IsProbabilityMeasure P
  good : ∀ᵐ h ∂P, Good L h
  stationary : ∀ m : ℤ, MeasurePreserving (shiftH m) P P
  indep : ∃ D : ℕ, ∀ (k : ℕ) (I J : Finset ℤ), (∀ i ∈ I, ∀ j ∈ J, i + D * sc L k < j) →
    IndepFun (fun h : Hspace => fun p : (Finset.range (k + 1) ×ˢ I) => h p.1.1 p.1.2)
      (fun h : Hspace => fun p : (Finset.range (k + 1) ×ˢ J) => h p.1.1 p.1.2) P

/-! ## Cylinder functions -/

/-- Restriction of a configuration to the coordinates in `E`. -/
def restr (E : Finset ℤ) (ω : Config) : E → Bool := fun j => ω j

@[fun_prop]
lemma measurable_restr (E : Finset ℤ) : Measurable (restr E) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- Extension of a pattern on `E` by `true` outside `E`. -/
def extE (E : Finset ℤ) (x : E → Bool) : Config :=
  fun j => if hj : j ∈ E then x ⟨j, hj⟩ else true

lemma restr_extE (E : Finset ℤ) (x : E → Bool) : restr E (extE E x) = x := by
  funext j; simp [restr, extE, j.2]

lemma Dep.eq_extE {G : Config → ℝ} {E : Finset ℤ} (hG : Dep G E) (ω : Config) :
    G ω = G (extE E (restr E ω)) := hG _ _ fun j hj => by simp [extE, restr, hj]

lemma Dep.measurable {G : Config → ℝ} {E : Finset ℤ} (hG : Dep G E) : Measurable G := by
  have : G = (G ∘ extE E) ∘ restr E := funext fun ω => hG.eq_extE ω
  rw [this]; exact (measurable_of_countable _).comp (measurable_restr E)

lemma Dep.bounded {G : Config → ℝ} {E : Finset ℤ} (hG : Dep G E) : ∃ C, ∀ ω, |G ω| ≤ C :=
  ⟨∑ x : E → Bool, |G (extE E x)|, fun ω => by
    rw [hG.eq_extE ω]
    exact Finset.single_le_sum (f := fun x => |G (extE E x)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ _)⟩

lemma Dep.integrable {G : Config → ℝ} {E : Finset ℤ} (hG : Dep G E) (μ : Measure Config)
    [IsFiniteMeasure μ] : Integrable G μ := by
  obtain ⟨C, hC⟩ := hG.bounded
  exact Integrable.of_bound hG.measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)

/-- Indicator of the pattern `x` on `E`. -/
noncomputable def indPat (E : Finset ℤ) (x : E → Bool) (ω : Config) : ℝ :=
  if restr E ω = x then 1 else 0

lemma dep_indPat (E : Finset ℤ) (x : E → Bool) : Dep (indPat E x) E := fun ω ω' h => by
  have : restr E ω = restr E ω' := funext fun j => h j j.2
  simp [indPat, this]

lemma indPat_nonneg (E : Finset ℤ) (x : E → Bool) (ω : Config) : 0 ≤ indPat E x ω := by
  unfold indPat; split_ifs <;> norm_num

lemma sum_indPat (E : Finset ℤ) (ω : Config) : ∑ x : E → Bool, indPat E x ω = 1 := by
  simp [indPat]

lemma Dep.decomp {G : Config → ℝ} {E : Finset ℤ} (hG : Dep G E) (ω : Config) :
    G ω = ∑ x : E → Bool, G (extE E x) * indPat E x ω := by
  rw [Finset.sum_eq_single (restr E ω)]
  · simp [indPat, ← hG.eq_extE]
  · intro x _ hx; simp [indPat, Ne.symm hx]
  · simp

/-! ## Choice of the stabilisation level -/

/-- `E ⊆ [-bnd E, bnd E]`. -/
def bnd (E : Finset ℤ) : ℕ := ∑ j ∈ E, j.natAbs

/-- A level at which `E` meets at most two blocks. -/
def kE (E : Finset ℤ) : ℕ := 2 * bnd E + 1

lemma mem_bnd {E : Finset ℤ} {j : ℤ} (hj : j ∈ E) : -(bnd E : ℤ) ≤ j ∧ j ≤ bnd E := by
  have : j.natAbs ≤ bnd E :=
    Finset.single_le_sum (f := fun j : ℤ => j.natAbs) (fun _ _ => Nat.zero_le _) hj
  omega

lemma bnd_mono {E F : Finset ℤ} (h : E ⊆ F) : bnd E ≤ bnd F :=
  Finset.sum_le_sum_of_subset h

lemma kE_mono {E F : Finset ℤ} (h : E ⊆ F) : kE E ≤ kE F := by
  simp only [kE]; have := bnd_mono h; omega

variable {L : ℕ}

lemma lt_sc_self (hL : 1 ≤ L) (n : ℕ) : n < sc L n := by
  unfold sc; exact Nat.lt_pow_self (by omega)

/-- A window of length at most `(4L)^k` meets at most two level-`k` blocks. -/
lemma card_starts_le_two {h : Hspace} (hg : Good L h) {k : ℕ} (hk : 1 ≤ k) {W : Finset ℤ}
    {lo hi : ℤ} (hW : ∀ i ∈ W, lo ≤ i ∧ i ≤ hi) (hlen : hi - lo < sc L k) :
    (starts L h k W).card ≤ 2 := by
  classical
  set a := prv L h k lo
  set b := nxt L h k a
  have hsub : starts L h k W ⊆ {a, b} := by
    intro x hx
    obtain ⟨i, hi', rfl⟩ := Finset.mem_image.1 hx
    have hiW := hW i hi'
    have hla : a ≤ lo := prv_le hg k lo
    have hlb : lo < b := lt_nxt_prv hg k lo
    by_cases hib : i < b
    · have : prv L h k i = a := prv_eq_of_mem_blk hg (prv_mem hg k lo)
        (by simp only [blk, Finset.mem_Ico]; omega)
      simp [this]
    · have hbm : h k b = true := nxt_mem hg k a
      have hc := hg.sep k hk b (nxt L h k b) hbm (nxt_mem hg k b) (lt_nxt hg k b)
      have : prv L h k i = b := prv_eq_of_mem_blk hg hbm
        (by simp only [blk, Finset.mem_Ico]; omega)
      simp [this]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

lemma card_starts_kE {h : Hspace} (hg : Good L h) (hL : 6 ≤ L) (E : Finset ℤ) :
    (starts L h (kE E) E).card ≤ L - 1 := by
  have := card_starts_le_two hg (by simp [kE]) (fun i hi => mem_bnd hi)
    (show (bnd E : ℤ) - -(bnd E : ℤ) < sc L (kE E) by
      have := lt_sc_self (L := L) (by omega) (kE E); simp only [kE] at this ⊢; omega)
  omega

section Limit

variable {P : Measure Hspace} (hP : HierarchyLaw L P) (hL : 6 ≤ L) (hLe : Even L)
include hP hL hLe

omit hP in
lemma Eh_const {h : Hspace} (hg : Good L h) (ℓ : ℕ) (W : Finset ℤ) (c : ℝ) :
    Eh L h ℓ W (fun _ => c) = c := by
  rw [Eh_congr' (fun _ => (mul_one c).symm), Eh_const_mul, Eh_one hg hL hLe, mul_one]

omit hP hLe in
lemma measurable_Eh (ℓ : ℕ) (W : Finset ℤ) (G : Config → ℝ) :
    Measurable (fun h => Eh L h ℓ W G) :=
  measurable_of_agreeOn ℓ (Finset.Icc (-(bnd W : ℤ) - 3 * sc L ℓ) (bnd W + 4 * sc L ℓ))
    fun _ _ hA => Eh_local (by omega) (fun i hi => mem_bnd hi) hA G

omit hP in
lemma Eh_abs_le {h : Hspace} (hg : Good L h) {ℓ : ℕ} {W : Finset ℤ} {G : Config → ℝ} {C : ℝ}
    (hC : ∀ ω, |G ω| ≤ C) : |Eh L h ℓ W G| ≤ C := by
  rw [abs_le]
  constructor
  · have := Eh_mono hg hL hLe (ℓ := ℓ) (W := W) (F := fun _ => -C) (G := G)
      fun ω => (abs_le.1 (hC ω)).1
    rwa [Eh_const hL hLe hg] at this
  · have := Eh_mono hg hL hLe (ℓ := ℓ) (W := W) (F := G) (G := fun _ => C)
      fun ω => (abs_le.1 (hC ω)).2
    rwa [Eh_const hL hLe hg] at this

lemma integrable_Eh {W : Finset ℤ} {G : Config → ℝ} (hG : Dep G W) (ℓ : ℕ) :
    Integrable (fun h => Eh L h ℓ W G) P := by
  obtain ⟨C, hC⟩ := hG.bounded
  have := hP.isProb
  refine Integrable.of_bound (measurable_Eh hL ℓ W G).aestronglyMeasurable C ?_
  filter_upwards [hP.good] with h hg
  rw [Real.norm_eq_abs]; exact Eh_abs_le hL hLe hg hC

omit hP in
/-- Stabilised expectations at any sufficiently high level and on any larger window agree. -/
lemma Eh_eq_kE {h : Hspace} (hg : Good L h) {E W : Finset ℤ} (hEW : E ⊆ W) {ℓ : ℕ}
    (hℓ : kE W ≤ ℓ) {G : Config → ℝ} (hG : Dep G E) :
    Eh L h ℓ W G = Eh L h (kE E) E G := by
  rw [Eh_eq_of_superset hg hL hLe hEW hG,
    Eh_stab hg hL hLe ((kE_mono hEW).trans hℓ) (card_starts_kE hg hL E) hG]

end Limit

/-! ## The finite-dimensional marginals -/

variable (L) in
/-- The probability of the pattern `x` on `E`. -/
noncomputable def qP (P : Measure Hspace) (E : Finset ℤ) (x : E → Bool) : ℝ :=
  ∫ h, Eh L h (kE E) E (indPat E x) ∂P

variable (L) in
/-- The finite-dimensional marginal on `E`. -/
noncomputable def Pfin (P : Measure Hspace) (E : Finset ℤ) : Measure (E → Bool) :=
  ∑ x : E → Bool, ENNReal.ofReal (qP L P E x) • Measure.dirac x

section Marginals

variable {P : Measure Hspace} (hP : HierarchyLaw L P) (hL : 6 ≤ L) (hLe : Even L)
include hP hL hLe

lemma qP_nonneg (E : Finset ℤ) (x : E → Bool) : 0 ≤ qP L P E x := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [hP.good] with h hg
  exact Eh_nonneg hg hL hLe (indPat_nonneg E x)

omit hP hL hLe in
lemma Pfin_singleton (E : Finset ℤ) (x : E → Bool) :
    Pfin L P E {x} = ENNReal.ofReal (qP L P E x) := by
  classical
  simp only [Pfin, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [hy]
  · simp

open Classical in
lemma Pfin_apply (E : Finset ℤ) (S : Set (E → Bool)) :
    Pfin L P E S = ENNReal.ofReal (∑ x ∈ Finset.univ.filter (· ∈ S), qP L P E x) := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg fun x _ => qP_nonneg hP hL hLe E x]
  simp only [Pfin, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

lemma sum_qP_filter {E F : Finset ℤ} (hEF : E ⊆ F) (x : E → Bool) :
    ∑ y ∈ Finset.univ.filter (fun y : F → Bool => (fun j : E => y ⟨j, hEF j.2⟩) = x), qP L P F y =
      qP L P E x := by
  classical
  simp only [qP]
  rw [← integral_finsetSum _ fun y _ => integrable_Eh hP hL hLe (dep_indPat F y) _]
  refine integral_congr_ae ?_
  filter_upwards [hP.good] with h hg
  rw [← Eh_sum]
  have hpt : ∀ ω, ∑ y ∈ Finset.univ.filter
      (fun y : F → Bool => (fun j : E => y ⟨j, hEF j.2⟩) = x), indPat F y ω = indPat E x ω := by
    intro ω
    by_cases hω : restr E ω = x
    · rw [Finset.sum_eq_single (restr F ω)]
      · simp [indPat, hω]
      · intro y _ hy; simp [indPat, Ne.symm hy]
      · intro hmem
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [← hω]; rfl⟩) hmem
    · rw [Finset.sum_eq_zero]
      · simp [indPat, hω]
      · intro y hy
        have hy' := (Finset.mem_filter.1 hy).2
        have : restr F ω ≠ y := fun h => hω (by rw [← hy', ← h]; rfl)
        simp [indPat, this]
  rw [Eh_congr' hpt]
  exact Eh_eq_kE hL hLe hg hEF le_rfl (dep_indPat E x)

lemma Pfin_isProb (E : Finset ℤ) : IsProbabilityMeasure (Pfin L P E) := by
  classical
  have := hP.isProb
  have h1 : ∑ x : E → Bool, qP L P E x = 1 := by
    simp only [qP]
    rw [← integral_finsetSum _ fun y _ => integrable_Eh hP hL hLe (dep_indPat E y) _]
    rw [integral_congr_ae (g := fun _ => (1 : ℝ)) ?_]
    · simp
    filter_upwards [hP.good] with h hg
    rw [← Eh_sum, Eh_congr' (sum_indPat E), Eh_one hg hL hLe]
  constructor
  rw [Pfin_apply hP hL hLe, ← ENNReal.ofReal_one, ← h1]
  congr 1
  exact Finset.sum_congr (by ext x; simp) fun _ _ => rfl

lemma Pfin_proj (E F : Finset ℤ) (hEF : E ⊆ F) :
    (Pfin L P F).map (fun y : F → Bool => fun j : E => y ⟨j, hEF j.2⟩) = Pfin L P E := by
  classical
  refine Measure.ext_of_singleton fun x => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x),
    Pfin_apply hP hL hLe, Pfin_singleton, ← sum_qP_filter hP hL hLe hEF x]
  congr 1
  exact Finset.sum_congr (by ext y; simp) fun _ _ => rfl

end Marginals

/-! ## The measure `ν` -/

section Nu

variable {P : Measure Hspace} (hP : HierarchyLaw L P) (hL : 6 ≤ L) (hLe : Even L)
include hP hL hLe

lemma exists_nu : ∃ ν : Measure Config, IsProbabilityMeasure ν ∧
    ∀ E : Finset ℤ, ν.map (fun ω : Config => fun j : E => ω j) = Pfin L P E :=
  @kolmogorov_extension (Pfin L P) (fun E => Pfin_isProb hP hL hLe E)
    (fun E F hEF => Pfin_proj hP hL hLe E F hEF)

/-- The law `ν` of the process `Z` (Proposition `prop:limit`). -/
noncomputable def nu : Measure Config := Classical.choose (exists_nu hP hL hLe)

instance nu_isProb : IsProbabilityMeasure (nu hP hL hLe) :=
  (Classical.choose_spec (exists_nu hP hL hLe)).1

lemma nu_map (E : Finset ℤ) : (nu hP hL hLe).map (restr E) = Pfin L P E :=
  (Classical.choose_spec (exists_nu hP hL hLe)).2 E

lemma nu_cyl (E : Finset ℤ) (x : E → Bool) :
    nu hP hL hLe {ω | restr E ω = x} = ENNReal.ofReal (qP L P E x) := by
  have : ((nu hP hL hLe).map (restr E)) {x} = Pfin L P E {x} := by rw [nu_map hP hL hLe E]
  rw [Measure.map_apply (measurable_restr E) (measurableSet_singleton x),
    Pfin_singleton] at this
  exact this

lemma integral_indPat (E : Finset ℤ) (x : E → Bool) :
    ∫ ω, indPat E x ω ∂(nu hP hL hLe) = qP L P E x := by
  have hset : MeasurableSet {ω | restr E ω = x} :=
    measurable_restr E (measurableSet_singleton x)
  have : indPat E x = Set.indicator {ω | restr E ω = x} 1 := by
    funext ω; simp [indPat, Set.indicator]
  rw [this, integral_indicator_one hset, measureReal_def, nu_cyl,
    ENNReal.toReal_ofReal (qP_nonneg hP hL hLe E x)]

/-- **Integrals of cylinder functions** against `ν`. -/
theorem integral_nu {E : Finset ℤ} {G : Config → ℝ} (hG : Dep G E) :
    ∫ ω, G ω ∂(nu hP hL hLe) = ∫ h, Eh L h (kE E) E G ∂P := by
  have h1 : ∫ ω, G ω ∂(nu hP hL hLe) =
      ∑ x : E → Bool, G (extE E x) * qP L P E x := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hG.decomp),
      integral_finsetSum _ fun x _ => ((dep_indPat E x).integrable _).const_mul _]
    exact Finset.sum_congr rfl fun x _ => by rw [integral_const_mul, integral_indPat]
  rw [h1]
  simp only [qP]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun x _ => (integrable_Eh hP hL hLe (dep_indPat E x) _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  show _ = Eh L h (kE E) E G
  rw [Eh_congr' hG.decomp, Eh_sum]
  exact Finset.sum_congr rfl fun x _ => (Eh_const_mul _ _ _ _).symm

/-- **Integrals of cylinder functions** against `ν`, computed at any high enough level. -/
theorem integral_nu' {E W : Finset ℤ} (hEW : E ⊆ W) {ℓ : ℕ} (hℓ : kE W ≤ ℓ) {G : Config → ℝ}
    (hG : Dep G E) : ∫ ω, G ω ∂(nu hP hL hLe) = ∫ h, Eh L h ℓ W G ∂P := by
  rw [integral_nu hP hL hLe hG]
  refine integral_congr_ae ?_
  filter_upwards [hP.good] with h hg
  exact (Eh_eq_kE hL hLe hg hEW hℓ hG).symm

end Nu

end FiniteOrderMixing
