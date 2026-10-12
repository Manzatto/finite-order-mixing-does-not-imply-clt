import FiniteOrderMixing.Cited.HLProcess

/-!
# A stationary finitely dependent colouring proper at range `m`

From independent copies of the Holroyd–Liggett four-colouring `ν4` we build, for every `m ≥ 1`,
a stationary colouring `V` of `ℤ` that is proper at range `m` (`V i ≠ V j` for `0 < |i - j| ≤ m`)
and `2m`-dependent.  For each dilation `k = d + 1 ≤ m` and residue `r < k`, a copy `ω ⟨d, r⟩`
is read along the residue class `r mod k`:

`V i = (ω ⟨d, i mod (d+1)⟩ (i div (d+1)))_{d < m}`.

Colours at distance `k` share the residue class `mod k` and are consecutive in it, so they differ.
The shift of `V` is `V` of a measure-preserving rearrangement of the copies (the residues rotate,
and the copy of the last residue is shifted), which gives stationarity.
-/

open MeasureTheory ProbabilityTheory Finset

namespace FiniteOrderMixing.HL

variable (m : ℕ)

/-- One copy for every dilation `d + 1 ≤ m` and every residue `r < d + 1`. -/
abbrev Idx := Σ d : Fin m, Fin (d.1 + 1)

/-- The residue of `i` modulo `d + 1`. -/
def res (d : ℕ) (i : ℤ) : Fin (d + 1) :=
  ⟨(i % ((d + 1 : ℕ) : ℤ)).toNat, by
    have h1 := Int.emod_nonneg i (show ((d + 1 : ℕ) : ℤ) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos i (show (0 : ℤ) < ((d + 1 : ℕ) : ℤ) by omega)
    omega⟩

lemma res_val (d : ℕ) (i : ℤ) : ((res d i : ℕ) : ℤ) = i % ((d + 1 : ℕ) : ℤ) := by
  have h1 := Int.emod_nonneg i (show ((d + 1 : ℕ) : ℤ) ≠ 0 by omega)
  exact Int.toNat_of_nonneg h1

lemma res_spec (d : ℕ) (i : ℤ) : ((d + 1 : ℕ) : ℤ) * (i / ((d + 1 : ℕ) : ℤ)) + (res d i : ℕ) = i := by
  rw [res_val]; exact Int.mul_ediv_add_emod i _

lemma res_bound (d : ℕ) (i : ℤ) : 0 ≤ ((res d i : ℕ) : ℤ) ∧ ((res d i : ℕ) : ℤ) < d + 1 := by
  have := (res d i).2; constructor <;> omega

/-- Moving one step to the right. -/
lemma res_succ (d : ℕ) (i : ℤ) :
    res d (i + 1) = finRotate (d + 1) (res d i) ∧
      (i + 1) / ((d + 1 : ℕ) : ℤ) = i / ((d + 1 : ℕ) : ℤ) + if res d i = Fin.last d then 1 else 0 := by
  have hs := res_spec d (i)
  have hb := res_bound d i
  have hk : (0 : ℤ) < ((d + 1 : ℕ) : ℤ) := by omega
  by_cases h : res d i = Fin.last d
  · have hr : ((res d i : ℕ) : ℤ) = d := by rw [h]; simp
    have hu := (Int.ediv_emod_unique (a := i + 1) (r := 0) (q := i / ((d + 1 : ℕ) : ℤ) + 1) hk).2
      ⟨by push_cast at hs ⊢; nlinarith, le_rfl, hk⟩
    refine ⟨?_, by rw [ite_eq_left h]; exact hu.1⟩
    rw [h, finRotate_last]
    ext
    have := res_val d (i + 1)
    rw [hu.2] at this
    simp only [Fin.val_zero]; omega
  · have hlt : (res d i : ℕ) < d := by
      have := (res d i).2
      have : (res d i : ℕ) ≠ d := fun e => h (Fin.ext (by simp [e]))
      omega
    have hu := (Int.ediv_emod_unique (a := i + 1) (r := ((res d i : ℕ) : ℤ) + 1)
      (q := i / ((d + 1 : ℕ) : ℤ)) hk).2 ⟨by linarith, by omega, by push_cast; omega⟩
    refine ⟨?_, by rw [ite_eq_right h, add_zero]; exact hu.1⟩
    ext
    rw [coe_finRotate_of_ne_last h]
    have := res_val d (i + 1)
    rw [hu.2] at this
    omega

/-- Moving `d + 1` steps to the right. -/
lemma res_add (d : ℕ) (i : ℤ) :
    res d (i + ((d + 1 : ℕ) : ℤ)) = res d i ∧
      (i + ((d + 1 : ℕ) : ℤ)) / ((d + 1 : ℕ) : ℤ) = i / ((d + 1 : ℕ) : ℤ) + 1 := by
  have hs := res_spec d i
  have hb := res_bound d i
  have hk : (0 : ℤ) < ((d + 1 : ℕ) : ℤ) := by omega
  have hu := (Int.ediv_emod_unique (a := i + ((d + 1 : ℕ) : ℤ)) (r := ((res d i : ℕ) : ℤ))
    (q := i / ((d + 1 : ℕ) : ℤ) + 1) hk).2 ⟨by linarith, hb.1, hb.2⟩
  refine ⟨?_, hu.1⟩
  ext
  have := res_val d (i + ((d + 1 : ℕ) : ℤ))
  rw [hu.2] at this
  omega

/-- The colour of `i`, as a function of the copies. -/
def Φ (ω : Idx m → ℤ → Fin 4) (i : ℤ) : Fin m → Fin 4 :=
  fun d => ω ⟨d, res d i⟩ (i / ((d.1 + 1 : ℕ) : ℤ))

/-- Coding the colours by `Fin q`. -/
noncomputable def enc : (Fin m → Fin 4) ≃ Fin (Fintype.card (Fin m → Fin 4)) :=
  Fintype.equivFin _

/-- The colouring. -/
noncomputable def Vm (ω : Idx m → ℤ → Fin 4) : ℤ → Fin (Fintype.card (Fin m → Fin 4)) :=
  fun i => enc m (Φ m ω i)

/-- The law of the copies. -/
noncomputable def Ωm : Measure (Idx m → ℤ → Fin 4) := Measure.pi fun _ => ν4

instance : IsProbabilityMeasure (Ωm m) := by unfold Ωm; infer_instance

/-- The law of the colouring. -/
noncomputable def PVm : Measure (ℤ → Fin (Fintype.card (Fin m → Fin 4))) := (Ωm m).map (Vm m)

lemma measurable_Vm : Measurable (Vm m) :=
  measurable_pi_iff.mpr fun _ => (measurable_of_countable (enc m)).comp
    (measurable_pi_iff.mpr fun _ => (measurable_pi_apply _).comp (measurable_pi_apply _))

instance : IsProbabilityMeasure (PVm m) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_Vm m).aemeasurable).2 inferInstance

/-! ## Stationarity -/

/-- The rotation of the residues. -/
def rot : Idx m ≃ Idx m := Equiv.sigmaCongrRight fun d => finRotate (d.1 + 1)

/-- The copy of the last residue is shifted. -/
def gsh (c : Idx m) : (ℤ → Fin 4) → (ℤ → Fin 4) := if c.2 = Fin.last c.1 then sh else id

/-- The rearrangement of the copies realising the shift. -/
def T (ω : Idx m → ℤ → Fin 4) : Idx m → ℤ → Fin 4 := fun c => gsh m c (ω (rot m c))

lemma measurable_gsh (c : Idx m) : Measurable (gsh m c) := by
  unfold gsh; split_ifs
  · exact measurable_sh
  · exact measurable_id

lemma gsh_preimage (c : Idx m) {S : Set (ℤ → Fin 4)} (hS : MeasurableSet S) :
    ν4 (gsh m c ⁻¹' S) = ν4 S := by
  unfold gsh; split_ifs
  · exact ν4_stationary.measure_preimage hS.nullMeasurableSet
  · rfl

lemma Vm_T (ω : Idx m → ℤ → Fin 4) : Vm m (T m ω) = fun i => Vm m ω (i + 1) := by
  funext i
  simp only [Vm]
  congr 1
  funext d
  obtain ⟨hr, hq⟩ := res_succ d.1 i
  simp only [Φ, T, rot, Equiv.sigmaCongrRight_apply, gsh]
  rw [hr, hq]
  split_ifs with h
  · simp [sh]
  · simp

lemma T_mp : MeasurePreserving (T m) (Ωm m) (Ωm m) := by
  have hT : Measurable (T m) := measurable_pi_iff.mpr fun c =>
    (measurable_gsh m c).comp (measurable_pi_apply _)
  refine ⟨hT, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hT (MeasurableSet.univ_pi hs)]
  have hpre : T m ⁻¹' Set.univ.pi s =
      Set.univ.pi fun c => gsh m ((rot m).symm c) ⁻¹' s ((rot m).symm c) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ_pi, T]
    constructor
    · intro h c
      have := h ((rot m).symm c)
      simpa using this
    · intro h c
      have := h (rot m c)
      simpa using this
  rw [hpre, Ωm, Measure.pi_pi]
  rw [Finset.prod_congr rfl fun c _ => gsh_preimage m _ (hs _)]
  exact Equiv.prod_comp (rot m).symm fun c => ν4 (s c)

theorem PVm_stationary :
    MeasurePreserving (fun V : ℤ → Fin (Fintype.card (Fin m → Fin 4)) => fun j => V (j + 1))
      (PVm m) (PVm m) := by
  have hs : Measurable fun V : ℤ → Fin (Fintype.card (Fin m → Fin 4)) => fun j => V (j + 1) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  refine ⟨hs, ?_⟩
  have hc : (fun V : ℤ → Fin (Fintype.card (Fin m → Fin 4)) => fun j => V (j + 1)) ∘ Vm m =
      Vm m ∘ T m := funext fun ω => (Vm_T m ω).symm
  rw [PVm, Measure.map_map hs (measurable_Vm m), hc,
    ← Measure.map_map (measurable_Vm m) (T_mp m).measurable, (T_mp m).map_eq]

/-! ## Properness -/

theorem PVm_proper : ∀ᵐ V ∂(PVm m), ∀ i j : ℤ, 0 < |i - j| → |i - j| ≤ m → V i ≠ V j := by
  have hmeas : MeasurableSet {V : ℤ → Fin (Fintype.card (Fin m → Fin 4)) |
      ∀ i j : ℤ, 0 < |i - j| → |i - j| ≤ m → V i ≠ V j} := by
    rw [measurableSet_setOfPred]
    refine Measurable.forall fun i => Measurable.forall fun j => measurable_const.imp
      (measurable_const.imp ?_)
    exact measurableSet_setOfPred.1
      (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl
  rw [PVm, ae_map_iff (measurable_Vm m).aemeasurable hmeas]
  have hcopy : ∀ᵐ ω ∂(Ωm m), ∀ c : Idx m, ∀ k : ℤ, ω c k ≠ ω c (k + 1) := by
    refine ae_all_iff.2 fun c => ?_
    have hmp := measurePreserving_eval (fun _ : Idx m => ν4) c
    exact ae_of_ae_map hmp.measurable.aemeasurable (hmp.map_eq.symm ▸ ν4_proper)
  filter_upwards [hcopy] with ω hω
  -- colours at distance `δ ≤ m` differ in the component of dilation `δ`
  have key : ∀ i : ℤ, ∀ δ : ℕ, 1 ≤ δ → δ ≤ m → Vm m ω i ≠ Vm m ω (i + δ) := by
    intro i δ hδ hδm hEq
    have hd : δ - 1 < m := by omega
    set d : Fin m := ⟨δ - 1, hd⟩
    have hδ' : ((d.1 + 1 : ℕ) : ℤ) = δ := by simp [d]; omega
    have hΦ : Φ m ω i = Φ m ω (i + δ) := (enc m).injective hEq
    have := congrFun hΦ d
    simp only [Φ] at this
    obtain ⟨hr, hq⟩ := res_add d.1 i
    rw [← hδ'] at this
    rw [hr, hq] at this
    exact hω _ _ this
  intro i j hpos hle hEq
  rcases lt_or_gt_of_ne (show i ≠ j by intro h; subst h; simp at hpos) with h | h
  · have := key i (j - i).toNat (by omega) (by rw [abs_sub_comm, abs_of_pos (by omega)] at hle; omega)
    rw [show i + ((j - i).toNat : ℤ) = j by omega] at this
    exact this hEq
  · have := key j (i - j).toNat (by omega) (by rw [abs_of_pos (by omega)] at hle; omega)
    rw [show j + ((i - j).toNat : ℤ) = i by omega] at this
    exact this hEq.symm

/-! ## Finite dependence -/

variable {m}

/-- The colourings agreeing with `τ` on `S`. -/
def cylV {q : ℕ} (S : Finset ℤ) (τ : ℤ → Fin q) : Set (ℤ → Fin q) := {V | ∀ i ∈ S, V i = τ i}

lemma measurableSet_cylV {q : ℕ} (S : Finset ℤ) (τ : ℤ → Fin q) : MeasurableSet (cylV S τ) := by
  have : cylV S τ = ⋂ i ∈ S, (fun V : ℤ → Fin q => V i) ⁻¹' {τ i} := by
    ext V; simp [cylV]
  rw [this]
  exact MeasurableSet.biInter S.countable_toSet fun i _ =>
    measurable_pi_apply i (measurableSet_singleton _)

/-- The indices of copy `c` read by the points of `S`. -/
def Sc (S : Finset ℤ) (c : Idx m) : Finset ℤ :=
  (S.filter fun i => res c.1 i = c.2).image fun i => i / ((c.1.1 + 1 : ℕ) : ℤ)

/-- The pattern that copy `c` must follow. -/
noncomputable def σc (τ : ℤ → Fin (Fintype.card (Fin m → Fin 4))) (c : Idx m) : ℤ → Fin 4 :=
  fun k => (enc m).symm (τ (((c.1.1 + 1 : ℕ) : ℤ) * k + (c.2 : ℕ))) c.1

lemma mem_Sc {S : Finset ℤ} {c : Idx m} {k : ℤ} (hk : k ∈ Sc S c) :
    ((c.1.1 + 1 : ℕ) : ℤ) * k + (c.2 : ℕ) ∈ S := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hk
  obtain ⟨hiS, hr⟩ := Finset.mem_filter.1 hi
  rw [← hr, res_spec]; exact hiS

lemma preimage_cylV (S : Finset ℤ) (τ : ℤ → Fin (Fintype.card (Fin m → Fin 4))) :
    Vm m ⁻¹' cylV S τ = Set.univ.pi fun c => cyl (Sc S c) (σc τ c) := by
  ext ω
  simp only [Set.mem_preimage, cylV, Set.mem_univ_pi, cyl, Set.mem_ofPred_eq]
  constructor
  · rintro h ⟨d, r⟩ k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hk
    obtain ⟨hiS, hr⟩ := Finset.mem_filter.1 hi
    simp only at hr
    subst hr
    have := congrArg (fun x => (enc m).symm x d) (h i hiS)
    simp only [Vm, Equiv.symm_apply_apply, Φ] at this
    simp only [σc]
    rw [res_spec, ← this]
  · intro h i hi
    simp only [Vm]
    rw [← Equiv.eq_symm_apply]
    funext d
    have hk : i / ((d.1 + 1 : ℕ) : ℤ) ∈ Sc S ⟨d, res d i⟩ :=
      Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, rfl⟩, rfl⟩
    have := h ⟨d, res d i⟩ _ hk
    simp only [σc, res_spec] at this
    exact this

lemma PVm_cylV (S : Finset ℤ) (τ : ℤ → Fin (Fintype.card (Fin m → Fin 4))) :
    PVm m (cylV S τ) = ∏ c, ν4 (cyl (Sc S c) (σc τ c)) := by
  rw [PVm, Measure.map_apply (measurable_Vm m) (measurableSet_cylV S τ), preimage_cylV, Ωm,
    Measure.pi_pi]

/-- **Finite dependence**: windows separated by more than `2m` are independent. -/
theorem PVm_indep (I J : Finset ℤ) (hsep : ∀ i ∈ I, ∀ j ∈ J, ((2 * m : ℕ) : ℤ) < |i - j|) :
    IndepFun (fun V : ℤ → Fin (Fintype.card (Fin m → Fin 4)) => fun i : I => V i)
      (fun V => fun j : J => V j) (PVm m) := by
  classical
  set q := Fintype.card (Fin m → Fin 4)
  have hX : ∀ K : Finset ℤ, Measurable fun V : ℤ → Fin q => fun i : K => V i :=
    fun K => measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  rw [indepFun_iff_map_prod_eq_prod_map_map (hX I).aemeasurable (hX J).aemeasurable]
  refine Measure.ext_of_singleton fun ⟨x, y⟩ => ?_
  set z : Fin q := enc m fun _ => 0
  set α' : ℤ → Fin q := fun i => if h : i ∈ I then x ⟨i, h⟩ else z
  set β' : ℤ → Fin q := fun j => if h : j ∈ J then y ⟨j, h⟩ else z
  set τ : ℤ → Fin q := fun i => if i ∈ I then α' i else β' i
  have hIJ : ∀ i ∈ I, i ∉ J := fun i hi hj => by have := hsep i hi i hj; simp at this; omega
  have hx : (fun V : ℤ → Fin q => fun i : I => V i) ⁻¹' {x} = cylV I α' := by
    ext V
    simp only [Set.mem_preimage, Set.mem_singleton_iff, cylV, Set.mem_ofPred_eq]
    constructor
    · rintro rfl i hi; simp [α', hi]
    · intro h; funext i; rw [h i i.2]; simp [α']
  have hy : (fun V : ℤ → Fin q => fun j : J => V j) ⁻¹' {y} = cylV J β' := by
    ext V
    simp only [Set.mem_preimage, Set.mem_singleton_iff, cylV, Set.mem_ofPred_eq]
    constructor
    · rintro rfl j hj; simp [β', hj]
    · intro h; funext j; rw [h j j.2]; simp [β']
  have hxy : (fun V : ℤ → Fin q => ((fun i : I => V i), fun j : J => V j)) ⁻¹' {(x, y)} =
      cylV (I ∪ J) τ := by
    rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod, hx, hy]
    ext V
    simp only [Set.mem_inter_iff, cylV, Set.mem_ofPred_eq, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · rw [h1 i hi]; simp [τ, hi]
      · rw [h2 i hi]; simp [τ, show i ∉ I from fun h => hIJ i h hi]
    · intro h
      refine ⟨fun i hi => by rw [h i (Or.inl hi)]; simp [τ, hi], fun j hj => ?_⟩
      rw [h j (Or.inr hj)]; simp [τ, show j ∉ I from fun h => hIJ j h hj]
  rw [Measure.map_apply ((hX I).prodMk (hX J)) (measurableSet_singleton _), hxy,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.map_apply (hX I) (measurableSet_singleton _),
    Measure.map_apply (hX J) (measurableSet_singleton _), hx, hy,
    PVm_cylV, PVm_cylV, PVm_cylV, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  obtain ⟨d, r⟩ := c
  have hunion : Sc (I ∪ J) ⟨d, r⟩ = Sc I ⟨d, r⟩ ∪ Sc J ⟨d, r⟩ := by
    simp only [Sc, Finset.filter_union, Finset.image_union]
  -- the two index sets are at distance at least two
  have hsep' : ∀ k ∈ Sc I ⟨d, r⟩, ∀ k' ∈ Sc J ⟨d, r⟩, 1 < |k - k'| := by
    intro k hk k' hk'
    have h := hsep _ (mem_Sc hk) _ (mem_Sc hk')
    simp only at h
    have hK : (0 : ℤ) < ((d.1 + 1 : ℕ) : ℤ) := by omega
    have hKm : ((d.1 + 1 : ℕ) : ℤ) ≤ m := by have := d.2; omega
    rw [show ((d.1 + 1 : ℕ) : ℤ) * k + (r : ℕ) - (((d.1 + 1 : ℕ) : ℤ) * k' + (r : ℕ)) =
      ((d.1 + 1 : ℕ) : ℤ) * (k - k') by ring, abs_mul, abs_of_pos hK] at h
    by_contra hc
    push Not at hc
    have : ((d.1 + 1 : ℕ) : ℤ) * |k - k'| ≤ ((d.1 + 1 : ℕ) : ℤ) * 1 :=
      mul_le_mul_of_nonneg_left hc hK.le
    push_cast at h this hKm
    omega
  have hcI : cyl (Sc I ⟨d, r⟩) (σc τ ⟨d, r⟩) = cyl (Sc I ⟨d, r⟩) (σc α' ⟨d, r⟩) := by
    ext ω
    simp only [cyl, Set.mem_ofPred_eq]
    refine forall₂_congr fun k hk => ?_
    simp only [σc, τ, ite_eq_left (mem_Sc hk)]
  have hcJ : cyl (Sc J ⟨d, r⟩) (σc τ ⟨d, r⟩) = cyl (Sc J ⟨d, r⟩) (σc β' ⟨d, r⟩) := by
    ext ω
    simp only [cyl, Set.mem_ofPred_eq]
    refine forall₂_congr fun k hk => ?_
    simp only [σc, τ, ite_eq_right (fun h => hIJ _ h (mem_Sc hk))]
  rw [hunion, ν4_indep_cyl _ _ _ _ rfl hsep', hcI, hcJ]

/-! ## The colouring theorem -/

/-- **[Holroyd–Liggett]** For every `m ≥ 1` there is a stationary, `2m`-dependent colouring of `ℤ`
with `q ≥ 4` colours whose colours at distance at most `m` differ almost surely. -/
theorem holroyd_liggett_colouring (hm : 1 ≤ m) :
    ∃ (q : ℕ) (P : Measure (ℤ → Fin q)), 4 ≤ q ∧ IsProbabilityMeasure P ∧
      MeasurePreserving (fun V : ℤ → Fin q => fun j => V (j + 1)) P P ∧
      (∀ I J : Finset ℤ, (∀ i ∈ I, ∀ j ∈ J, ((2 * m : ℕ) : ℤ) < |i - j|) →
        IndepFun (fun V : ℤ → Fin q => fun i : I => V i) (fun V => fun j : J => V j) P) ∧
      (∀ᵐ V ∂P, ∀ i j : ℤ, 0 < |i - j| → |i - j| ≤ m → V i ≠ V j) := by
  refine ⟨Fintype.card (Fin m → Fin 4), PVm m, ?_, inferInstance, PVm_stationary m,
    fun I J h => PVm_indep I J h, PVm_proper m⟩
  simp only [Fintype.card_fun, Fintype.card_fin]
  calc 4 = 4 ^ 1 := by norm_num
    _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm

end FiniteOrderMixing.HL
