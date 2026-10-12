import FiniteOrderMixing.Stationarity
import FiniteOrderMixing.Mixing

/-!
# Finite dependence of the nested marker sets (Proposition `prop:hierarchy-dependence`)

For windows `I`, `J` separated by more than `4q(4L)^{k}`, the marker configurations through level
`k` on `I` and on `J` are independent.

The proof is by induction on `k`.  Given the levels `≤ k`, the level-`(k+1)` markers on `I` are
determined by the old markers on a window `I'` around `I` and by the colours of the old markers in
`I'`, which are read from the fresh colouring `ω (k+1)` at an interval of indices; the index
intervals of `I` and `J` are more than `4L` apart, so the colours are independent (`(4L)`-dependence
of the colouring).  Integrating out the fresh colouring, stationarity shows that the result depends
on the old markers on `I'` only (the absolute position of the index interval is irrelevant), and
the induction hypothesis applies.
-/

open MeasureTheory ProbabilityTheory Finset

namespace FiniteOrderMixing

variable {L q : ℕ}

/-- A function of finitely many marker indicators and colours is measurable. -/
lemma measurable_of_window_H {β : Type*} [MeasurableSpace β] (hq : 1 ≤ q)
    {f : Hspace × (ℤ → Fin q) → β} (K : ℕ) (W : Finset ℤ)
    (hf : ∀ y y' : Hspace, ∀ v v' : ℤ → Fin q, (∀ k ≤ K, ∀ j ∈ W, y k j = y' k j) →
      (∀ j ∈ W, v j = v' j) → f (y, v) = f (y', v')) : Measurable f := by
  classical
  let S := Finset.range (K + 1) ×ˢ W
  let r : Hspace × (ℤ → Fin q) → (S → Bool) × (W → Fin q) :=
    fun p => (fun s => p.1 s.1.1 s.1.2, fun j => p.2 j)
  let ext : (S → Bool) × (W → Fin q) → Hspace × (ℤ → Fin q) := fun x =>
    (fun k j => if h : (k, j) ∈ S then x.1 ⟨_, h⟩ else false,
      fun j => if h : j ∈ W then x.2 ⟨j, h⟩ else ⟨0, hq⟩)
  have hr : Measurable r := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.mpr fun s => measurable_fst.eval.eval
    · exact measurable_pi_iff.mpr fun j => (measurable_pi_apply _).comp measurable_snd
  have hfe : f = (f ∘ ext) ∘ r := by
    funext p
    obtain ⟨y, v⟩ := p
    refine hf _ _ _ _ (fun k hk j hj => ?_) (fun j hj => ?_)
    · have : (k, j) ∈ S := Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), hj⟩
      simp [r, this]
    · simp [r, hj]
  rw [hfe]; exact (measurable_of_countable _).comp hr

/-- A function of finitely many colours factors through the restriction. -/
lemma factor_restr (hq : 1 ≤ q) {f : (ℤ → Fin q) → ℝ} (S : Finset ℤ)
    (hf : ∀ v v', (∀ j ∈ S, v j = v' j) → f v = f v') :
    ∃ φ : (S → Fin q) → ℝ, f = φ ∘ fun v (j : S) => v j := by
  classical
  exact ⟨fun x => f fun j => if h : j ∈ S then x ⟨j, h⟩ else ⟨0, hq⟩,
    funext fun v => hf _ _ fun j hj => by simp [hj]⟩

variable (L) in
/-- The marker sets truncated at level `k`. -/
def Yk (k : ℕ) (ω : ℕ → ℤ → Fin q) : Hspace :=
  fun k' => if k' ≤ k then mk L ω k' else fun _ => false

variable (L) in
/-- The level-`(k+1)` configuration on `I` in terms of the levels `≤ k` and the fresh colouring. -/
def PhiI (k : ℕ) (I : Finset ℤ) (y : Hspace) (v : ℤ → Fin q) :
    (Finset.range (k + 1 + 1) ×ˢ I) → Bool :=
  fun p => if p.1.1 ≤ k then y p.1.1 p.1.2 else sel (y k) v (sc L (k + 1)) p.1.2

lemma rI_succ (k : ℕ) (I : Finset ℤ) (ω : ℕ → ℤ → Fin q) :
    rI (k + 1) I (Mh L ω) = PhiI L k I (Yk L k ω) (ω (k + 1)) := by
  funext p
  have hp := (Finset.mem_product.1 p.2).1
  rw [Finset.mem_range] at hp
  by_cases h : p.1.1 ≤ k
  · simp [rI, PhiI, Yk, Mh, h]
  · have : p.1.1 = k + 1 := by omega
    simp only [rI, PhiI, h, ite_false, Mh, Yk, le_refl, ite_true]
    rw [this]; rfl

lemma measurable_Yk (hq : 1 ≤ q) (k : ℕ) : Measurable (Yk (q := q) L k) :=
  measurable_pi_iff.mpr fun k' => by
    by_cases h : k' ≤ k
    · simp only [Yk, h, ite_true]; exact measurable_mk L hq k'
    · simp only [Yk, h, ite_false]; exact measurable_const

/-- The window of coordinates on which `PhiI` depends. -/
lemma PhiI_local (k : ℕ) (I : Finset ℤ) {y y' : Hspace} {v v' : ℤ → Fin q}
    (hy : ∀ k' ≤ k, ∀ j : ℤ, |j| ≤ (((I.sum fun t => t.natAbs) + q * sc L (k + 1) : ℕ) : ℤ) →
      y k' j = y' k' j)
    (hv : ∀ j : ℤ, |j| ≤ (((I.sum fun t => t.natAbs) + q * sc L (k + 1) : ℕ) : ℤ) → v j = v' j) :
    PhiI L k I y v = PhiI L k I y' v' := by
  set B : ℤ := (((I.sum fun t => t.natAbs) + q * sc L (k + 1) : ℕ) : ℤ) with hBdef
  have htI : ∀ t ∈ I, |t| ≤ (I.sum fun t => t.natAbs) := fun t ht => by
    have := Finset.single_le_sum (f := fun t : ℤ => t.natAbs) (fun _ _ => Nat.zero_le _) ht
    rw [Int.abs_eq_natAbs]; exact_mod_cast this
  have hB : ∀ u ∈ thicken I (q * sc L (k + 1)), |u| ≤ B := fun u hu => by
    obtain ⟨i, hi, hui⟩ := mem_thicken.1 hu
    have := htI i hi
    have h1 := abs_sub_abs_le_abs_sub u i
    rw [hBdef]; push_cast at hui this ⊢; linarith
  funext p
  have hpI : |p.1.2| ≤ B := by
    have h1 := htI _ (Finset.mem_product.1 p.2).2
    rw [hBdef]; have h2 : (0 : ℤ) ≤ q * sc L (k + 1) := by positivity
    push_cast at h1 ⊢; linarith
  simp only [PhiI]
  split_ifs with h
  · exact hy _ h _ hpI
  · refine sel_local (I := I) (fun u hu => hy k le_rfl u (hB u hu)) (fun u hu _ => ?_) _
      (Finset.mem_product.1 p.2).2
    have hidx : idx (y k) u = idx (y' k) u := idx_congr fun x hx =>
      hy k le_rfl x (hx.trans (hB u hu))
    simp only [col]
    rw [hidx, hv _ ((abs_idx_le _ u).trans (hB u hu))]

lemma measurable_PhiI (hq : 1 ≤ q) (k : ℕ) (I : Finset ℤ) :
    Measurable fun p : Hspace × (ℤ → Fin q) => PhiI L k I p.1 p.2 := by
  set B : ℕ := (I.sum fun t => t.natAbs) + q * sc L (k + 1)
  refine measurable_of_window_H hq k (Finset.Icc (-(B : ℤ)) B)
    fun y y' v v' hy hv => PhiI_local k I (fun k' hk' j hj => hy k' hk' j ?_) (fun j hj => hv j ?_)
  · exact Finset.mem_Icc.2 (abs_le.1 hj)
  · exact Finset.mem_Icc.2 (abs_le.1 hj)

lemma abs_le_sum_fintype {α : Type*} [Fintype α] (f : α → ℝ) (x : α) :
    |f x| ≤ ∑ z, |f z| :=
  Finset.single_le_sum (f := fun z => |f z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ x)

lemma rI_Yk (k : ℕ) (I : Finset ℤ) (ω : ℕ → ℤ → Fin q) :
    rI k I (Yk L k ω) = rI k I (Mh L ω) := by
  funext p
  have hp := (Finset.mem_product.1 p.2).1
  rw [Finset.mem_range] at hp
  simp [rI, Yk, Mh, show p.1.1 ≤ k by omega]

section Core

variable {PV : Measure (ℤ → Fin q)} [IsProbabilityMeasure PV] (hC : ColouringLaw L q PV)
  (hq : 1 ≤ q)
include hC hq

omit hC in
lemma map_Yk_pair (k : ℕ) :
    (POmega PV).map (fun ω => (Yk L k ω, ω (k + 1))) = ((POmega PV).map (Yk L k)).prod PV := by
  classical
  set R : (ℕ → ℤ → Fin q) → (Finset.range (k + 1) → ℤ → Fin q) := fun ω i => ω i
  have hR : Measurable R := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  set ext : (Finset.range (k + 1) → ℤ → Fin q) → (ℕ → ℤ → Fin q) :=
    fun x j => if h : j < k + 1 then x ⟨j, Finset.mem_range.2 h⟩ else fun _ => ⟨0, hq⟩
  have hext : Measurable ext := measurable_pi_iff.mpr fun j => by
    by_cases h : j < k + 1
    · simp only [ext, h, dite_true]; exact measurable_pi_apply _
    · simp only [ext, h, dite_false]; exact measurable_const
  have hY : ∀ ω, Yk L k ω = Yk L k (ext (R ω)) := fun ω => by
    funext k'
    simp only [Yk]
    split_ifs with h
    · exact mk_congr L k' fun j hj => by simp [ext, R]; intro; omega
    · rfl
  have hcomp : (fun ω => (Yk L k ω, ω (k + 1))) =
      Prod.map (Yk L k ∘ ext) id ∘ fun ω => (R ω, ω (k + 1)) := by
    funext ω; simp [hY ω]
  rw [hcomp, ← Measure.map_map ((measurable_Yk hq k).comp hext |>.prodMap measurable_id)
    (hR.prodMk (measurable_pi_apply _)), map_pair_eq_prod (k + 1),
    ← Measure.map_prod_map _ _ ((measurable_Yk hq k).comp hext) measurable_id, Measure.map_id,
    Measure.map_map ((measurable_Yk hq k).comp hext) hR]
  congr 2
  funext ω; exact (hY ω).symm

omit hC in
/-- Integrating out the fresh colouring of level `k+1`. -/
lemma integral_level (k : ℕ) {K : Hspace × (ℤ → Fin q) → ℝ} (hK : Measurable K) {C : ℝ}
    (hKb : ∀ p, |K p| ≤ C) :
    ∫ ω, K (Yk L k ω, ω (k + 1)) ∂(POmega PV) =
      ∫ ω, (∫ v, K (Yk L k ω, v) ∂PV) ∂(POmega PV) := by
  have hpair : Measurable fun ω : ℕ → ℤ → Fin q => (Yk L k ω, ω (k + 1)) :=
    (measurable_Yk hq k).prodMk (measurable_pi_apply _)
  have hint : Integrable K (((POmega PV).map (Yk L k)).prod PV) :=
    Integrable.of_bound hK.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hKb p)
  calc ∫ ω, K (Yk L k ω, ω (k + 1)) ∂(POmega PV)
      = ∫ p, K p ∂((POmega PV).map fun ω => (Yk L k ω, ω (k + 1))) :=
        (integral_map hpair.aemeasurable hK.aestronglyMeasurable).symm
    _ = ∫ p, K p ∂(((POmega PV).map (Yk L k)).prod PV) := by rw [map_Yk_pair hq k]
    _ = ∫ y, ∫ v, K (y, v) ∂PV ∂((POmega PV).map (Yk L k)) := integral_prod K hint
    _ = _ := integral_map (measurable_Yk hq k).aemeasurable
        hint.integral_prod_left.aestronglyMeasurable

omit hq in
/-- The marker sets are almost surely good. -/
lemma ae_good (hL : 1 ≤ L) : ∀ᵐ ω ∂(POmega PV), Good L (Mh L ω) := by
  have h : ∀ k, ∀ᵐ ω ∂(POmega PV), Proper L (ω (k + 1)) := fun k => by
    have hmap : (POmega PV).map (fun ω => ω (k + 1)) = PV :=
      Measure.infinitePi_map_eval (fun _ => PV) (k + 1)
    exact ae_of_ae_map (measurable_pi_apply (k + 1)).aemeasurable (hmap.symm ▸ hC.proper)
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact good_Mh hL hω

omit [IsProbabilityMeasure PV] in
/-- Stationarity makes the integrated fresh colouring a local function of the old levels. -/
lemma integral_PhiI_local {k : ℕ} {I : Finset ℤ} {a b : ℤ}
    (hIab : thicken I (q * sc L (k + 1)) ⊆ Finset.Icc a b)
    (f : (Finset.range (k + 1 + 1) ×ˢ I → Bool) → ℝ) {y y' : Hspace}
    (hA : AgreeOn k (Finset.Icc a b) y y') :
    ∫ v, f (PhiI L k I y v) ∂PV = ∫ v, f (PhiI L k I y' v) ∂PV := by
  set δ := idx (y k) (a - 1) - idx (y' k) (a - 1)
  have hidx : ∀ u ∈ Finset.Icc a b, idx (y k) u = idx (y' k) u + δ := by
    intro u hu
    simp only [Finset.mem_Icc] at hu
    have h1 := idx_sub (y k) (show a - 1 ≤ u by omega)
    have h2 := idx_sub (y' k) (show a - 1 ≤ u by omega)
    have h3 : ncount (y k) (a - 1) u = ncount (y' k) (a - 1) u := by
      unfold ncount; congr 1
      exact Finset.filter_congr fun x hx => by
        simp only [Finset.mem_Ioc] at hx
        rw [hA k le_rfl x (Finset.mem_Icc.2 ⟨by omega, by omega⟩)]
    simp only [δ]; omega
  have hIsub : ∀ t ∈ I, t ∈ Finset.Icc a b := fun t ht =>
    hIab (mem_thicken.2 ⟨t, ht, by simp only [sub_self, abs_zero]; positivity⟩)
  have hPhi : ∀ v, PhiI L k I y v = PhiI L k I y' (shiftZ δ v) := fun v => by
    funext p
    simp only [PhiI]
    split_ifs with h
    · exact hA _ h _ (hIsub _ (Finset.mem_product.1 p.2).2)
    · refine sel_local (I := I) (fun u hu => hA k le_rfl u (hIab hu)) (fun u hu _ => ?_) _
        (Finset.mem_product.1 p.2).2
      simp only [col, shiftZ]
      rw [hidx u (hIab hu)]
  have hmeas : Measurable fun w => f (PhiI L k I y' w) :=
    (measurable_of_countable f).comp ((measurable_PhiI hq k I).comp
      (measurable_const.prodMk measurable_id))
  simp_rw [hPhi]
  rw [← integral_map (measurable_shiftZ δ).aemeasurable hmeas.aestronglyMeasurable,
    (shiftZ_mp hC.stat δ).map_eq]

omit [IsProbabilityMeasure PV] in
/-- Given the old levels, windows whose index intervals are separated have independent colours. -/
lemma integral_PhiI_mul {k : ℕ} {I J : Finset ℤ} {aI bI aJ bJ : ℤ} {y : Hspace}
    (hdense : ∀ i : ℤ, ∃ j, i ≤ j ∧ j < i + 3 * sc L k ∧ y k j = true)
    (hIab : thicken I (q * sc L (k + 1)) ⊆ Finset.Icc aI bI)
    (hJab : thicken J (q * sc L (k + 1)) ⊆ Finset.Icc aJ bJ)
    (hgap : bI + (8 * L + 1) * (3 * sc L k) ≤ aJ) (_haJ : aJ ≤ bJ)
    (f : (Finset.range (k + 1 + 1) ×ˢ I → Bool) → ℝ)
    (g : (Finset.range (k + 1 + 1) ×ˢ J → Bool) → ℝ) :
    ∫ v, f (PhiI L k I y v) * g (PhiI L k J y v) ∂PV =
      (∫ v, f (PhiI L k I y v) ∂PV) * ∫ v, g (PhiI L k J y v) ∂PV := by
  set IWI := Finset.Icc (idx (y k) aI) (idx (y k) bI)
  set IWJ := Finset.Icc (idx (y k) aJ) (idx (y k) bJ)
  have hmono : ∀ a b u : ℤ, a ≤ u → u ≤ b → idx (y k) a ≤ idx (y k) u ∧ idx (y k) u ≤ idx (y k) b :=
    fun a b u hau hub => by
      have := idx_sub (y k) hau; have := idx_sub (y k) hub; omega
  have hloc : ∀ (K : Finset ℤ) (a b : ℤ), thicken K (q * sc L (k + 1)) ⊆ Finset.Icc a b →
      ∀ v v' : ℤ → Fin q, (∀ j ∈ Finset.Icc (idx (y k) a) (idx (y k) b), v j = v' j) →
        PhiI L k K y v = PhiI L k K y v' := by
    intro K a b hK v v' hvv'
    funext p
    simp only [PhiI]
    split_ifs with h
    · rfl
    · refine sel_local (I := K) (fun _ _ => rfl) (fun u hu _ => ?_) _ (Finset.mem_product.1 p.2).2
      have hu' := Finset.mem_Icc.1 (hK hu)
      simp only [col]
      rw [hvv' _ (Finset.mem_Icc.2 (hmono a b u hu'.1 hu'.2))]
  obtain ⟨φ, hφ⟩ := factor_restr hq IWI (f := fun v => f (PhiI L k I y v))
    fun v v' h => congrArg f (hloc I aI bI hIab v v' h)
  obtain ⟨ψ, hψ⟩ := factor_restr hq IWJ (f := fun v => g (PhiI L k J y v))
    fun v v' h => congrArg g (hloc J aJ bJ hJab v v' h)
  have hsep : ∀ i ∈ IWI, ∀ j ∈ IWJ, ((8 * L : ℕ) : ℤ) < |i - j| := by
    intro i hi j hj
    simp only [IWI, IWJ, Finset.mem_Icc] at hi hj
    have hn := ncount_ge_of_dense (o := y k) (G := 3 * sc L k) (by
      intro i; obtain ⟨j, h1, h2, h3⟩ := hdense i; exact ⟨j, h1, by push_cast; omega, h3⟩)
      (8 * L + 1) bI aJ (by push_cast at hgap ⊢; linarith)
    have hsub := idx_sub (y k) (show bI ≤ aJ by
      have : (0 : ℤ) ≤ (8 * L + 1) * (3 * sc L k) := by positivity
      linarith)
    rw [abs_sub_comm, abs_of_pos (by omega)]
    push_cast at hn ⊢; omega
  have hr : ∀ S : Finset ℤ, Measurable fun (v : ℤ → Fin q) (j : S) => v j :=
    fun S => measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  have hind := (hC.dep IWI IWJ hsep).comp (measurable_of_countable φ) (measurable_of_countable ψ)
  have e1 : ∀ v, f (PhiI L k I y v) = φ fun j : IWI => v j := fun v => congrFun hφ v
  have e2 : ∀ v, g (PhiI L k J y v) = ψ fun j : IWJ => v j := fun v => congrFun hψ v
  simp only [e1, e2]
  exact hind.integral_fun_mul_eq_mul_integral
    ((measurable_of_countable φ).comp (hr IWI)).aestronglyMeasurable
    ((measurable_of_countable ψ).comp (hr IWJ)).aestronglyMeasurable

/-- **Proposition `prop:hierarchy-dependence`** (integral form). -/
theorem indep_core (hq4 : 4 ≤ q) (hL : 1 ≤ L) : ∀ (k : ℕ) (I J : Finset ℤ),
    (∀ i ∈ I, ∀ j ∈ J, i + 4 * q * sc L k < j) →
    ∀ (f : (Finset.range (k + 1) ×ˢ I → Bool) → ℝ) (g : (Finset.range (k + 1) ×ˢ J → Bool) → ℝ),
    ∫ ω, f (rI k I (Mh L ω)) * g (rI k J (Mh L ω)) ∂(POmega PV) =
      (∫ ω, f (rI k I (Mh L ω)) ∂(POmega PV)) * ∫ ω, g (rI k J (Mh L ω)) ∂(POmega PV) := by
  intro k
  induction k with
  | zero =>
    intro I J _ f g
    have hc : ∀ (K : Finset ℤ) (ω : ℕ → ℤ → Fin q), rI 0 K (Mh L ω) = fun _ => true := fun K ω => by
      funext p
      have hp := (Finset.mem_product.1 p.2).1
      rw [Finset.mem_range] at hp
      simp [rI, Mh, show p.1.1 = 0 by omega, mk]
    simp only [hc, integral_const, probReal_univ, smul_eq_mul, one_mul]
  | succ k ih =>
    intro I J hIJ f g
    classical
    set ω0 : ℕ → ℤ → Fin q := fun _ _ => ⟨0, hq⟩
    -- empty windows are trivial
    rcases I.eq_empty_or_nonempty with hI | hIne
    · subst hI
      have hc : ∀ ω : ℕ → ℤ → Fin q, rI (k + 1) ∅ (Mh L ω) = rI (k + 1) ∅ (Mh L ω0) := fun ω =>
        funext fun p => absurd (Finset.mem_product.1 p.2).2 (by simp)
      simp only [hc, integral_const_mul, integral_const, probReal_univ, smul_eq_mul,
        one_mul]
    rcases J.eq_empty_or_nonempty with hJ | hJne
    · subst hJ
      have hc : ∀ ω : ℕ → ℤ → Fin q, rI (k + 1) ∅ (Mh L ω) = rI (k + 1) ∅ (Mh L ω0) := fun ω =>
        funext fun p => absurd (Finset.mem_product.1 p.2).2 (by simp)
      simp only [hc, integral_mul_const, integral_const, probReal_univ, smul_eq_mul,
        one_mul]
    set N := sc L (k + 1)
    have hsc : N = 4 * L * sc L k := by simp only [N, sc]; ring
    have hsck : 1 ≤ sc L k := Nat.one_le_pow _ _ (by omega)
    set aI := I.min' hIne - q * N
    set bI := I.max' hIne + q * N
    set aJ := J.min' hJne - q * N
    set bJ := J.max' hJne + q * N
    have hmm := hIJ _ (I.max'_mem hIne) _ (J.min'_mem hJne)
    have hthick : ∀ (K : Finset ℤ) (hK : K.Nonempty),
        thicken K (q * N) ⊆ Finset.Icc (K.min' hK - q * N) (K.max' hK + q * N) := by
      intro K hK x hx
      obtain ⟨i, hi, hxi⟩ := mem_thicken.1 hx
      have h1 := K.min'_le i hi
      have h2 := K.le_max' i hi
      rw [abs_le] at hxi
      simp only [Finset.mem_Icc]; push_cast at hxi ⊢; constructor <;> omega
    have hIab := hthick I hIne
    have hJab := hthick J hJne
    have hqN : (q * N : ℤ) = q * (4 * L * sc L k) := by rw [hsc]; push_cast; ring
    have hgap : bI + (8 * L + 1) * (3 * sc L k) ≤ aJ := by
      simp only [bI, aJ]
      rw [hsc] at hmm
      push_cast at hmm ⊢
      have hq' : (4 : ℤ) ≤ q := by exact_mod_cast hq4
      have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
      have hs' : (1 : ℤ) ≤ sc L k := by exact_mod_cast hsck
      nlinarith
    have hsep' : ∀ i ∈ Finset.Icc aI bI, ∀ j ∈ Finset.Icc aJ bJ, i + 4 * q * sc L k < j := by
      intro i hi j hj
      simp only [Finset.mem_Icc] at hi hj
      simp only [bI, aJ] at hi hj
      rw [hsc] at hmm
      push_cast at hmm hi hj ⊢
      have hq' : (4 : ℤ) ≤ q := by exact_mod_cast hq4
      have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
      have hs' : (1 : ℤ) ≤ sc L k := by exact_mod_cast hsck
      nlinarith
    have haJ : aJ ≤ bJ := by
      have := J.min'_le _ (J.max'_mem hJne); simp only [aJ, bJ]
      have : (0 : ℤ) ≤ q * N := by positivity
      linarith
    -- the integrated fresh colouring
    set Fb : Hspace → ℝ := fun y => ∫ v, f (PhiI L k I y v) ∂PV
    set Gb : Hspace → ℝ := fun y => ∫ v, g (PhiI L k J y v) ∂PV
    obtain ⟨f', hf'⟩ := factor_rI (f := Fb) (k := k) (I := Finset.Icc aI bI)
      fun y y' hA => integral_PhiI_local hC hq hIab f hA
    obtain ⟨g', hg'⟩ := factor_rI (f := Gb) (k := k) (I := Finset.Icc aJ bJ)
      fun y y' hA => integral_PhiI_local hC hq hJab g hA
    have hFb : ∀ ω : ℕ → ℤ → Fin q, Fb (Yk L k ω) = f' (rI k (Finset.Icc aI bI) (Mh L ω)) := fun ω => by
      rw [hf']; exact congrArg f' (rI_Yk k _ ω)
    have hGb : ∀ ω : ℕ → ℤ → Fin q, Gb (Yk L k ω) = g' (rI k (Finset.Icc aJ bJ) (Mh L ω)) := fun ω => by
      rw [hg']; exact congrArg g' (rI_Yk k _ ω)
    have hmf : Measurable fun p : Hspace × (ℤ → Fin q) => f (PhiI L k I p.1 p.2) :=
      (measurable_of_countable f).comp (measurable_PhiI hq k I)
    have hmg : Measurable fun p : Hspace × (ℤ → Fin q) => g (PhiI L k J p.1 p.2) :=
      (measurable_of_countable g).comp (measurable_PhiI hq k J)
    have hF : ∫ ω, f (rI (k + 1) I (Mh L ω)) ∂(POmega PV) =
        ∫ ω, f' (rI k (Finset.Icc aI bI) (Mh L ω)) ∂(POmega PV) := by
      simp only [rI_succ]
      rw [integral_level hq k hmf (fun p => abs_le_sum_fintype f _)]
      exact integral_congr_ae (Filter.Eventually.of_forall hFb)
    have hG : ∫ ω, g (rI (k + 1) J (Mh L ω)) ∂(POmega PV) =
        ∫ ω, g' (rI k (Finset.Icc aJ bJ) (Mh L ω)) ∂(POmega PV) := by
      simp only [rI_succ]
      rw [integral_level hq k hmg (fun p => abs_le_sum_fintype g _)]
      exact integral_congr_ae (Filter.Eventually.of_forall hGb)
    have hFG : ∫ ω, f (rI (k + 1) I (Mh L ω)) * g (rI (k + 1) J (Mh L ω)) ∂(POmega PV) =
        ∫ ω, f' (rI k (Finset.Icc aI bI) (Mh L ω)) * g' (rI k (Finset.Icc aJ bJ) (Mh L ω))
          ∂(POmega PV) := by
      simp only [rI_succ]
      have hb : ∀ p : Hspace × (ℤ → Fin q),
          |f (PhiI L k I p.1 p.2) * g (PhiI L k J p.1 p.2)| ≤ (∑ z, |f z|) * ∑ z, |g z| := by
        intro p
        rw [abs_mul]
        exact mul_le_mul (abs_le_sum_fintype f _) (abs_le_sum_fintype g _) (abs_nonneg _)
          (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      rw [integral_level hq k
        (K := fun p => f (PhiI L k I p.1 p.2) * g (PhiI L k J p.1 p.2)) (hmf.mul hmg) hb]
      refine integral_congr_ae ?_
      filter_upwards [ae_good hC hL] with ω hg
      rw [← hFb, ← hGb]
      exact integral_PhiI_mul hC hq (fun i => by
          obtain ⟨j, h1, h2, h3⟩ := hg.dense k i
          exact ⟨j, h1, h2, by simp only [Yk, le_refl, ite_true]; exact h3⟩)
        hIab hJab hgap haJ f g
    rw [hFG, hF, hG]
    exact ih _ _ hsep' f' g'

end Core

end FiniteOrderMixing
