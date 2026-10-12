import FiniteOrderMixing.Realisation.WanderAverage
import FiniteOrderMixing.Realisation.Defs

/-!
# Transplanting the planar model into a surface

A `C^r` diffeomorphism of the plane equal to the identity outside `(-5, 5)²` is conjugated, by a
small affine map `ι`, into a chart of the surface `M` and extended by the identity.  The horseshoe
coding and the shadowing estimate are carried over through the chart, whose inverse is Lipschitz
near the base point (`IsChartLipschitzMetric`).  The result is `surface_wandering`, the form of
strong pluripotency (Kiriki–Li–Nakano–Soma–Vargas) used in the proof of Theorem B.
-/

open Set Filter Topology Manifold

namespace FiniteOrderMixing

/-- `z` lies in the closed square `[-5, 5]²`. -/
def In5 (z : P2) : Prop := |z.1| ≤ 5 ∧ |z.2| ≤ 5

lemma in5_of_not_far {z : P2} (h : ¬ PlaneDiffeo.Far z) : In5 z := by
  unfold PlaneDiffeo.Far at h; rw [not_or, not_le, not_le] at h; exact ⟨h.1.le, h.2.le⟩

lemma far_of_not_in5 {z : P2} (h : ¬ In5 z) : PlaneDiffeo.Far z := by
  unfold In5 at h; unfold PlaneDiffeo.Far
  by_contra h'; rw [not_or, not_le, not_le] at h'; exact h ⟨h'.1.le, h'.2.le⟩

lemma isCompact_in5 : IsCompact {z : P2 | In5 z} := by
  have : {z : P2 | In5 z} = Icc (-5 : ℝ) 5 ×ˢ Icc (-5 : ℝ) 5 := by
    ext z; simp only [In5, mem_ofPred_eq, mem_prod, mem_Icc, abs_le]
  rw [this]; exact isCompact_Icc.prod isCompact_Icc

lemma norm_le_of_in5 {z : P2} (h : In5 z) : ‖z‖ ≤ 5 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact max_le h.1 h.2

/-- A map fixing the points outside `(-5, 5)²` maps `[-5, 5]²` into itself. -/
lemma in5_apply {f : P2 → P2} (hf : ∀ z, PlaneDiffeo.Far z → f z = z)
    (hi : Function.Injective f) {z : P2} (hz : In5 z) : In5 (f z) := by
  by_contra h
  have h1 := hf _ (far_of_not_in5 h)
  have h2 : f z = z := hi h1
  rw [h2] at h; exact h hz

lemma in5_iterate {f : P2 → P2} (hf : ∀ z, PlaneDiffeo.Far z → f z = z)
    (hi : Function.Injective f) {z : P2} (hz : In5 z) (i : ℕ) : In5 (f^[i] z) := by
  induction i with
  | zero => exact hz
  | succ i ih => rw [Function.iterate_succ_apply']; exact in5_apply hf hi ih

section Transplant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The affine embedding `ι(z) = e₀ + λ L z` of the plane into the chart at `p₀`. -/
noncomputable def emb (I : ModelWithCorners ℝ E H) (p₀ : M) (L : P2 ≃L[ℝ] E) (lam : ℝ) (z : P2) : E :=
  extChartAt I p₀ p₀ + lam • L z

/-- The inverse `ι⁻¹(e) = L⁻¹ (λ⁻¹ (e - e₀))`. -/
noncomputable def embInv (I : ModelWithCorners ℝ E H) (p₀ : M) (L : P2 ≃L[ℝ] E) (lam : ℝ) (e : E) : P2 :=
  L.symm (lam⁻¹ • (e - extChartAt I p₀ p₀))

variable {p₀ : M} {L : P2 ≃L[ℝ] E} {lam : ℝ}

lemma embInv_emb (hlam : lam ≠ 0) (z : P2) : embInv I p₀ L lam (emb I p₀ L lam z) = z := by
  simp [emb, embInv, smul_smul, inv_mul_cancel₀ hlam]

lemma emb_embInv (hlam : lam ≠ 0) (e : E) : emb I p₀ L lam (embInv I p₀ L lam e) = e := by
  simp [emb, embInv, smul_smul, mul_inv_cancel₀ hlam]

lemma emb_injective (hlam : lam ≠ 0) : Function.Injective (emb I p₀ L lam) :=
  fun z z' h => by rw [← embInv_emb (I := I) (p₀ := p₀) (L := L) hlam z, h, embInv_emb hlam]

lemma contDiff_emb {n : WithTop ℕ∞} : ContDiff ℝ n (emb I p₀ L lam) :=
  contDiff_const.add (contDiff_const.smul L.contDiff)

lemma contDiff_embInv {n : WithTop ℕ∞} : ContDiff ℝ n (embInv I p₀ L lam) :=
  L.symm.contDiff.comp (contDiff_const.smul (contDiff_id.sub contDiff_const))

/-- The conjugate of `f` by `ι` and the chart at `p₀`, extended by the identity. -/
noncomputable def liftFun (I : ModelWithCorners ℝ E H) (p₀ : M) (L : P2 ≃L[ℝ] E) (lam : ℝ)
    (f : P2 → P2) (p : M) : M := by
  classical
  exact if p ∈ (extChartAt I p₀).source then
    (extChartAt I p₀).symm (emb I p₀ L lam (f (embInv I p₀ L lam (extChartAt I p₀ p))))
  else p

/-- The geometric hypotheses: `ι` maps `[-5, 5]²` into the chart target. -/
def EmbHyp (I : ModelWithCorners ℝ E H) (p₀ : M) (L : P2 ≃L[ℝ] E) (lam : ℝ) : Prop :=
  lam ≠ 0 ∧ ∀ z, In5 z → emb I p₀ L lam z ∈ (extChartAt I p₀).target

variable (hE : EmbHyp I p₀ L lam) {f g : P2 → P2}
  (hf : ∀ z, PlaneDiffeo.Far z → f z = z) (hfi : Function.Injective f)

include hE hf hfi in
lemma emb_apply_mem_target {e : E} (he : e ∈ (extChartAt I p₀).target) :
    emb I p₀ L lam (f (embInv I p₀ L lam e)) ∈ (extChartAt I p₀).target := by
  by_cases h : In5 (embInv I p₀ L lam e)
  · exact hE.2 _ (in5_apply hf hfi h)
  · rw [hf _ (far_of_not_in5 h), emb_embInv hE.1]; exact he

lemma liftFun_of_mem {p : M} (hp : p ∈ (extChartAt I p₀).source) :
    liftFun I p₀ L lam f p =
      (extChartAt I p₀).symm (emb I p₀ L lam (f (embInv I p₀ L lam (extChartAt I p₀ p)))) := by
  simp only [liftFun, hp, ↓reduceIte]

lemma liftFun_of_not_mem {p : M} (hp : p ∉ (extChartAt I p₀).source) :
    liftFun I p₀ L lam f p = p := by
  simp only [liftFun, hp, ↓reduceIte]

include hE hf hfi in
lemma liftFun_mem_source {p : M} (hp : p ∈ (extChartAt I p₀).source) :
    liftFun I p₀ L lam f p ∈ (extChartAt I p₀).source := by
  rw [liftFun_of_mem hp]
  exact (extChartAt I p₀).map_target (emb_apply_mem_target hE hf hfi ((extChartAt I p₀).map_source hp))

include hE in
lemma liftFun_emb {z : P2} (hz : In5 z) :
    liftFun I p₀ L lam f ((extChartAt I p₀).symm (emb I p₀ L lam z)) =
      (extChartAt I p₀).symm (emb I p₀ L lam (f z)) := by
  have hm := hE.2 z hz
  rw [liftFun_of_mem ((extChartAt I p₀).map_target hm), (extChartAt I p₀).right_inv hm,
    embInv_emb hE.1]

include hE hf hfi in
lemma liftFun_iterate_emb {z : P2} (hz : In5 z) (i : ℕ) :
    (liftFun I p₀ L lam f)^[i] ((extChartAt I p₀).symm (emb I p₀ L lam z)) =
      (extChartAt I p₀).symm (emb I p₀ L lam (f^[i] z)) := by
  induction i generalizing z with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, liftFun_emb hE hz, ih (in5_apply hf hfi hz),
      Function.iterate_succ_apply]

include hE in
lemma liftFun_comp (hg : ∀ z, PlaneDiffeo.Far z → g z = z) (hgi : Function.Injective g)
    (hfg : ∀ z, f (g z) = z) (p : M) : liftFun I p₀ L lam f (liftFun I p₀ L lam g p) = p := by
  by_cases hp : p ∈ (extChartAt I p₀).source
  · have hm := emb_apply_mem_target hE hg hgi ((extChartAt I p₀).map_source hp) (f := g)
    rw [liftFun_of_mem hp, liftFun_of_mem ((extChartAt I p₀).map_target hm),
      (extChartAt I p₀).right_inv hm, embInv_emb hE.1, hfg, emb_embInv hE.1,
      (extChartAt I p₀).left_inv hp]
  · rw [liftFun_of_not_mem hp, liftFun_of_not_mem hp]

variable [T2Space M]

include hE hf in
lemma liftFun_eventually_id {p : M} (hp : p ∉ (extChartAt I p₀).source) :
    liftFun I p₀ L lam f =ᶠ[𝓝 p] id := by
  set K := (extChartAt I p₀).symm '' (emb I p₀ L lam '' {z | In5 z})
  have hKc : IsCompact K := by
    refine (isCompact_in5.image (contDiff_emb (n := 0)).continuous).image_of_continuousOn
      ((continuousOn_extChartAt_symm p₀).mono ?_)
    rintro _ ⟨z, hz, rfl⟩; exact hE.2 z hz
  have hpK : p ∉ K := by
    rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hp ((extChartAt I p₀).map_target (hE.2 z hz))
  filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hpK] with q hq
  by_cases hqs : q ∈ (extChartAt I p₀).source
  · have hz : ¬ In5 (embInv I p₀ L lam (extChartAt I p₀ q)) := by
      intro hz
      apply hq
      refine ⟨_, ⟨_, hz, rfl⟩, ?_⟩
      rw [emb_embInv hE.1, (extChartAt I p₀).left_inv hqs]
    rw [liftFun_of_mem hqs, hf _ (far_of_not_in5 hz), emb_embInv hE.1,
      (extChartAt I p₀).left_inv hqs]; rfl
  · exact liftFun_of_not_mem hqs

include hE hf hfi in
lemma contMDiff_liftFun {n : WithTop ℕ∞} [IsManifold I n M] (hfc : ContDiff ℝ n f) :
    ContMDiff I I n (liftFun I p₀ L lam f) := by
  intro p
  by_cases hp : p ∈ (extChartAt I p₀).source
  · have hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n fun e => emb I p₀ L lam (f (embInv I p₀ L lam e)) :=
      (contDiff_emb.comp (hfc.comp contDiff_embInv)).contMDiff
    have hon : ContMDiffOn I I n
        ((extChartAt I p₀).symm ∘ (fun e => emb I p₀ L lam (f (embInv I p₀ L lam e))) ∘
          extChartAt I p₀) (extChartAt I p₀).source := by
      refine (contMDiffOn_extChartAt_symm p₀).comp ((hF.contMDiffOn (s := univ)).comp ?_ fun _ _ => mem_univ _) ?_
      · rw [extChartAt_source]; exact contMDiffOn_extChartAt
      · intro q hq; exact emb_apply_mem_target hE hf hfi ((extChartAt I p₀).map_source hq)
    exact (hon.congr fun q hq => liftFun_of_mem hq).contMDiffAt
      ((isOpen_extChartAt_source p₀).mem_nhds hp)
  · exact contMDiffAt_id.congr_of_eventuallyEq (liftFun_eventually_id hE hf hp)

/-- The diffeomorphism of `M` obtained from a planar diffeomorphism fixing `ℝ² ∖ (-5, 5)²`. -/
noncomputable def liftDiffeo (r : ℕ∞) [IsManifold I r M] (T : PlaneDiffeo r)
    (hT : ∀ z, PlaneDiffeo.Far z → T z = z) : M ≃ₘ^r⟮I, I⟯ M where
  toFun := liftFun I p₀ L lam T
  invFun := liftFun I p₀ L lam T.symm
  left_inv p := liftFun_comp hE hT T.injective (fun z => T.symm_apply_apply z) p
  right_inv p := liftFun_comp hE (fun z hz => T.symm_eq_of_apply_eq (hT z hz)) T.symm.injective
    (fun z => T.apply_symm_apply z) p
  contMDiff_toFun := contMDiff_liftFun hE hT T.injective T.contDiff
  contMDiff_invFun := contMDiff_liftFun hE (fun z hz => T.symm_eq_of_apply_eq (hT z hz))
    T.symm.injective T.symm.contDiff

lemma liftDiffeo_apply (r : ℕ∞) [IsManifold I r M] (T : PlaneDiffeo r)
    (hT : ∀ z, PlaneDiffeo.Far z → T z = z) (p : M) :
    liftDiffeo hE r T hT p = liftFun I p₀ L lam T p := rfl

end Transplant

/-! ### Choosing the chart embedding -/

section Choose

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- Near `p₀`, the distance is bounded by the distance in the chart at `p₀`. -/
def ChartUpperLip (p₀ : M) : Prop :=
  ∃ U ∈ 𝓝 p₀, ∃ C : ℝ, ∀ y ∈ U, ∀ z ∈ U, dist y z ≤ C * ‖extChartAt I p₀ y - extChartAt I p₀ z‖

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
lemma IsChartLipschitzMetric.chartUpperLip (hd : IsChartLipschitzMetric I (M := M)) (p₀ : M) :
    ChartUpperLip I p₀ := by
  obtain ⟨U, hU, C, hC⟩ := hd p₀
  exact ⟨U, hU, C, fun y hy z hz => (hC y hy z hz).1⟩

/-- There is a chart embedding `ι` of `[-5, 5]²` which is Lipschitz through the inverse chart
and lands in a prescribed neighbourhood `N` of the base point. -/
lemma exists_embHyp' (hE : Module.finrank ℝ E = 2) {p₀ : M} (hd : ChartUpperLip I p₀)
    {N : Set M} (hN : N ∈ 𝓝 p₀) : ∃ (L : P2 ≃L[ℝ] E) (lam C : ℝ),
      EmbHyp I p₀ L lam ∧ 0 ≤ C ∧
      (∀ z z', In5 z → In5 z' → dist ((extChartAt I p₀).symm (emb I p₀ L lam z))
        ((extChartAt I p₀).symm (emb I p₀ L lam z')) ≤ C * dist z z') ∧
      ∀ z, In5 z → (extChartAt I p₀).symm (emb I p₀ L lam z) ∈ N := by
  have hfr : Module.finrank ℝ P2 = Module.finrank ℝ E := by
    rw [hE, Module.finrank_prod, Module.finrank_self]
  let L : P2 ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hfr
  obtain ⟨U₀, hU₀, C₀, hC₀⟩ := hd
  set U := U₀ ∩ N
  have hU : U ∈ 𝓝 p₀ := Filter.inter_mem hU₀ hN
  set φ := extChartAt I p₀
  have hV : φ.target ∩ φ.symm ⁻¹' U ∈ 𝓝 (φ p₀) := by
    refine inter_mem (extChartAt_target_mem_nhds p₀) ?_
    apply ((continuousOn_extChartAt_symm p₀).continuousAt (extChartAt_target_mem_nhds p₀)).preimage_mem_nhds
    rw [extChartAt_to_inv]; exact hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  set nL := ‖(L : P2 →L[ℝ] E)‖
  set lam := δ / (10 * (nL + 1)) with hlam
  have hnL : 0 ≤ nL := norm_nonneg _
  have hlam0 : 0 < lam := by positivity
  have hin : ∀ z, In5 z → emb I p₀ L lam z ∈ φ.target ∩ φ.symm ⁻¹' U := fun z hz => by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, emb, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hlam0]
    calc lam * ‖L z‖ ≤ lam * (nL * 5) := by
          gcongr
          exact (L : P2 →L[ℝ] E).le_opNorm_of_le (norm_le_of_in5 hz)
      _ = δ * (5 * nL / (10 * (nL + 1))) := by rw [hlam]; ring
      _ < δ * 1 := by
          gcongr
          rw [div_lt_one (by positivity)]; linarith
      _ = δ := mul_one δ
  refine ⟨L, lam, |C₀| * lam * nL, ⟨hlam0.ne', fun z hz => (hin z hz).1⟩, by positivity, ?_,
    fun z hz => (hin z hz).2.2⟩
  intro z z' hz hz'
  have h1 := hin z hz
  have h2 := hin z' hz'
  have := hC₀ _ h1.2.1 _ h2.2.1
  rw [φ.right_inv h1.1, φ.right_inv h2.1, emb, emb, add_sub_add_left_eq_sub, ← smul_sub,
    ← map_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0] at this
  calc _ ≤ C₀ * (lam * ‖L (z - z')‖) := this
    _ ≤ |C₀| * (lam * ‖L (z - z')‖) := by gcongr; exact le_abs_self _
    _ ≤ |C₀| * (lam * (nL * ‖z - z'‖)) := by
        gcongr; exact (L : P2 →L[ℝ] E).le_opNorm _
    _ = |C₀| * lam * nL * dist z z' := by rw [dist_eq_norm]; ring

/-- There is a chart embedding `ι` of `[-5, 5]²` which is Lipschitz through the inverse chart. -/
lemma exists_embHyp (hE : Module.finrank ℝ E = 2) (hd : IsChartLipschitzMetric I (M := M))
    (p₀ : M) : ∃ (L : P2 ≃L[ℝ] E) (lam C : ℝ), EmbHyp I p₀ L lam ∧ 0 ≤ C ∧
      ∀ z z', In5 z → In5 z' → dist ((extChartAt I p₀).symm (emb I p₀ L lam z))
        ((extChartAt I p₀).symm (emb I p₀ L lam z')) ≤ C * dist z z' := by
  obtain ⟨L, lam, C, h1, h2, h3, -⟩ := exists_embHyp' I hE (IsChartLipschitzMetric.chartUpperLip I hd p₀) Filter.univ_mem
  exact ⟨L, lam, C, h1, h2, h3⟩

/-- **Strong pluripotency** (Kiriki–Li–Nakano–Soma–Vargas, in the form used for Theorem B).
On a surface without boundary, for every `r ≥ 1` and every `ω ∈ Σ`, there are a `C^r`
diffeomorphism `T` with a two-symbol horseshoe coded by `cod` and a nonempty open set `W` whose
orbits follow the orbit of `cod ω` in Cesàro mean. -/
theorem surface_wandering (hE : Module.finrank ℝ E = 2) [IsManifold I (⊤ : ℕ∞) M] [Nonempty M]
    (hd : IsChartLipschitzMetric I (M := M)) (r : ℕ) (hr : 1 ≤ r) (ω : Config) :
    ∃ (T : M ≃ₘ^r⟮I, I⟯ M) (cod : Config → M), HorseshoeCoding T cod ∧
      ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧ ∃ a : ℕ → ℝ,
        (∀ i : ℕ, ∀ y ∈ W, dist (T^[i] y) (T^[i] (cod ω)) ≤ a i) ∧
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 0) := by
  have : IsManifold I r M := IsManifold.of_le (n := (⊤ : ℕ∞)) (by exact_mod_cast le_top)
  obtain ⟨T₂, hc₂, hfar, W₂, hWo, hWne, hWfar, a₂, ha₂, ha₂0⟩ := plane_wandering r hr ω
  set p₀ : M := Classical.arbitrary M
  obtain ⟨L, lam, C, hE', hC, hlip⟩ := exists_embHyp I hE hd p₀
  set φ := extChartAt I p₀
  set T : M ≃ₘ^r⟮I, I⟯ M := liftDiffeo hE' r T₂ hfar
  set cod : Config → M := fun ω => φ.symm (emb I p₀ L lam (pcod ω))
  have hcod5 : ∀ ω, In5 (pcod ω) := fun ω => by
    have h1 := codX_mem ω; have h2 := codY_mem ω
    show |codX ω| ≤ 5 ∧ |codY ω| ≤ 5
    exact ⟨by rw [abs_le]; constructor <;> linarith [h1.1, h1.2],
      by rw [abs_le]; constructor <;> linarith [h2.1, h2.2]⟩
  have hTit : ∀ (z : P2), In5 z → ∀ i : ℕ, T^[i] (φ.symm (emb I p₀ L lam z)) =
      φ.symm (emb I p₀ L lam (T₂^[i] z)) := fun z hz i =>
    liftFun_iterate_emb hE' hfar T₂.injective hz i
  refine ⟨T, cod, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- continuity
    refine (continuousOn_extChartAt_symm p₀).comp_continuous
      ((contDiff_emb (n := 0)).continuous.comp hc₂.continuous) fun ω => hE'.2 _ (hcod5 ω)
  · -- injectivity
    intro ω ω' h
    exact hc₂.injective (emb_injective hE'.1 (((extChartAt I p₀).symm.injOn.eq_iff
      (hE'.2 _ (hcod5 ω)) (hE'.2 _ (hcod5 ω'))).1 h))
  · -- conjugacy
    intro ω
    have := hTit (pcod ω) (hcod5 ω) 1
    simp only [Function.iterate_one] at this
    rw [this, ← hc₂.conj]
  · -- the cylinder estimate
    obtain ⟨C', ϱ, hϱ0, hϱ1, hh⟩ := hc₂.holder
    refine ⟨C * C', ϱ, hϱ0, hϱ1, fun ℓ ω ω' hω => ?_⟩
    calc dist (cod ω) (cod ω') ≤ C * dist (pcod ω) (pcod ω') := hlip _ _ (hcod5 ω) (hcod5 ω')
      _ ≤ C * (C' * ϱ ^ ℓ) := by gcongr; exact hh ℓ ω ω' hω
      _ = C * C' * ϱ ^ ℓ := by ring
  · set W : Set M := φ.source ∩ φ ⁻¹' (emb I p₀ L lam '' W₂)
    have himg : emb I p₀ L lam '' W₂ = embInv I p₀ L lam ⁻¹' W₂ := by
      ext e; constructor
      · rintro ⟨w, hw, rfl⟩; simpa [embInv_emb hE'.1] using hw
      · intro he; exact ⟨_, he, emb_embInv hE'.1 e⟩
    refine ⟨W, ?_, ?_, fun i => C * a₂ i, ?_, ?_⟩
    · refine (continuousOn_extChartAt p₀).isOpen_inter_preimage (isOpen_extChartAt_source p₀) ?_
      rw [himg]; exact hWo.preimage (contDiff_embInv (n := 0)).continuous
    · obtain ⟨w, hw⟩ := hWne
      have hm := hE'.2 w (in5_of_not_far (hWfar w hw))
      exact ⟨φ.symm (emb I p₀ L lam w), φ.map_target hm, ⟨w, hw, (φ.right_inv hm).symm⟩⟩
    · intro i y hy
      obtain ⟨hys, w, hw, hwy⟩ := hy
      have hw5 := in5_of_not_far (hWfar w hw)
      have hy' : y = φ.symm (emb I p₀ L lam w) := by rw [hwy, φ.left_inv hys]
      rw [hy', hTit w hw5 i, hTit _ (hcod5 ω) i]
      calc _ ≤ C * dist (T₂^[i] w) (T₂^[i] (pcod ω)) :=
            hlip _ _ (in5_iterate hfar T₂.injective hw5 i)
              (in5_iterate hfar T₂.injective (hcod5 ω) i)
        _ ≤ C * a₂ i := by gcongr; exact ha₂ i w hw
    · have := ha₂0.const_mul C
      rw [mul_zero] at this
      refine this.congr fun n => ?_
      rw [← Finset.mul_sum]; ring

end Choose

end FiniteOrderMixing
