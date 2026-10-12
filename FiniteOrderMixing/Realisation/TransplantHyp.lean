import FiniteOrderMixing.Realisation.Transplant
import FiniteOrderMixing.Realisation.SmoothWandering
import FiniteOrderMixing.Realisation.Hyperbolic

/-!
# The transplanted horseshoe is uniformly hyperbolic

Through the chart at `p₀`, the derivative of the transplanted map `T` at a point of the horseshoe
is conjugate to `diag(3, 1/3)`.  The chart derivative and its inverse are bounded near `p₀` for the
Riemannian norm, so the horseshoe is uniformly hyperbolic (`isHyperbolicSet_lift`).
-/

open Set Filter Topology Manifold Bundle

namespace FiniteOrderMixing

section ChartLower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

lemma tangent_norm_congr {y y' : M} (h : y' = y) (u : E) :
    @Norm.norm (TangentSpace I y') _ u = @Norm.norm (TangentSpace I y) _ u := by
  subst h; rfl

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- Near `p₀`, the Riemannian norm is bounded by the norm in the chart at `p₀`. -/
lemma eventually_norm_le_mfderiv_extChartAt (p₀ : M) :
    ∃ K > 0, ∀ᶠ y in 𝓝 p₀, ∀ v : TangentSpace I y,
      ‖v‖ ≤ K * ‖NormedSpace.fromTangentSpace (extChartAt I p₀ y)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p₀) y v)‖ := by
  obtain ⟨C, hC, h⟩ := eventually_norm_mfderivWithin_symm_extChartAt_comp_lt I p₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, extChartAt_source_mem_nhds (I := I) p₀] with y hy hys v
  have hid := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) (x := p₀) hys
  have hv0 := DFunLike.congr_fun hid v
  rw [ContinuousLinearMap.comp_apply] at hv0
  have hv : (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (range I) (extChartAt I p₀ y))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I p₀) y v) = v := hv0
  have hyy : (extChartAt I p₀).symm (extChartAt I p₀ y) = y := (extChartAt I p₀).left_inv hys
  have key := ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (range I)
    (extChartAt I p₀ y)).le_opNorm (mfderiv I 𝓘(ℝ, E) (extChartAt I p₀) y v)).trans
    (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _))
  refine (le_of_eq (tangent_norm_congr (I := I) hyy v).symm).trans ?_
  convert key using 2 <;> first | exact congrArg norm hv.symm | rfl

section Dist

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M']
  [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)] [IsManifold I 1 M']
  [IsContinuousRiemannianBundle E (fun (x : M') ↦ TangentSpace I x)]

set_option backward.isDefEq.respectTransparency false in
/-- For a metric bounded by the intrinsic Riemannian distance,
`d(y, z) ≤ C ‖φ y - φ z‖` locally: push the segment in the chart back to the manifold. -/
lemma chartUpperLip_of_edist_le_riemannian
    (hmetric : ∀ y z : M', edist y z ≤ riemannianEDist I y z) (x : M') : ChartUpperLip I x := by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      Metric.ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∩
        {y | ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y‖ < C} :=
    Metric.mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  refine ⟨(chartAt H x).source ∩ (extChartAt I x) ⁻¹' Metric.ball (extChartAt I x x) r,
    inter_mem (chart_source_mem_nhds H x)
      ((continuousAt_extChartAt x).preimage_mem_nhds (Metric.ball_mem_nhds _ r_pos)),
    C, fun y hy z hz => ?_⟩
  let η := ContinuousAffineMap.lineMap (R := ℝ) (extChartAt I x y) (extChartAt I x z)
  set γ := (extChartAt I x).symm ∘ η
  have hy' : extChartAt I x y ∈ Metric.ball (extChartAt I x x) r ∩ range I :=
    ⟨hy.2, mem_range_self _⟩
  have hz' : extChartAt I x z ∈ Metric.ball (extChartAt I x x) r ∩ range I :=
    ⟨hz.2, mem_range_self _⟩
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩
        {y | ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) y‖ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
     ← segment_eq_image_lineMap, η]
    exact Subset.trans (((convex_ball _ _).inter I.convex_range).segment_subset hy' hz') hr
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hys : y ∈ (extChartAt I x).source := by rw [extChartAt_source]; exact hy.1
  have hzs : z ∈ (extChartAt I x).source := by rw [extChartAt_source]; exact hz.1
  have hd : riemannianEDist I y z ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp only [γ, η, Function.comp_apply, ContinuousAffineMap.coe_lineMap_eq,
        AffineMap.lineMap_apply_zero]
      exact (extChartAt I x).left_inv hys
    · simp only [γ, η, Function.comp_apply, ContinuousAffineMap.coe_lineMap_eq,
        AffineMap.lineMap_apply_one]
      exact (extChartAt I x).left_inv hzs
  have hlen : pathELength I γ 0 1 ≤
      ENNReal.ofReal C * edist (extChartAt I x y) (extChartAt I x z) := by
    rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
      ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
    have : mfderiv[Icc 0 1] γ t =
        (mfderiv[range I] (extChartAt I x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
      apply mfderivWithin_comp
      · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
      · exact η_smooth.mdifferentiableOn one_ne_zero t ht
      · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
      · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact uniqueDiffOn_Icc zero_lt_one t ht
    have : mfderiv[Icc 0 1] γ t 1 =
        (mfderiv[range I] (extChartAt I x).symm (η t)) (mfderiv[Icc 0 1] η t 1) := congr($this 1)
    rw [this, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul C_pos.le]
    apply ENNReal.ofReal_le_ofReal
    refine ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (η t)).le_opNorm _).trans ?_
    gcongr
    · exact (hη.2 ht).le
    · simp only [mfderivWithin_eq_fderivWithin]
      exact le_of_eq rfl
  have hfin : ENNReal.ofReal C * edist (extChartAt I x y) (extChartAt I x z) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top _ _)
  have h : edist y z ≤ ENNReal.ofReal C * edist (extChartAt I x y) (extChartAt I x z) := by
    exact (hmetric y z).trans (hd.trans hlen)
  have h2 := (ENNReal.toReal_le_toReal (edist_ne_top _ _) hfin).2 h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal C_pos.le, ← dist_edist, ← dist_edist,
    dist_eq_norm] at h2
  exact h2

/-- The usual Riemannian metric is a special case of the chart estimate. -/
lemma chartUpperLip_of_riemannian [IsRiemannianManifold I M'] (x : M') : ChartUpperLip I x :=
  chartUpperLip_of_edist_le_riemannian
    (fun y z => (IsRiemannianManifold.out (I := I) y z).le) x

end Dist

end ChartLower

section Lift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p₀ : M} {L : P2 ≃L[ℝ] E} {lam : ℝ}

lemma hasFDerivAt_emb (z : P2) :
    HasFDerivAt (emb I p₀ L lam) (lam • (L : P2 →L[ℝ] E)) z := by
  unfold emb
  exact ((L : P2 →L[ℝ] E).hasFDerivAt.const_smul lam).const_add _

lemma hasFDerivAt_embInv (e : E) :
    HasFDerivAt (embInv I p₀ L lam)
      ((L.symm : E →L[ℝ] P2).comp (lam⁻¹ • ContinuousLinearMap.id ℝ E)) e := by
  unfold embInv
  exact (L.symm : E →L[ℝ] P2).hasFDerivAt.comp e
    (((hasFDerivAt_id e).sub_const _).const_smul lam⁻¹)

lemma liftFun_comp_eq (hE : EmbHyp I p₀ L lam) {f g : P2 → P2}
    (hg : ∀ z, PlaneDiffeo.Far z → g z = z) (hgi : Function.Injective g) (p : M) :
    liftFun I p₀ L lam f (liftFun I p₀ L lam g p) = liftFun I p₀ L lam (f ∘ g) p := by
  by_cases hp : p ∈ (extChartAt I p₀).source
  · have hm := emb_apply_mem_target hE hg hgi ((extChartAt I p₀).map_source hp)
    rw [liftFun_of_mem hp, liftFun_of_mem ((extChartAt I p₀).map_target hm),
      (extChartAt I p₀).right_inv hm, embInv_emb hE.1, liftFun_of_mem hp]
    rfl
  · rw [liftFun_of_not_mem hp, liftFun_of_not_mem hp, liftFun_of_not_mem hp]

lemma iterate_far {f : P2 → P2} (hf : ∀ z, PlaneDiffeo.Far z → f z = z) (n : ℕ) :
    ∀ z, PlaneDiffeo.Far z → f^[n] z = z := fun z hz => Function.iterate_fixed (hf z hz) n

lemma liftFun_iterate (hE : EmbHyp I p₀ L lam) {f : P2 → P2}
    (hf : ∀ z, PlaneDiffeo.Far z → f z = z) (hfi : Function.Injective f) (n : ℕ) :
    (liftFun I p₀ L lam f)^[n] = liftFun I p₀ L lam (f^[n]) := by
  induction n with
  | zero =>
    funext p
    by_cases hp : p ∈ (extChartAt I p₀).source
    · rw [Function.iterate_zero, Function.iterate_zero, id, liftFun_of_mem hp, id,
        emb_embInv hE.1, (extChartAt I p₀).left_inv hp]
    · rw [liftFun_of_not_mem hp]; rfl
  | succ n ih =>
    funext p
    rw [Function.iterate_succ_apply, ih, liftFun_comp_eq hE hf hfi, Function.iterate_succ]

variable [I.Boundaryless] [IsManifold I 1 M]

/-- The derivative of the transplanted map at a point `φ⁻¹(ι z)`. -/
lemma hasMFDerivAt_liftFun (hE : EmbHyp I p₀ L lam) {f : P2 → P2}
    (hf : ∀ z, PlaneDiffeo.Far z → f z = z) (hfi : Function.Injective f) {z : P2} (hz : In5 z)
    {D : P2 →L[ℝ] P2} (hfd : HasFDerivAt f D z) :
    HasMFDerivAt I I (liftFun I p₀ L lam f) ((extChartAt I p₀).symm (emb I p₀ L lam z))
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p₀).symm (range I) (emb I p₀ L lam (f z))).comp
        (((lam • (L : P2 →L[ℝ] E)).comp (D.comp ((L.symm : E →L[ℝ] P2).comp
          (lam⁻¹ • ContinuousLinearMap.id ℝ E)))).comp
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p₀) ((extChartAt I p₀).symm (emb I p₀ L lam z))))) := by
  set φ := extChartAt I p₀
  set x := φ.symm (emb I p₀ L lam z)
  have hzt := hE.2 z hz
  have hxs : x ∈ φ.source := φ.map_target hzt
  have hφx : φ x = emb I p₀ L lam z := φ.right_inv hzt
  set G : E → E := fun e => emb I p₀ L lam (f (embInv I p₀ L lam e))
  have hGx : G (φ x) = emb I p₀ L lam (f z) := by simp only [G, hφx, embInv_emb hE.1]
  have hGt : G (φ x) ∈ φ.target := emb_apply_mem_target hE hf hfi (φ.map_source hxs)
  -- the three derivatives
  have h1 : HasMFDerivAt I 𝓘(ℝ, E) φ x (mfderiv I 𝓘(ℝ, E) φ x) :=
    (mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hxs)).hasMFDerivAt
  have h2 : HasFDerivAt G ((lam • (L : P2 →L[ℝ] E)).comp (D.comp ((L.symm : E →L[ℝ] P2).comp
      (lam⁻¹ • ContinuousLinearMap.id ℝ E)))) (φ x) := by
    rw [hφx]
    have ha := hasFDerivAt_embInv (I := I) (p₀ := p₀) (L := L) (lam := lam) (emb I p₀ L lam z)
    have hb : HasFDerivAt f D (embInv I p₀ L lam (emb I p₀ L lam z)) := by
      rw [embInv_emb hE.1]; exact hfd
    exact (hasFDerivAt_emb _).comp _ (hb.comp _ ha)
  have h3 : HasMFDerivAt 𝓘(ℝ, E) I φ.symm (G (φ x))
      (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) (G (φ x))) :=
    ((mdifferentiableWithinAt_extChartAt_symm hGt).hasMFDerivWithinAt).hasMFDerivAt
      (by rw [I.range_eq_univ]; exact univ_mem)
  have hc := h3.comp x (h2.hasMFDerivAt.comp x h1)
  rw [hGx] at hc
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := I) p₀).mem_nhds hxs] with q hq
  exact liftFun_of_mem hq

end Lift

section Hyp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {p₀ : M} {L : P2 ≃L[ℝ] E} {lam : ℝ}

/-- **The transplanted horseshoe is uniformly hyperbolic.** -/
theorem isHyperbolicSet_lift (hE : EmbHyp I p₀ L lam) {K : ℝ} (hK : 0 < K)
    (hbd : ∀ z, In5 z → ∀ v : TangentSpace I ((extChartAt I p₀).symm (emb I p₀ L lam z)),
      ‖NormedSpace.fromTangentSpace _ (mfderiv I 𝓘(ℝ, E) (extChartAt I p₀) _ v)‖ ≤ K * ‖v‖ ∧
      ‖v‖ ≤ K * ‖NormedSpace.fromTangentSpace _ (mfderiv I 𝓘(ℝ, E) (extChartAt I p₀) _ v)‖)
    {f : P2 → P2} (hf : ∀ z, PlaneDiffeo.Far z → f z = z) (hfi : Function.Injective f)
    (hc : HorseshoeCoding f pcod)
    (hD : ∀ (n : ℕ) (ω : Config), HasFDerivAt (f^[n]) (diagL ^ n) (pcod ω)) :
    IsHyperbolicSet I (liftFun I p₀ L lam f)
      (Set.range fun ω => (extChartAt I p₀).symm (emb I p₀ L lam (pcod ω))) := by
  set φ := extChartAt I p₀
  set Λ := Set.range fun ω => φ.symm (emb I p₀ L lam (pcod ω))
  have hcod5 : ∀ ω, In5 (pcod ω) := fun ω => by
    have h1 := codX_mem ω; have h2 := codY_mem ω
    show |codX ω| ≤ 5 ∧ |codY ω| ≤ 5
    exact ⟨by rw [abs_le]; constructor <;> linarith [h1.1, h1.2],
      by rw [abs_le]; constructor <;> linarith [h2.1, h2.2]⟩
  have hΛs : ∀ x ∈ Λ, x ∈ φ.source := by
    rintro _ ⟨ω, rfl⟩; exact φ.map_target (hE.2 _ (hcod5 ω))
  have hinv : ∀ x ∈ Λ, (mfderiv I 𝓘(ℝ, E) φ x).IsInvertible := fun x hx =>
    isInvertible_mfderiv_extChartAt (hΛs x hx)
  have hT1 : ∀ ω, liftFun I p₀ L lam f (φ.symm (emb I p₀ L lam (pcod ω))) =
      φ.symm (emb I p₀ L lam (pcod (shift ω))) := fun ω => by
    rw [liftFun_emb hE (hcod5 ω), ← hc.conj]
  -- the tangent isomorphisms `A_x = (D_x φ)⁻¹ ∘ L`
  set A : ∀ x : M, P2 →L[ℝ] TangentSpace I x := fun x =>
    (mfderiv I 𝓘(ℝ, E) φ x).inverse.comp
      (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (φ x)).symm :
        E →L[ℝ] TangentSpace 𝓘(ℝ, E) (φ x)).comp
        (L : P2 →L[ℝ] E))
  set B : ∀ x : M, TangentSpace I x →L[ℝ] P2 := fun x =>
    (L.symm : E →L[ℝ] P2).comp
      (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (φ x)) : TangentSpace 𝓘(ℝ, E) (φ x) →L[ℝ] E).comp
        (mfderiv I 𝓘(ℝ, E) φ x))
  have hDA : ∀ x ∈ Λ, ∀ w, mfderiv I 𝓘(ℝ, E) φ x (A x w) =
      (NormedSpace.fromTangentSpace (φ x)).symm (L w) := fun x hx w => by
    simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    exact (hinv x hx).self_apply_inverse _
  set K' : ℝ := K * (‖(L : P2 →L[ℝ] E)‖ + ‖(L.symm : E →L[ℝ] P2)‖ + 1)
  have hK' : 0 < K' := by positivity
  apply isHyperbolicSet_of_diag (K := K') ?_ ?_ A B ?_ ?_ hK' ?_ ?_ ?_
  · exact isCompact_range ((continuousOn_extChartAt_symm p₀).comp_continuous
      ((contDiff_emb (n := 0)).continuous.comp hc.continuous) fun ω => hE.2 _ (hcod5 ω))
  · ext y; constructor
    · rintro ⟨_, ⟨ω, rfl⟩, rfl⟩; exact ⟨shift ω, (hT1 ω).symm⟩
    · rintro ⟨ω, rfl⟩
      obtain ⟨ω', rfl⟩ : ∃ ω', shift ω' = ω := ⟨fun j => ω (j - 1), by funext j; simp [shift]⟩
      exact ⟨_, ⟨ω', rfl⟩, hT1 ω'⟩
  · intro x hx w
    have h := hDA x hx w
    simp only [B, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [h, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  · intro x hx v
    simp only [A, B, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact (hinv x hx).inverse_apply_self v
  · rintro _ ⟨ω, rfl⟩ w
    have hx : φ.symm (emb I p₀ L lam (pcod ω)) ∈ Λ := ⟨ω, rfl⟩
    have h2 := (hbd _ (hcod5 ω) (A _ w)).2
    rw [hDA _ hx w, ContinuousLinearEquiv.apply_symm_apply] at h2
    refine h2.trans ?_
    calc K * ‖(L : P2 →L[ℝ] E) w‖ ≤ K * (‖(L : P2 →L[ℝ] E)‖ * ‖w‖) := by
          gcongr; exact (L : P2 →L[ℝ] E).le_opNorm w
      _ ≤ K * (‖(L : P2 →L[ℝ] E)‖ * ‖w‖) + K * ((‖(L.symm : E →L[ℝ] P2)‖ + 1) * ‖w‖) :=
          le_add_of_nonneg_right (by positivity)
      _ = K' * ‖w‖ := by simp only [K']; ring
  · rintro _ ⟨ω, rfl⟩ v
    have h1 := (hbd _ (hcod5 ω) v).1
    simp only [B, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    calc ‖(L.symm : E →L[ℝ] P2) (NormedSpace.fromTangentSpace _ (mfderiv I 𝓘(ℝ, E) φ _ v))‖
        ≤ ‖(L.symm : E →L[ℝ] P2)‖ * ‖NormedSpace.fromTangentSpace _
          (mfderiv I 𝓘(ℝ, E) φ _ v)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(L.symm : E →L[ℝ] P2)‖ * (K * ‖v‖) := by gcongr
      _ ≤ ‖(L.symm : E →L[ℝ] P2)‖ * (K * ‖v‖) + (‖(L : P2 →L[ℝ] E)‖ + 1) * (K * ‖v‖) :=
          le_add_of_nonneg_right (by positivity)
      _ = K' * ‖v‖ := by simp only [K']; ring
  · rintro _ ⟨ω, rfl⟩ n w
    set x := φ.symm (emb I p₀ L lam (pcod ω))
    have hx : x ∈ Λ := ⟨ω, rfl⟩
    have hfn : ∀ z, PlaneDiffeo.Far z → f^[n] z = z := iterate_far hf n
    have hfni : Function.Injective (f^[n]) := hfi.iterate n
    have hder := hasMFDerivAt_liftFun hE hfn hfni (hcod5 ω) (hD n ω)
    set e' := emb I p₀ L lam ((f^[n]) (pcod ω))
    have he' : e' ∈ φ.target := hE.2 _ (in5_iterate hf hfi (hcod5 ω) n)
    have hy : liftFun I p₀ L lam (f^[n]) x = φ.symm e' := liftFun_emb hE (hcod5 ω)
    rw [liftFun_iterate hE hf hfi n, hder.mfderiv, hy]
    -- the middle factor
    have hmid : ((lam • (L : P2 →L[ℝ] E)).comp ((diagL ^ n).comp ((L.symm : E →L[ℝ] P2).comp
        (lam⁻¹ • ContinuousLinearMap.id ℝ E)))) (L w) = L ((diagL ^ n) w) := by
      simp [smul_smul, hE.1]
    -- `D φ⁻¹` is the inverse of `D φ`
    have hid := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := p₀) he'
    have hinv' := isInvertible_mfderiv_extChartAt (I := I) (x := p₀) (φ.map_target he')
    have h1 : mfderiv I 𝓘(ℝ, E) φ (φ.symm e')
        ((mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) e') (L ((diagL ^ n) w))) = L ((diagL ^ n) w) :=
      DFunLike.congr_fun hid (L ((diagL ^ n) w))
    have h2 : (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) e') (L ((diagL ^ n) w)) =
        (mfderiv I 𝓘(ℝ, E) φ (φ.symm e')).inverse (L ((diagL ^ n) w)) := by
      conv_rhs => rw [← h1]
      exact (hinv'.inverse_apply_self _).symm
    calc _ = (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) e')
          (((lam • (L : P2 →L[ℝ] E)).comp ((diagL ^ n).comp ((L.symm : E →L[ℝ] P2).comp
            (lam⁻¹ • ContinuousLinearMap.id ℝ E)))) (mfderiv I 𝓘(ℝ, E) φ x (A x w))) := rfl
      _ = (mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) e') (L ((diagL ^ n) w)) := by
          rw [hDA x hx w]; exact congrArg _ hmid
      _ = _ := h2

end Hyp

section Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- **Strong pluripotency with a hyperbolic horseshoe**, using only the upper chart estimate.
The coded horseshoe is uniformly hyperbolic and contained in a ball of radius `1/2`. -/
theorem surface_wandering_hyp_of_chartUpperLip (hE : Module.finrank ℝ E = 2)
    [IsManifold I (⊤ : ℕ∞) M] [Nonempty M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (hd : ∀ x : M, ChartUpperLip I x)
    (r : ℕ∞) (_hr : 1 ≤ r) (ω : Config) :
    ∃ (T : M ≃ₘ^r⟮I, I⟯ M) (cod : Config → M), HorseshoeCoding T cod ∧
      IsHyperbolicSet I T (Set.range cod) ∧
      (∃ p : M, ∀ ω', dist (cod ω') p < 1 / 2) ∧
      ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧ ∃ a : ℕ → ℝ,
        (∀ i : ℕ, ∀ y ∈ W, dist (T^[i] y) (T^[i] (cod ω)) ≤ a i) ∧
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 0) := by
  have : IsManifold I r M := IsManifold.of_le (n := (⊤ : ℕ∞)) (by exact_mod_cast le_top)
  have : IsManifold I 1 M := IsManifold.of_le (n := (⊤ : ℕ∞)) (by exact_mod_cast le_top)
  obtain ⟨T₂, hc₂, hfar, hDer, W₂, hWo, hWne, hWfar, a₂, ha₂, ha₂0⟩ := plane_wandering_deriv_all r ω
  set p₀ : M := Classical.arbitrary M
  obtain ⟨K₁, hK₁, hev₁⟩ := eventually_norm_mfderiv_extChartAt_apply_le (I := I) p₀
  obtain ⟨K₂, hK₂, hev₂⟩ := eventually_norm_le_mfderiv_extChartAt (I := I) p₀
  obtain ⟨L, lam, C, hE', hC, hlip, hN⟩ :=
    exists_embHyp' I hE (hd p₀) ((hev₁.and hev₂).and
      (Metric.ball_mem_nhds p₀ (by norm_num : (0 : ℝ) < 1 / 2)))
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
  have hhyp : IsHyperbolicSet I T (Set.range cod) := by
    refine isHyperbolicSet_lift hE' (K := max K₁ K₂) (by positivity) ?_ hfar T₂.injective hc₂ hDer
    intro z hz v
    obtain ⟨⟨h1, h2⟩, -⟩ := hN z hz
    exact ⟨(h1 v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)),
      (h2 v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩
  refine ⟨T, cod, ⟨?_, ?_, ?_, ?_⟩, hhyp,
    ⟨p₀, fun ω' => (hN _ (hcod5 ω')).2⟩, ?_⟩
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

/-- The version for a finite intrinsic Riemannian distance, retained for existing callers. -/
theorem surface_wandering_hyp (hE : Module.finrank ℝ E = 2)
    [IsManifold I (⊤ : ℕ∞) M] [Nonempty M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    (r : ℕ) (hr : 1 ≤ r) (ω : Config) :
    ∃ (T : M ≃ₘ^r⟮I, I⟯ M) (cod : Config → M), HorseshoeCoding T cod ∧
      IsHyperbolicSet I T (Set.range cod) ∧
      ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧ ∃ a : ℕ → ℝ,
        (∀ i : ℕ, ∀ y ∈ W, dist (T^[i] y) (T^[i] (cod ω)) ≤ a i) ∧
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 0) := by
  obtain ⟨T, cod, hc, hh, -, hW⟩ := surface_wandering_hyp_of_chartUpperLip I hE
    (chartUpperLip_of_riemannian (I := I) (M' := M)) r (by exact_mod_cast hr) ω
  exact ⟨T, cod, hc, hh, hW⟩

end Surface

end FiniteOrderMixing
