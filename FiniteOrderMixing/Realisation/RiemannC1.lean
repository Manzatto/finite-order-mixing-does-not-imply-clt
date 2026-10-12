import FiniteOrderMixing.Realisation.Defs

/-!
# The `C¹` norm on a Riemannian manifold

On a Riemannian manifold `M` (the distance being the Riemannian distance), the paper uses
`‖f‖_{C¹(M)} = ‖f‖_∞ + ‖Df‖_∞`, where `‖Df‖_∞ = sup_x ‖D_x f‖` is computed with the Riemannian
norms on the tangent spaces.

* `C1BoundM I f A` — `f ∈ C¹(M)` and `‖f‖_∞ + ‖Df‖_∞ ≤ A`;
* `abs_sub_le_of_norm_mfderiv_le` — `|f x - f y| ≤ ‖Df‖_∞ d(x, y)`, by integrating along paths;
* `C1BoundM.lipBound` — hence a `C¹` bound is a Lipschitz bound (`LipBound`);
* `exists_bound_norm_mfderiv` — on a compact manifold, `C¹` functions have bounded differential.
-/

open Set Filter Topology Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff

namespace FiniteOrderMixing

section Riemann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- **The path estimate.** If `‖D f‖ ≤ b` along a `C¹` path `γ` on `[0, 1]`, then
`|f(γ 1) - f(γ 0)| ≤ b · length(γ)`. -/
lemma ofReal_abs_sub_le_pathELength {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) {b : ℝ}
    (hb : ∀ x, ‖mfderiv I 𝓘(ℝ, ℝ) f x‖ ≤ b) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1)) :
    ENNReal.ofReal |f (γ 1) - f (γ 0)| ≤ ENNReal.ofReal b * pathELength I γ 0 1 := by
  have hg : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (f ∘ γ) (Icc 0 1) := hf.comp_contMDiffOn hγ
  have hg' : ContDiffOn ℝ 1 (f ∘ γ) (Icc 0 1) := contMDiffOn_iff_contDiffOn.1 hg
  have hus : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hcont : ContinuousOn (derivWithin (f ∘ γ) (Icc 0 1)) (Icc 0 1) :=
    hg'.continuousOn_derivWithin hus le_rfl
  have hint : IntegrableOn (fun t => derivWithin (f ∘ γ) (Icc 0 1) t) (Icc 0 1) :=
    hcont.integrableOn_compact isCompact_Icc
  -- the fundamental theorem of calculus
  have hftc := intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hg' zero_le_one
  have h1 : |(f ∘ γ) 1 - (f ∘ γ) 0| ≤ ∫ t in Icc (0 : ℝ) 1, ‖derivWithin (f ∘ γ) (Icc 0 1) t‖ := by
    rw [← hftc, intervalIntegral.integral_of_le zero_le_one, ← restrict_Ioc_eq_restrict_Icc]
    have := MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Ioc (0 : ℝ) 1))
      (fun t => derivWithin (f ∘ γ) (Icc 0 1) t)
    rwa [Real.norm_eq_abs] at this
  -- pointwise bound on the derivative
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ‖derivWithin (f ∘ γ) (Icc 0 1) t‖ₑ ≤
      ENNReal.ofReal b * ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc 0 1) t 1‖ₑ := by
    intro t ht
    have hcomp : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f ∘ γ) (Icc 0 1) t =
        (mfderiv I 𝓘(ℝ, ℝ) f (γ t)).comp (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc 0 1) t) :=
      mfderiv_comp_mfderivWithin t ((hf (γ t)).mdifferentiableAt one_ne_zero)
        ((hγ t ht).mdifferentiableWithinAt one_ne_zero) (hus t ht).uniqueMDiffWithinAt
    set w := mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc 0 1) t 1
    have hd : derivWithin (f ∘ γ) (Icc 0 1) t =
        NormedSpace.fromTangentSpace (f (γ t)) ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)) w) := by
      have := congrArg (fun L => L 1) hcomp
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [mfderivWithin_eq_fderivWithin] at this
      exact this
    have hle : ‖NormedSpace.fromTangentSpace (f (γ t)) ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)) w)‖ ≤
        b * ‖w‖ := by
      rw [← norm_tangentSpace_vectorSpace]
      exact ((mfderiv I 𝓘(ℝ, ℝ) f (γ t)).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right (hb (γ t)) (norm_nonneg _))
    rw [hd, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul
      ((ContinuousLinearMap.opNorm_nonneg _).trans (hb (γ t)))]
    exact ENNReal.ofReal_le_ofReal hle
  calc ENNReal.ofReal |f (γ 1) - f (γ 0)| = ENNReal.ofReal |(f ∘ γ) 1 - (f ∘ γ) 0| := rfl
    _ ≤ ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, ‖derivWithin (f ∘ γ) (Icc 0 1) t‖) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin (f ∘ γ) (Icc 0 1) t‖ₑ :=
        ofReal_integral_norm_eq_lintegral_enorm hint
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal b * ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc 0 1) t 1‖ₑ :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal b * pathELength I γ 0 1 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          pathELength_eq_lintegral_mfderivWithin_Icc]

section Dist

variable [IsRiemannianManifold I M]

/-- **Mean value inequality.** For the Riemannian distance, `|f x - f y| ≤ ‖Df‖_∞ d(x, y)`. -/
lemma abs_sub_le_of_norm_mfderiv_le {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) {b : ℝ}
    (hb : ∀ x, ‖mfderiv I 𝓘(ℝ, ℝ) f x‖ ≤ b) (x y : M) : |f x - f y| ≤ b * dist x y := by
  have hb0 : 0 ≤ b := (ContinuousLinearMap.opNorm_nonneg _).trans (hb x)
  have hd : edist y x = riemannianEDist I y x := IsRiemannianManifold.out y x
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hfin : edist y x ≠ ⊤ := edist_ne_top y x
  set δ : ℝ := ε / (b + 1)
  have hδ : 0 < δ := by positivity
  have hlt : riemannianEDist I y x < edist y x + ENNReal.ofReal δ := by
    rw [← hd]; exact ENNReal.lt_add_right hfin (by simpa using hδ)
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
  have key := ofReal_abs_sub_le_pathELength hf hb hγ
  rw [hγ0, hγ1] at key
  have h2 : ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal (b * (dist x y + δ)) := by
    refine key.trans ?_
    rw [ENNReal.ofReal_mul hb0]
    gcongr
    refine hlen.le.trans ?_
    rw [edist_dist, dist_comm, ← ENNReal.ofReal_add dist_nonneg hδ.le]
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  calc |f x - f y| ≤ b * (dist x y + δ) := h3
    _ = b * dist x y + b * δ := by ring
    _ < b * dist x y + ε := by
        have : b * δ < ε := by
          simp only [δ]
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
        linarith

end Dist

section ChartBound

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- Near `x`, the differential of the chart at `x` is bounded from the Riemannian norm to the norm
of the model space. -/
lemma eventually_norm_mfderiv_extChartAt_apply_le (x : M) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y,
      ‖NormedSpace.fromTangentSpace (extChartAt I x y)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y v)‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC, h⟩ := eventually_norm_mfderiv_extChartAt_lt I x
  refine ⟨C, hC, h.mono fun y hy v => ?_⟩
  exact ((mfderiv I 𝓘(ℝ, E) (extChartAt I x) y).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _))

end ChartBound

variable [I.Boundaryless] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

/-- The differential of a `C¹` function is locally bounded. -/
lemma eventually_norm_mfderiv_le {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) (x : M) :
    ∃ b, ∀ᶠ y in 𝓝 x, ‖mfderiv I 𝓘(ℝ, ℝ) f y‖ ≤ b := by
  obtain ⟨C, hC, hCev⟩ := eventually_norm_mfderiv_extChartAt_apply_le (I := I) x
  set φ := extChartAt I x
  have hFc : ContDiffOn ℝ 1 (f ∘ φ.symm) φ.target :=
    contMDiffOn_iff_contDiffOn.1 (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := I) (n := 1) x))
  have hopen : IsOpen φ.target := isOpen_extChartAt_target (I := I) x
  have hFd : ContinuousOn (fderiv ℝ (f ∘ φ.symm)) φ.target :=
    hFc.continuousOn_fderiv_of_isOpen hopen le_rfl
  set K := ‖fderiv ℝ (f ∘ φ.symm) (φ x)‖ + 1
  have hK : ∀ᶠ e in 𝓝 (φ x), ‖fderiv ℝ (f ∘ φ.symm) e‖ ≤ K := by
    have hc := (hFd.continuousAt (hopen.mem_nhds (mem_extChartAt_target x))).norm
    exact (hc.eventually (gt_mem_nhds (lt_add_one _))).mono fun e he => he.le
  refine ⟨K * C, ?_⟩
  filter_upwards [hCev, (continuousAt_extChartAt (I := I) x).preimage_mem_nhds hK,
    extChartAt_source_mem_nhds (I := I) x] with y hy hyK hys
  have hyt : φ y ∈ φ.target := φ.map_source hys
  have heq : f =ᶠ[𝓝 y] (f ∘ φ.symm) ∘ φ := by
    filter_upwards [(isOpen_extChartAt_source (I := I) x).mem_nhds hys] with z hz
    simp [φ.left_inv hz]
  have hFm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ φ.symm) (φ y) :=
    ((hFc.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hyt)).mdifferentiableAt
  have hφm : MDifferentiableAt I 𝓘(ℝ, E) φ y :=
    mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hys)
  have hcomp : mfderiv I 𝓘(ℝ, ℝ) f y =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f ∘ φ.symm) (φ y)).comp (mfderiv I 𝓘(ℝ, E) φ y) := by
    rw [heq.mfderiv_eq]; exact mfderiv_comp y hFm hφm
  have hK0 : 0 ≤ K := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have h1 : NormedSpace.fromTangentSpace (f y) (mfderiv I 𝓘(ℝ, ℝ) f y v) =
      fderiv ℝ (f ∘ φ.symm) (φ y)
        (NormedSpace.fromTangentSpace (φ y) (mfderiv I 𝓘(ℝ, E) φ y v)) := by
    have := DFunLike.congr_fun hcomp v
    simp only [mfderiv_eq_fderiv] at this
    exact this
  rw [norm_tangentSpace_vectorSpace, h1]
  calc ‖fderiv ℝ (f ∘ φ.symm) (φ y) (NormedSpace.fromTangentSpace (φ y)
        (mfderiv I 𝓘(ℝ, E) φ y v))‖
      ≤ ‖fderiv ℝ (f ∘ φ.symm) (φ y)‖ *
          ‖NormedSpace.fromTangentSpace (φ y) (mfderiv I 𝓘(ℝ, E) φ y v)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * (C * ‖v‖) := mul_le_mul hyK (hy v) (norm_nonneg _) hK0
    _ = K * C * ‖v‖ := by ring

/-- On a compact manifold, the differential of a `C¹` function is bounded. -/
lemma exists_bound_norm_mfderiv [CompactSpace M] {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    ∃ b, ∀ x, ‖mfderiv I 𝓘(ℝ, ℝ) f x‖ ≤ b := by
  choose b hb using fun x => eventually_norm_mfderiv_le hf x
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x => {y | ‖mfderiv I 𝓘(ℝ, ℝ) f y‖ ≤ b x}) (fun x _ => hb x)
  refine ⟨∑ x ∈ t, |b x|, fun y => ?_⟩
  obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  exact hy.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun x => |b x|) (fun _ _ => abs_nonneg _) hx))

/-! ### The `C¹` norm -/

variable (I) in
/-- `‖Df‖_∞ = sup_x ‖D_x f‖`, with the Riemannian norm on `T_x M`. -/
noncomputable def dSupNorm (f : M → ℝ) : ℝ := ⨆ x, ‖mfderiv I 𝓘(ℝ, ℝ) f x‖

/-- `‖f‖_∞ = sup_x |f x|`. -/
noncomputable def supNorm (f : M → ℝ) : ℝ := ⨆ x, |f x|

variable (I) in
/-- **The `C¹` norm** `‖f‖_{C¹(M)} = ‖f‖_∞ + ‖Df‖_∞`. -/
noncomputable def c1Norm (f : M → ℝ) : ℝ := supNorm f + dSupNorm I f

variable (I) in
/-- `C1BoundM I f A`: `f ∈ C¹(M)` and `‖f‖_∞ + ‖Df‖_∞ ≤ A`. -/
def C1BoundM (f : M → ℝ) (A : ℝ) : Prop :=
  ContMDiff I 𝓘(ℝ, ℝ) 1 f ∧ ∃ a b : ℝ, (∀ x, |f x| ≤ a) ∧
    (∀ x, ‖mfderiv I 𝓘(ℝ, ℝ) f x‖ ≤ b) ∧ a + b ≤ A

/-- A `C¹` function has a finite `C¹` norm, which is a `C¹` bound. -/
lemma c1BoundM_c1Norm [CompactSpace M] {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    C1BoundM I f (c1Norm I f) := by
  obtain ⟨b, hb⟩ := exists_bound_norm_mfderiv hf
  obtain ⟨a, ha⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuous.continuousOn
  have hA : BddAbove (Set.range fun x => |f x|) :=
    ⟨a, by rintro _ ⟨x, rfl⟩; simpa [Real.norm_eq_abs] using ha x (mem_univ x)⟩
  have hB : BddAbove (Set.range fun x => ‖mfderiv I 𝓘(ℝ, ℝ) f x‖) :=
    ⟨b, by rintro _ ⟨x, rfl⟩; exact hb x⟩
  exact ⟨hf, supNorm f, dSupNorm I f, fun x => le_ciSup hA x, fun x => le_ciSup hB x, le_rfl⟩

/-- `C1BoundM I f A` is `f ∈ C¹(M)` with `‖f‖_{C¹} ≤ A`. -/
lemma c1BoundM_iff [CompactSpace M] [Nonempty M] {f : M → ℝ} {A : ℝ} :
    C1BoundM I f A ↔ ContMDiff I 𝓘(ℝ, ℝ) 1 f ∧ c1Norm I f ≤ A := by
  constructor
  · rintro ⟨hf, a, b, ha, hb, hab⟩
    exact ⟨hf, (add_le_add (ciSup_le ha) (ciSup_le hb)).trans hab⟩
  · rintro ⟨hf, h⟩
    obtain ⟨-, a, b, ha, hb, hab⟩ := c1BoundM_c1Norm hf
    exact ⟨hf, a, b, ha, hb, hab.trans h⟩

omit [I.Boundaryless] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] in
lemma C1BoundM.mono {f : M → ℝ} {A B : ℝ} (h : C1BoundM I f A) (hAB : A ≤ B) : C1BoundM I f B := by
  obtain ⟨hf, a, b, ha, hb, hab⟩ := h
  exact ⟨hf, a, b, ha, hb, hab.trans hAB⟩

/-- A smooth function on a compact manifold has a `C¹` bound. -/
lemma exists_c1BoundM [CompactSpace M] {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    ∃ A, C1BoundM I f A :=
  ⟨_, c1BoundM_c1Norm hf⟩

omit [I.Boundaryless] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] in
/-- **`C¹` bounds are Lipschitz bounds** for the Riemannian distance: `‖f‖_∞ ≤ ‖f‖_{C¹}` and
`Lip(f) ≤ ‖Df‖_∞ ≤ ‖f‖_{C¹}`. -/
lemma C1BoundM.lipBound [IsRiemannianManifold I M] {f : M → ℝ} {A : ℝ} (h : C1BoundM I f A) :
    LipBound f A := by
  obtain ⟨hf, a, b, ha, hb, hab⟩ := h
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · have := ha x
    have hb0 : 0 ≤ b := (ContinuousLinearMap.opNorm_nonneg _).trans (hb x)
    linarith
  · have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha x)
    exact (abs_sub_le_of_norm_mfderiv_le hf hb x y).trans
      (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)

end Riemann

end FiniteOrderMixing
