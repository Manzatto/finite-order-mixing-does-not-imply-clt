import FiniteOrderMixing.Realisation.Surface
import FiniteOrderMixing.Realisation.TransplantHyp
import FiniteOrderMixing.Realisation.SmoothVolume
import FiniteOrderMixing.Realisation.BoundedRiemann

/-!
# Properties and auxiliary results for the physical realisation

`M` is a compact smooth surface without boundary with a Riemannian metric, possibly disconnected.
The auxiliary distance is the intrinsic Riemannian distance truncated at `2`, and
`‖f‖_{C¹(M)} = ‖f‖_∞ + ‖Df‖_∞` (`c1Norm`) uses the original Riemannian tangent norms.
The main statement `TheoremB` and its proof `theoremB` are in `TheoremB.lean`.
`PhysicalRealisation` lists items
(i)–(vi) of **Theorem `thm:physical`** for the class `C¹(M)` with this norm:

* (ii) `mixingC1`: `|μ(∏ fᵢ ∘ T^{nᵢ}) - ∏ μ(fᵢ)| ≤ C e^{-cΔ} ∏ ‖fᵢ‖_{C¹}` for `fᵢ ∈ C¹(M)`;
* (iv) `robust`: the open `C¹`-ball `{g : ‖g - f₀‖_{C¹} < δ}` has no Gaussian limits;
* (vi) `notMixing`: no exponential mixing of order `2R + 2` in `C¹(M)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Manifold Bundle
open scoped ContDiff

namespace FiniteOrderMixing

section Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [MeasurableSpace M]

/-- `Λ` is a **two-symbol horseshoe** of `T`, as in the paper: a compact invariant uniformly
hyperbolic set (for the Riemannian metric) on which `T` is conjugate to the full shift on two
symbols, with exponentially small images of cylinders. -/
def IsHyperbolicHorseshoe (T : M → M) (Λ : Set M) : Prop :=
  IsTwoSymbolHorseshoe T Λ ∧ IsHyperbolicSet I T Λ

/-- The properties of **Theorem `thm:physical`** for a `C^r` diffeomorphism `T`, the horseshoe
`Λ`, the measure `μ`, the observable `f₀` and the order `R`, with the `C¹` norm of the Riemannian
metric. -/
structure PhysicalRealisation {r : WithTop ℕ∞} (T : M ≃ₘ^r⟮I, I⟯ M) (Λ : Set M) (μ : Measure M)
    (f₀ : M → ℝ) (R : ℕ) : Prop extends
    RealisationProperties T.toEquiv Λ μ f₀ (C1BoundM I) R where
  /-- `f₀ ∈ C^∞(M)`. -/
  smooth : ContMDiff I 𝓘(ℝ) ∞ f₀
  /-- (ii) exponential mixing of order `R` for `C¹(M)` observables, in the norm `‖·‖_{C¹}`. -/
  mixingC1 : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ f : Fin R → M → ℝ, (∀ i, ContMDiff I 𝓘(ℝ, ℝ) 1 (f i)) →
    ∀ n : Fin R → ℕ, StrictMono n → ∀ d : ℝ, Gapped n d →
      |∫ x, ∏ i, f i (T^[n i] x) ∂μ - ∏ i, ∫ x, f i x ∂μ| ≤
        C * Real.exp (-c * d) * ∏ i, c1Norm I (f i)
  /-- (iv) an open `C¹`-neighbourhood of `f₀` without Gaussian limits. -/
  robust : ∃ δ > 0, ∀ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) 1 g → c1Norm I (g - f₀) < δ →
    NoGaussianSubseqLimit μ (birkhoffSum T fun x => g x - ∫ y, g y ∂μ)
  /-- (v) a nonempty open set on which time averages converge uniformly; it lies in the basin. -/
  basin : ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧
    (∀ g : C(M, ℝ), TendstoUniformlyOn (fun n y => birkhoffAverage ℝ T g n y)
      (fun _ => ∫ y, g y ∂μ) atTop W) ∧ W ⊆ statBasin T μ
  /-- (v) the basin has positive measure for every measure charging open sets. -/
  basinPos : ∀ m : Measure M, m.IsOpenPosMeasure → 0 < m (statBasin T μ)
  /-- (v) hence `μ` is physical: `m(B_T(μ)) > 0` for every smooth volume `m`. -/
  physical : ∀ m : Measure M, IsSmoothVolume I m → 0 < m (statBasin T μ)

end Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

lemma c1Norm_nonneg [I.Boundaryless] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] [CompactSpace M]
    [Nonempty M] {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) : 0 ≤ c1Norm I f := by
  obtain ⟨-, a, b, ha, hb, hab⟩ := c1BoundM_c1Norm hf
  have x := Classical.arbitrary M
  have h1 := (abs_nonneg _).trans (ha x)
  have h2 := (ContinuousLinearMap.opNorm_nonneg _).trans (hb x)
  linarith

variable (I) in
/-- The conclusions of Theorem B from a metric for which `C¹` bounds are Lipschitz bounds
and the hyperbolic wandering construction is available. -/
theorem theoremB_of_metric [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [I.Boundaryless]
    [IsManifold I ∞ M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (hBd : ∀ (f : M → ℝ) (A : ℝ), C1BoundM I f A → LipBound f A)
    (r : ℕ∞) (R : ℕ) (hR : 2 ≤ R)
    (hw : ∀ w : Config, ∃ (T : M ≃ₘ^r⟮I, I⟯ M) (cod : Config → M), HorseshoeCoding T cod ∧
      IsHyperbolicSet I T (Set.range cod) ∧
      ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧ ∃ a : ℕ → ℝ,
        (∀ i : ℕ, ∀ y ∈ W, dist (T^[i] y) (T^[i] (cod w)) ≤ a i) ∧
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 0)) :
    ∃ (T : M ≃ₘ^r⟮I, I⟯ M) (Λ : Set M) (μ : Measure M) (f₀ : M → ℝ),
      IsHyperbolicHorseshoe I T Λ ∧ PhysicalRealisation I T Λ μ f₀ R := by
  obtain ⟨ν, T, cod, f₀, W, hν, hc, hhyp, hf₀s, hf₀, hf₀b, hWo, hWne, hunif⟩ :=
    physical_core_of I (M := M) r R hR (fun T cod => IsHyperbolicSet I T (Set.range cod))
      hw
  have := hν.isProb
  have hf₀c : Continuous f₀ := hf₀s.continuous
  have hf₀1 : ContMDiff I 𝓘(ℝ, ℝ) 1 f₀ := hf₀s.of_le (by exact_mod_cast le_top)
  obtain ⟨A₀, hA₀⟩ := exists_c1BoundM hf₀1
  have hTc : Continuous ⇑T.toEquiv := T.continuous
  have hTic : Continuous ⇑T.toEquiv⁻¹ := T.symm.continuous
  have hc' : HorseshoeCoding ⇑T.toEquiv cod := hc
  have hprops := realisationProperties_of_coding hR hν hTc hTic hc' hf₀c hf₀
    hBd hA₀
  obtain ⟨δ, hδ, hrob⟩ := robust_of_coding hR hν hTc.measurable hc' hf₀c hf₀ hf₀b
  have hbasin : W ⊆ statBasin T (ν.map cod) := fun y hy g => (hunif g).tendsto_at hy
  refine ⟨T, Set.range cod, ν.map cod, f₀, ⟨⟨cod, hc, rfl⟩, hhyp⟩,
    { toRealisationProperties := hprops
      smooth := hf₀s
      mixingC1 := ?_
      robust := ⟨δ, hδ, fun g hg hgδ => hrob g ?_⟩
      basin := ⟨W, hWo, hWne, hunif, hbasin⟩
      basinPos := fun m hm => (hWo.measure_pos m hWne).trans_le (measure_mono hbasin)
      physical := fun m hm => by
        have := hm.isOpenPosMeasure
        exact (hWo.measure_pos m hWne).trans_le (measure_mono hbasin) }⟩
  · obtain ⟨C, c, hc0, hmix⟩ := hprops.mixing R hR le_rfl
    refine ⟨|C| + 1, c, by positivity, hc0, fun f hf n hn d hd => ?_⟩
    have h := hmix f (fun i => c1Norm I (f i)) (fun i => c1BoundM_c1Norm (hf i)) n hn d hd
    have hpos : 0 ≤ Real.exp (-c * d) * ∏ i, c1Norm I (f i) :=
      mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ => c1Norm_nonneg (hf i))
    calc _ ≤ C * Real.exp (-c * d) * ∏ i, c1Norm I (f i) := h
      _ = C * (Real.exp (-c * d) * ∏ i, c1Norm I (f i)) := by ring
      _ ≤ (|C| + 1) * (Real.exp (-c * d) * ∏ i, c1Norm I (f i)) := by
          gcongr; linarith [le_abs_self C]
      _ = _ := by ring
  · have hgf : ContMDiff I 𝓘(ℝ, ℝ) 1 (g - f₀) := hg.sub hf₀1
    exact (hBd _ _ (c1BoundM_c1Norm hgf)).mono hgδ.le

variable (I) in
/-- The version using a globally finite intrinsic Riemannian distance. -/
theorem theoremB_metric [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hE : Module.finrank ℝ E = 2) [I.Boundaryless]
    [IsManifold I ∞ M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] [IsRiemannianManifold I M]
    (r R : ℕ) (hr : 2 ≤ r) (hR : 2 ≤ R) :
    ∃ (T : M ≃ₘ^r⟮I, I⟯ M) (Λ : Set M) (μ : Measure M) (f₀ : M → ℝ),
      IsHyperbolicHorseshoe I T Λ ∧ PhysicalRealisation I T Λ μ f₀ R :=
  theoremB_of_metric I (fun _ _ h => h.lipBound) r R hR
    (surface_wandering_hyp I hE r (by omega))

end FiniteOrderMixing
