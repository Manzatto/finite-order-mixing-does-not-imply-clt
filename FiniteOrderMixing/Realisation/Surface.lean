import FiniteOrderMixing.Realisation.Generic
import FiniteOrderMixing.Realisation.Transplant
import FiniteOrderMixing.TheoremC

/-!
# Theorem B: realisation with a physical measure on a compact surface

* `exists_lipBound_of_contMDiff` — on a compact manifold with a chart-Lipschitz metric, smooth
  observables are Lipschitz;
* `theoremB_lipschitz` — **Theorem `thm:physical`**, combining Theorem C, the strong pluripotency theorem
  (`surface_wandering`, proved in `Transplant.lean`), Lemma `lem:transfer` and
  Proposition `prop:physical-transfer`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Manifold

namespace FiniteOrderMixing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- On a compact manifold whose metric is chart-Lipschitz, `C¹` observables are Lipschitz. -/
theorem exists_lipBound_of_contMDiff [I.Boundaryless] [CompactSpace M]
    (hd : IsChartLipschitzMetric I (M := M)) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f) {B₀ : ℝ}
    (hb : ∀ x, |f x| ≤ B₀) : ∃ A, LipBound f A := by
  have hloc : LocallyLipschitzOn Set.univ f := by
    intro x _
    obtain ⟨U, hU, C, hC⟩ := hd x
    have h2 := ((contMDiffAt_iff).1 (hf x)).2
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
      I.range_eq_univ, contDiffWithinAt_univ] at h2
    obtain ⟨K, t, ht, hK⟩ := h2.exists_lipschitzOnWith
    set φ := extChartAt I x
    have hV : U ∩ φ.source ∩ φ ⁻¹' t ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem hU (extChartAt_source_mem_nhds x))
        ((continuousAt_extChartAt x).preimage_mem_nhds ht)
    refine ⟨K * (max C 0).toNNReal, U ∩ φ.source ∩ φ ⁻¹' t, mem_nhdsWithin_of_mem_nhds hV,
      LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
    have hfy : f y = (f ∘ φ.symm) (φ y) := by simp [φ.left_inv hy.1.2]
    have hfz : f z = (f ∘ φ.symm) (φ z) := by simp [φ.left_inv hz.1.2]
    rw [hfy, hfz]
    calc dist ((f ∘ φ.symm) (φ y)) ((f ∘ φ.symm) (φ z)) ≤ K * dist (φ y) (φ z) :=
          hK.dist_le_mul _ hy.2 _ hz.2
      _ ≤ K * (max C 0 * dist y z) := by
          gcongr
          rw [dist_eq_norm]
          exact (hC y hy.1.1 z hz.1.1).2.trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
      _ = ((K * (max C 0).toNNReal : NNReal) : ℝ) * dist y z := by
          rw [NNReal.coe_mul, Real.coe_toNNReal _ (le_max_right _ _)]; ring
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_univ
  refine ⟨max B₀ K, fun x => (hb x).trans (le_max_left _ _), fun x y => ?_⟩
  rw [← Real.dist_eq]
  exact (hK.dist_le_mul x (Set.mem_univ _) y (Set.mem_univ _)).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)

variable (I) in
/-- The common core of Theorem B: the symbolic measure `ν`, the diffeomorphism `T` with its
horseshoe coding `cod`, the observable `f₀ = χ₊ - χ₋` with `f₀ ∘ cod = Z₀`, and a nonempty open
set `W` on which time averages converge uniformly to `(cod)_* ν` (Proposition
`prop:physical-transfer`).  It takes as input a form of strong pluripotency `hw`, whose extra
property `P` of the diffeomorphism and its coding is carried along. -/
theorem physical_core_of [FiniteDimensional ℝ E] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
    [IsManifold I (⊤ : ℕ∞) M] (r : ℕ∞) (R : ℕ) (hR : 2 ≤ R) (P : (M ≃ₘ^r⟮I, I⟯ M) → (Config → M) → Prop)
    (hw : ∀ ω : Config, ∃ (T : M ≃ₘ^r⟮I, I⟯ M) (cod : Config → M), HorseshoeCoding T cod ∧
      P T cod ∧ ∃ W : Set M, IsOpen W ∧ W.Nonempty ∧ ∃ a : ℕ → ℝ,
        (∀ i : ℕ, ∀ y ∈ W, dist (T^[i] y) (T^[i] (cod ω)) ≤ a i) ∧
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) atTop (𝓝 0)) :
    ∃ (ν : Measure Config) (T : M ≃ₘ^r⟮I, I⟯ M) (cod : Config → M) (f₀ : M → ℝ) (W : Set M),
      SymbolicProperties R ν ∧ HorseshoeCoding T cod ∧ P T cod ∧ ContMDiff I 𝓘(ℝ) (⊤ : ℕ∞) f₀ ∧
      (∀ ω, f₀ (cod ω) = Z 0 ω) ∧ (∀ x, |f₀ x| ≤ 1) ∧ IsOpen W ∧ W.Nonempty ∧
      ∀ g : C(M, ℝ), TendstoUniformlyOn (fun n y => birkhoffAverage ℝ T g n y)
        (fun _ => ∫ y, g y ∂(ν.map cod)) atTop W := by
  classical
  obtain ⟨ν, hν⟩ := theoremC R hR
  have := hν.isProb
  obtain ⟨ω, hω⟩ := exists_generic hR hν
  obtain ⟨T, cod, hc, hP, W, hWo, hWne, a, ha, ha0⟩ := hw ω
  -- the observable `f₀ = χ₊ - χ₋`
  have hcl : ∀ b : Bool, IsClosed (cod '' {ω : Config | ω 0 = b}) := fun b =>
    ((isClosed_eq (continuous_apply 0) continuous_const).isCompact.image hc.continuous).isClosed
  have hdisj : Disjoint (cod '' {ω : Config | ω 0 = false}) (cod '' {ω : Config | ω 0 = true}) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨ω, hω, rfl⟩ ⟨ω', hω', e⟩
    have := hc.injective e
    subst this
    simp_all
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed I (n := ⊤) (hcl false) (hcl true) hdisj
  set f₀ : M → ℝ := fun x => 2 * f x - 1
  have hf₀s : ContMDiff I 𝓘(ℝ) (⊤ : ℕ∞) f₀ :=
    ((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff.comp f.contMDiff
  have hf₀c : Continuous f₀ := hf₀s.continuous
  have hf₀b : ∀ x, |f₀ x| ≤ 1 := fun x => by
    have := hf01 x
    rw [abs_le]; constructor <;> simp only [f₀] <;> linarith [this.1, this.2]
  have hf₀ : ∀ ω, f₀ (cod ω) = Z 0 ω := fun ω => by
    cases hω' : ω 0
    · have : f (cod ω) = 0 := hf0 ⟨ω, hω', rfl⟩
      simp [f₀, Z, hω', this]
    · have : f (cod ω) = 1 := hf1 ⟨ω, hω', rfl⟩
      simp [f₀, Z, hω', this]; norm_num
  -- (v): uniform convergence of time averages on `W` (Proposition `prop:physical-transfer`)
  have hunif : ∀ g : C(M, ℝ), TendstoUniformlyOn (fun n y => birkhoffAverage ℝ T g n y)
      (fun _ => ∫ y, g y ∂(ν.map cod)) atTop W := by
    intro g
    have hgen := hω _ (g.continuous.comp hc.continuous)
    have hint : ∫ y, g y ∂(ν.map cod) = ∫ ω', (g ∘ cod) ω' ∂ν :=
      integral_map_cod hc.continuous.measurable ν g.continuous.measurable
    have havg : ∀ n, birkhoffAverage ℝ T g n (cod ω) = birkhoffAverage ℝ shift (g ∘ cod) n ω :=
      fun n => by simp only [birkhoffAverage_eq, birkhoffSum, Function.comp, hc.iterate]
    obtain ⟨G, hG⟩ := isCompact_univ.exists_bound_of_continuousOn g.continuous.continuousOn
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG (Classical.arbitrary M) (Set.mem_univ _))
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨ρ, hρ, hρg⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε / 4) (by positivity)
    set c : ℝ := 2 * (G + 1) / ρ
    have hc0 : 0 < c := by positivity
    set τ : ℝ := ε / 4 / c
    have hτ : 0 < τ := by positivity
    have h1 : ∀ᶠ n : ℕ in atTop,
        |birkhoffAverage ℝ T g n (cod ω) - ∫ y, g y ∂(ν.map cod)| < ε / 4 := by
      rw [hint]
      filter_upwards [(Metric.tendsto_nhds.1 hgen) (ε / 4) (by positivity)] with n hn
      rw [havg]; rwa [Real.dist_eq] at hn
    have h2 : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i < τ :=
      (Metric.tendsto_nhds.1 ha0 τ hτ).mono fun n hn => by
        rw [Real.dist_eq, sub_zero] at hn; exact (le_abs_self _).trans_lt hn
    filter_upwards [h1, h2, eventually_ge_atTop 1] with n hn1 hn2 hn y hy
    have hpt : ∀ i, |g (T^[i] y) - g (T^[i] (cod ω))| ≤ ε / 4 + c * a i := by
      intro i
      have hai : dist (T^[i] y) (T^[i] (cod ω)) ≤ a i := ha i y hy
      by_cases hdist : dist (T^[i] y) (T^[i] (cod ω)) < ρ
      · have := hρg hdist
        rw [Real.dist_eq] at this
        have : 0 ≤ c * a i := mul_nonneg hc0.le (dist_nonneg.trans hai)
        linarith
      · push Not at hdist
        have hai' : ρ ≤ a i := hdist.trans hai
        have hgy := hG (T^[i] y) (Set.mem_univ _)
        have hgx := hG (T^[i] (cod ω)) (Set.mem_univ _)
        rw [Real.norm_eq_abs] at hgy hgx
        have hca : 2 * (G + 1) ≤ c * a i := by
          simp only [c]
          rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
          nlinarith
        calc |g (T^[i] y) - g (T^[i] (cod ω))| ≤ |g (T^[i] y)| + |g (T^[i] (cod ω))| :=
              abs_sub _ _
          _ ≤ ε / 4 + c * a i := by linarith
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiff : |birkhoffAverage ℝ T g n y - birkhoffAverage ℝ T g n (cod ω)| ≤
        ε / 4 + c * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) := by
      rw [birkhoffAverage_eq, birkhoffAverage_eq, ← sub_div]
      have hs : birkhoffSum T g n y - birkhoffSum T g n (cod ω) =
          ∑ i ∈ Finset.range n, (g (T^[i] y) - g (T^[i] (cod ω))) := by
        simp [birkhoffSum, Finset.sum_sub_distrib]
      rw [hs, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
      calc |∑ i ∈ Finset.range n, (g (T^[i] y) - g (T^[i] (cod ω)))|
          ≤ ∑ i ∈ Finset.range n, |g (T^[i] y) - g (T^[i] (cod ω))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range n, (ε / 4 + c * a i) := Finset.sum_le_sum fun i _ => hpt i
        _ = (ε / 4 + c * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i)) * n := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            field_simp
    have hcτ : c * τ = ε / 4 := by simp only [τ]; field_simp
    rw [Real.dist_eq]
    calc |∫ y, g y ∂(ν.map cod) - birkhoffAverage ℝ T g n y|
        ≤ |birkhoffAverage ℝ T g n (cod ω) - ∫ y, g y ∂(ν.map cod)| +
          |birkhoffAverage ℝ T g n y - birkhoffAverage ℝ T g n (cod ω)| := by
          rw [abs_sub_comm (birkhoffAverage ℝ T g n (cod ω)),
            abs_sub_comm (birkhoffAverage ℝ T g n y)]
          exact abs_sub_le _ _ _
      _ < ε / 4 + (ε / 4 + c * τ) := by
          have : c * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) < c * τ :=
            mul_lt_mul_of_pos_left hn2 hc0
          linarith
      _ < ε := by rw [hcτ]; linarith
  exact ⟨ν, T, cod, f₀, W, hν, hc, hP, hf₀s, hf₀, hf₀b, hWo, hWne, hunif⟩

variable (I) in
theorem physical_core [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2) [I.Boundaryless]
    [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
    (hd : IsChartLipschitzMetric I (M := M)) (r R : ℕ) (hr : 2 ≤ r) (hR : 2 ≤ R) :
    ∃ (ν : Measure Config) (T : M ≃ₘ^r⟮I, I⟯ M) (cod : Config → M) (f₀ : M → ℝ) (W : Set M),
      SymbolicProperties R ν ∧ HorseshoeCoding T cod ∧ ContMDiff I 𝓘(ℝ) (⊤ : ℕ∞) f₀ ∧
      (∀ ω, f₀ (cod ω) = Z 0 ω) ∧ (∀ x, |f₀ x| ≤ 1) ∧ IsOpen W ∧ W.Nonempty ∧
      ∀ g : C(M, ℝ), TendstoUniformlyOn (fun n y => birkhoffAverage ℝ T g n y)
        (fun _ => ∫ y, g y ∂(ν.map cod)) atTop W := by
  obtain ⟨ν, T, cod, f₀, W, h1, h2, -, h3⟩ := physical_core_of I r R hR (fun _ _ => True)
    fun ω => by
      obtain ⟨T, cod, hc, hrest⟩ := surface_wandering I hE hd r (by omega) ω
      exact ⟨T, cod, hc, trivial, hrest⟩
  exact ⟨ν, T, cod, f₀, W, h1, h2, h3⟩

variable (I) in
/-- **Theorem `thm:physical`** (physical realisation), from Theorem C and strong pluripotency
(`surface_wandering`), for observables that are Lipschitz for the metric of `M`.  The version
with the `C¹` norm of a Riemannian metric is `theoremB` in `TheoremB.lean`. -/
theorem theoremB_lipschitz [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2) [I.Boundaryless]
    [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
    (hd : IsChartLipschitzMetric I (M := M)) (r R : ℕ) (hr : 2 ≤ r) (hR : 2 ≤ R) :
    ∃ (T : M ≃ₘ^r⟮I, I⟯ M) (Λ : Set M) (μ : Measure M) (f₀ : M → ℝ),
      IsTwoSymbolHorseshoe T Λ ∧ SurfaceRealisation I T Λ μ f₀ R := by
  obtain ⟨ν, T, cod, f₀, W, hν, hc, hf₀s, hf₀, hf₀b, hWo, hWne, hunif⟩ :=
    physical_core I hE hd r R hr hR
  have := hν.isProb
  have hf₀c : Continuous f₀ := hf₀s.continuous
  obtain ⟨A₀, hA₀⟩ := exists_lipBound_of_contMDiff hd (hf₀s.of_le (by exact_mod_cast le_top)) hf₀b
  have hTc : Continuous ⇑T.toEquiv := T.continuous
  have hTic : Continuous ⇑T.toEquiv⁻¹ := T.symm.continuous
  have hc' : HorseshoeCoding ⇑T.toEquiv cod := hc
  have hprops := realisationProperties_of_coding hR hν hTc hTic hc' hf₀c hf₀ (fun f A h => h) hA₀
  obtain ⟨δ, hδ, hrob⟩ := robust_of_coding hR hν hTc.measurable hc' hf₀c hf₀ hf₀b
  have hbasin : W ⊆ statBasin T (ν.map cod) := fun y hy g => (hunif g).tendsto_at hy
  refine ⟨T, Set.range cod, ν.map cod, f₀, ⟨cod, hc, rfl⟩,
    { toRealisationProperties := hprops
      smooth := hf₀s
      robust := ⟨δ, hδ, hrob⟩
      basin := ⟨W, hWo, hWne, hunif, hbasin⟩
      physical := fun m hm => (hWo.measure_pos m hWne).trans_le (measure_mono hbasin) }⟩

end FiniteOrderMixing
