import FiniteOrderMixing.Realisation.Robust
import FiniteOrderMixing.Mixing

/-!
# Generic points of the symbolic measure

Proposition `prop:physical-transfer` starts from a point `ω` that is generic for `ν`: the time
averages of every continuous `u : Σ → ℝ` along its orbit converge to `ν(u)`.  The paper obtains
such a point from Birkhoff's ergodic theorem and the ergodicity of `ν` (Corollary
`cor:mixing-ergodic`).  Here the exponential two-point mixing of `ν` gives it directly:

* `ae_tendsto_birkhoffAverage_holder` — the law of large numbers for `d_θ`-Hölder observables
  (Lemma `lem:variance` and `ae_tendsto_birkhoffSum_div`);
* `exists_window` — continuous observables are uniformly approximated by functions of finitely
  many coordinates;
* `exists_generic` — a point that is generic for every continuous observable.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace FiniteOrderMixing

/-! ## Correlations of a centred observable -/

lemma corr_le_of_expMixing {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {T : Y → Y}
    {Bd : (Y → ℝ) → ℝ → Prop} {C c : ℝ}
    (hmix : ∀ (f : Fin 2 → Y → ℝ) (A : Fin 2 → ℝ), (∀ i, Bd (f i) (A i)) →
      ∀ (n : Fin 2 → ℕ), StrictMono n → ∀ d : ℝ, Gapped n d →
        |∫ x, ∏ i, f i (T^[n i] x) ∂μ - ∏ i, ∫ x, f i x ∂μ| ≤ C * Real.exp (-c * d) * ∏ i, A i)
    {h : Y → ℝ} {A : ℝ} (hh : Bd h A) (hh0 : ∫ x, h x ∂μ = 0) (k : ℕ) (hk : 1 ≤ k) :
    |∫ x, h x * h (T^[k] x) ∂μ| ≤ max C 0 * Real.exp (-c * k) * A ^ 2 := by
  have hmono : StrictMono ![0, k] :=
    Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; simp; omega
  have hgap : Gapped ![0, k] (k : ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (lt_irrefl _)
    · simp
    · exact absurd hij (by decide)
    · exact absurd hij (lt_irrefl _)
  have := hmix ![h, h] ![A, A] (fun i => by fin_cases i <;> exact hh) ![0, k] hmono k hgap
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.iterate_zero, id, hh0, mul_zero, sub_zero] at this
  refine this.trans ?_
  rw [show A * A = A ^ 2 by ring]
  gcongr
  exact le_max_left _ _

/-! ## The law of large numbers for Hölder observables -/

lemma HolderBound.sub_const {θ : ℝ} (hθ : 0 ≤ θ) {F : Config → ℝ} {A : ℝ}
    (hF : HolderBound θ F A) (m : ℝ) (hm : |m| ≤ A) :
    HolderBound θ (fun ω => F ω - m) (2 * A) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hm
  refine ⟨fun ω => (abs_sub _ _).trans (by linarith [hF.1 ω]), fun ω ω' => ?_⟩
  have hd : 0 ≤ dθ θ ω ω' := by
    unfold dθ; split_ifs <;> [exact pow_nonneg hθ _; exact le_rfl]
  simp only [sub_sub_sub_cancel_right]
  exact (hF.2 ω ω').trans (mul_le_mul_of_nonneg_right (by linarith) hd)

lemma birkhoffAverage_eq {Y : Type*} (T : Y → Y) (g : Y → ℝ) (n : ℕ) (x : Y) :
    birkhoffAverage ℝ T g n x = birkhoffSum T g n x / n := by
  rw [birkhoffAverage, smul_eq_mul, inv_mul_eq_div]

theorem ae_tendsto_birkhoffAverage_holder {R : ℕ} (hR : 2 ≤ R) {ν : Measure Config}
    (hν : SymbolicProperties R ν) {F : Config → ℝ} {A : ℝ} (hF : HolderBound (1 / 2) F A) :
    ∀ᵐ ω ∂ν, Tendsto (fun n => birkhoffAverage ℝ shift F n ω) atTop (𝓝 (∫ ω, F ω ∂ν)) := by
  have := hν.isProb
  have hFm : Measurable F := hF.measurable (by norm_num) (by norm_num)
  have hA : 0 ≤ A := (abs_nonneg _).trans (hF.1 fun _ => true)
  set m := ∫ ω, F ω ∂ν
  have hFi : Integrable F ν := integrable_of_abs_le hFm hF.1
  have hm : |m| ≤ A := by
    calc |m| ≤ ∫ ω, |F ω| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _ω, A ∂ν := integral_mono hFi.abs (integrable_const _) hF.1
      _ = A := by simp
  set h : Config → ℝ := fun ω => F ω - m
  have hh := hF.sub_const (by norm_num) m hm
  have hhm : Measurable h := hFm.sub measurable_const
  have hh0 : ∫ ω, h ω ∂ν = 0 := by
    simp only [h]; rw [integral_sub hFi (integrable_const _)]; simp [m]
  obtain ⟨C, c, hc, hmix⟩ := hν.mixing (1 / 2) (by norm_num) (by norm_num) 2 le_rfl hR
  have hvar := integral_birkhoffSum_sq_le hν.invariant hhm hh.1 hc (le_max_right C 0)
    (corr_le_of_expMixing hmix hh hh0)
  have hlln := ae_tendsto_birkhoffSum_div measurable_shift hhm (by positivity) hh.1 hvar
  filter_upwards [hlln] with ω hω
  have hsum : ∀ n, birkhoffSum shift F n ω = birkhoffSum shift h n ω + n * m := fun n => by
    simp only [birkhoffSum, h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  have : Tendsto (fun n : ℕ => birkhoffSum shift h n ω / n + m) atTop (𝓝 (0 + m)) :=
    hω.add tendsto_const_nhds
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [birkhoffAverage_eq, hsum]
  field_simp

/-! ## Cylinder functions -/

/-- The indicator of the cylinder `{ω : ω|_{[-ℓ,ℓ]} = p}`. -/
noncomputable def cylInd (ℓ : ℕ) (p : Finset.Icc (-(ℓ : ℤ)) ℓ → Bool) (ω : Config) : ℝ :=
  open Classical in if ∀ j : Finset.Icc (-(ℓ : ℤ)) ℓ, ω j = p j then 1 else 0

lemma dθ_ge_of_ne {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {ω ω' : Config} {j : ℤ}
    (h : ω j ≠ ω' j) : θ ^ j.natAbs ≤ dθ θ ω ω' := by
  classical
  have hex : ∃ n : ℕ, ∃ j : ℤ, j.natAbs = n ∧ ω j ≠ ω' j := ⟨j.natAbs, j, rfl, h⟩
  unfold dθ
  simp only [hex, ↓reduceDIte]
  exact pow_le_pow_of_le_one hθ0 hθ1 (Nat.find_min' hex ⟨j, rfl, h⟩)

lemma mem_Icc_iff_natAbs_le {ℓ : ℕ} {j : ℤ} : j ∈ Finset.Icc (-(ℓ : ℤ)) ℓ ↔ j.natAbs ≤ ℓ := by
  rw [Finset.mem_Icc]; omega

lemma holderBound_cylInd {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ℓ : ℕ)
    (p : Finset.Icc (-(ℓ : ℤ)) ℓ → Bool) : HolderBound θ (cylInd ℓ p) (2 * θ⁻¹ ^ ℓ) := by
  classical
  have h1 : 1 ≤ θ⁻¹ ^ ℓ := one_le_pow₀ ((one_le_inv₀ hθ0).2 hθ1)
  have hb : ∀ ω, |cylInd ℓ p ω| ≤ 1 := fun ω => by
    unfold cylInd; split_ifs <;> simp
  refine ⟨fun ω => (hb ω).trans (by linarith), fun ω ω' => ?_⟩
  by_cases heq : cylInd ℓ p ω = cylInd ℓ p ω'
  · rw [heq, sub_self, abs_zero]
    exact mul_nonneg (by positivity) (by
      unfold dθ; split_ifs <;> [exact pow_nonneg hθ0.le _; exact le_rfl])
  · -- the two configurations differ inside the window
    obtain ⟨j, hj, hne⟩ : ∃ j : ℤ, j.natAbs ≤ ℓ ∧ ω j ≠ ω' j := by
      by_contra hcon
      push Not at hcon
      apply heq
      unfold cylInd
      have : (∀ j : Finset.Icc (-(ℓ : ℤ)) ℓ, ω j = p j) ↔
          ∀ j : Finset.Icc (-(ℓ : ℤ)) ℓ, ω' j = p j := by
        refine forall_congr' fun j => ?_
        rw [hcon j (mem_Icc_iff_natAbs_le.1 j.2)]
      simp only [this]
    have hd := dθ_ge_of_ne hθ0.le hθ1 hne
    have hpow : θ ^ ℓ ≤ θ ^ j.natAbs := pow_le_pow_of_le_one hθ0.le hθ1 hj
    calc |cylInd ℓ p ω - cylInd ℓ p ω'| ≤ |cylInd ℓ p ω| + |cylInd ℓ p ω'| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hb ω) (hb ω')
      _ = 2 * (θ⁻¹ ^ ℓ * θ ^ ℓ) := by
          rw [← mul_pow, inv_mul_cancel₀ hθ0.ne', one_pow]; norm_num
      _ ≤ 2 * (θ⁻¹ ^ ℓ * dθ θ ω ω') := by gcongr; exact hpow.trans hd
      _ = 2 * θ⁻¹ ^ ℓ * dθ θ ω ω' := by ring

/-- The configuration equal to `p` on `[-ℓ, ℓ]` and to `true` elsewhere. -/
def extend (ℓ : ℕ) (p : Finset.Icc (-(ℓ : ℤ)) ℓ → Bool) : Config := fun j =>
  if h : j ∈ Finset.Icc (-(ℓ : ℤ)) ℓ then p ⟨j, h⟩ else true

lemma continuous_trunc (ℓ : ℕ) : Continuous (trunc ℓ) :=
  continuous_pi fun j => by
    by_cases h : j.natAbs ≤ ℓ
    · simpa [trunc, h] using continuous_apply j
    · simpa [trunc, h] using continuous_const

/-- A function of the coordinates in `[-ℓ, ℓ]` is a combination of cylinder indicators. -/
lemma comp_trunc_eq_sum (u : Config → ℝ) (ℓ : ℕ) (ω : Config) :
    u (trunc ℓ ω) = ∑ p : Finset.Icc (-(ℓ : ℤ)) ℓ → Bool, u (extend ℓ p) * cylInd ℓ p ω := by
  classical
  rw [Finset.sum_eq_single (fun j : Finset.Icc (-(ℓ : ℤ)) ℓ => ω j)]
  · have hc : cylInd ℓ (fun j => ω j) ω = 1 := by unfold cylInd; simp
    have he : extend ℓ (fun j : Finset.Icc (-(ℓ : ℤ)) ℓ => ω j) = trunc ℓ ω := by
      funext j
      by_cases h : j ∈ Finset.Icc (-(ℓ : ℤ)) ℓ
      · simp [extend, trunc, h, mem_Icc_iff_natAbs_le.1 h]
      · have : ¬ j.natAbs ≤ ℓ := fun h' => h (mem_Icc_iff_natAbs_le.2 h')
        simp [extend, trunc, h, this]
    rw [hc, he, mul_one]
  · intro p _ hp
    have : cylInd ℓ p ω = 0 := by
      unfold cylInd
      split_ifs with hall
      · exact absurd (funext fun j => (hall j).symm) hp
      · rfl
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Continuous observables -/

/-- A continuous observable is uniformly approximated by functions of the coordinates in a
finite window. -/
lemma exists_window (u : Config → ℝ) (hu : Continuous u) {ε : ℝ} (hε : 0 < ε) :
    ∃ ℓ : ℕ, ∀ ω ω' : Config, (∀ j : ℤ, j.natAbs ≤ ℓ → ω j = ω' j) → |u ω - u ω'| < ε := by
  classical
  have hloc : ∀ ω : Config, ∃ ℓ : ℕ, ∀ ω' : Config,
      (∀ j : ℤ, j.natAbs ≤ ℓ → ω' j = ω j) → |u ω' - u ω| < ε / 2 := by
    intro ω
    have hV : IsOpen (u ⁻¹' Metric.ball (u ω) (ε / 2)) := Metric.isOpen_ball.preimage hu
    obtain ⟨I, s, hs, hIs⟩ := isOpen_pi_iff.1 hV ω (Metric.mem_ball_self (half_pos hε))
    refine ⟨I.sup Int.natAbs, fun ω' h => ?_⟩
    have hmem : ω' ∈ (I : Set ℤ).pi s := fun a ha => by
      rw [h a (Finset.le_sup (f := Int.natAbs) ha)]; exact (hs a ha).2
    have := hIs hmem
    simpa [Metric.mem_ball, Real.dist_eq] using this
  choose ℓ hℓ using hloc
  set O : Config → Set Config := fun ω =>
    ⋂ j ∈ Finset.Icc (-(ℓ ω : ℤ)) (ℓ ω), {ω' | ω' j = ω j}
  have hmemO : ∀ ω ω', ω' ∈ O ω ↔ ∀ j : ℤ, j.natAbs ≤ ℓ ω → ω' j = ω j := fun ω ω' => by
    simp only [O, Set.mem_iInter, Set.mem_ofPred_eq]
    exact forall_congr' fun j => by rw [mem_Icc_iff_natAbs_le]
  have hO : ∀ ω, IsOpen (O ω) := fun ω =>
    isOpen_biInter_finset fun j _ => by
      have : IsOpen ((fun ω' : Config => ω' j) ⁻¹' ({ω j} : Set Bool)) :=
        (isOpen_discrete _).preimage (continuous_apply j)
      exact this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun ω _ => Set.mem_iUnion.2 ⟨ω, (hmemO ω ω).2 fun _ _ => rfl⟩)
  refine ⟨t.sup ℓ, fun ω₁ ω₂ h => ?_⟩
  obtain ⟨ω, hωt, hω₁⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ω₁))
  have h1 := (hmemO ω ω₁).1 hω₁
  have hle : ℓ ω ≤ t.sup ℓ := Finset.le_sup hωt
  have h2 : ∀ j : ℤ, j.natAbs ≤ ℓ ω → ω₂ j = ω j := fun j hj =>
    (h j (hj.trans hle)).symm.trans (h1 j hj)
  have e1 := hℓ ω ω₁ h1
  have e2 := hℓ ω ω₂ h2
  calc |u ω₁ - u ω₂| ≤ |u ω₁ - u ω| + |u ω₂ - u ω| := by
        rw [abs_sub_comm (u ω₂)]; exact abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add e1 e2
    _ = ε := by ring

lemma abs_birkhoffAverage_sub_le {Y : Type*} {T : Y → Y} {g g' : Y → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x, |g x - g' x| ≤ ε) (n : ℕ) (x : Y) :
    |birkhoffAverage ℝ T g n x - birkhoffAverage ℝ T g' n x| ≤ ε := by
  rw [birkhoffAverage_eq, birkhoffAverage_eq, ← sub_div, ← birkhoffSum_sub_apply]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [hε]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_div, abs_of_pos hn', div_le_iff₀ hn', mul_comm]
    exact abs_birkhoffSum_le (h := g - g') h n x

/-- A point that is generic for `ν`: the time averages of every continuous observable converge
to its integral. -/
theorem exists_generic {R : ℕ} (hR : 2 ≤ R) {ν : Measure Config} (hν : SymbolicProperties R ν) :
    ∃ ω : Config, ∀ u : Config → ℝ, Continuous u →
      Tendsto (fun n => birkhoffAverage ℝ shift u n ω) atTop (𝓝 (∫ ω', u ω' ∂ν)) := by
  classical
  have := hν.isProb
  have hall : ∀ᵐ ω ∂ν, ∀ q : (Σ ℓ : ℕ, (Finset.Icc (-(ℓ : ℤ)) ℓ → Bool)),
      Tendsto (fun n => birkhoffAverage ℝ shift (cylInd q.1 q.2) n ω) atTop
        (𝓝 (∫ ω', cylInd q.1 q.2 ω' ∂ν)) :=
    ae_all_iff.2 fun q => ae_tendsto_birkhoffAverage_holder hR hν
      (holderBound_cylInd (θ := 1 / 2) (by norm_num) (by norm_num) q.1 q.2)
  obtain ⟨ω, hω⟩ := hall.exists
  refine ⟨ω, fun u hu => ?_⟩
  have hcyl : ∀ ℓ p, Integrable (cylInd ℓ p) ν := fun ℓ p =>
    integrable_of_abs_le ((holderBound_cylInd (θ := 1 / 2) (by norm_num) (by norm_num) ℓ p
      ).measurable (by norm_num) (by norm_num)) (holderBound_cylInd (θ := 1 / 2) (by norm_num)
        (by norm_num) ℓ p).1
  obtain ⟨Cu, hCu⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuousOn
  have hui : Integrable u ν :=
    integrable_of_abs_le hu.measurable fun x => by
      simpa [Real.norm_eq_abs] using hCu x (Set.mem_univ x)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ℓ, hℓ⟩ := exists_window u hu (show 0 < ε / 4 by positivity)
  set uℓ : Config → ℝ := fun ω' => u (trunc ℓ ω')
  have huℓm : Measurable uℓ := (hu.comp (continuous_trunc ℓ)).measurable
  have huℓi : Integrable uℓ ν :=
    integrable_of_abs_le huℓm fun x => by
      simpa [Real.norm_eq_abs] using hCu _ (Set.mem_univ (trunc ℓ x))
  have happrox : ∀ ω', |u ω' - uℓ ω'| ≤ ε / 4 := fun ω' =>
    (hℓ ω' (trunc ℓ ω') fun j hj => by simp [trunc, hj]).le
  -- the averages of `uℓ` converge
  have hconv : Tendsto (fun n => birkhoffAverage ℝ shift uℓ n ω) atTop
      (𝓝 (∫ ω', uℓ ω' ∂ν)) := by
    have hsum : ∀ n, birkhoffAverage ℝ shift uℓ n ω = ∑ p : Finset.Icc (-(ℓ : ℤ)) ℓ → Bool,
        u (extend ℓ p) * birkhoffAverage ℝ shift (cylInd ℓ p) n ω := fun n => by
      simp only [birkhoffAverage_eq, birkhoffSum, uℓ]
      simp_rw [comp_trunc_eq_sum u ℓ]
      rw [Finset.sum_comm, Finset.sum_div]
      exact Finset.sum_congr rfl fun p _ => by rw [← Finset.mul_sum, mul_div_assoc]
    have hint : ∫ ω', uℓ ω' ∂ν = ∑ p : Finset.Icc (-(ℓ : ℤ)) ℓ → Bool,
        u (extend ℓ p) * ∫ ω', cylInd ℓ p ω' ∂ν := by
      show ∫ ω', u (trunc ℓ ω') ∂ν = _
      simp_rw [comp_trunc_eq_sum u ℓ]
      rw [integral_finsetSum _ fun p _ => (hcyl ℓ p).const_mul _]
      simp_rw [integral_const_mul]
    simp_rw [hsum, hint]
    exact tendsto_finsetSum _ fun p _ => (hω ⟨ℓ, p⟩).const_mul _
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hconv (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := abs_birkhoffAverage_sub_le (T := shift) (by positivity) happrox n ω
  have h2 : |∫ ω', u ω' ∂ν - ∫ ω', uℓ ω' ∂ν| ≤ ε / 4 := by
    rw [← integral_sub hui huℓi]
    calc |∫ ω', (u ω' - uℓ ω') ∂ν| ≤ ∫ ω', |u ω' - uℓ ω'| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _ω', ε / 4 ∂ν := integral_mono (hui.sub huℓi).abs (integrable_const _) happrox
      _ = ε / 4 := by simp
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  calc |birkhoffAverage ℝ shift u n ω - ∫ ω', u ω' ∂ν|
      ≤ |birkhoffAverage ℝ shift u n ω - birkhoffAverage ℝ shift uℓ n ω| +
        |birkhoffAverage ℝ shift uℓ n ω - ∫ ω', uℓ ω' ∂ν| +
        |∫ ω', uℓ ω' ∂ν - ∫ ω', u ω' ∂ν| := by
          have := abs_sub_le (birkhoffAverage ℝ shift u n ω) (birkhoffAverage ℝ shift uℓ n ω)
            (∫ ω', u ω' ∂ν)
          have := abs_sub_le (birkhoffAverage ℝ shift uℓ n ω) (∫ ω', uℓ ω' ∂ν)
            (∫ ω', u ω' ∂ν)
          linarith
    _ < ε / 4 + ε / 4 + ε / 4 := by
        rw [abs_sub_comm (∫ ω', uℓ ω' ∂ν)]
        linarith
    _ < ε := by linarith

end FiniteOrderMixing
