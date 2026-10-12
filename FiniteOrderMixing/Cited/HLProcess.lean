import FiniteOrderMixing.Cited.HLWord
import FiniteOrderMixing.Cited.Kolmogorov

/-!
# The Holroyd–Liggett one-dependent four-colouring of `ℤ`

The weights `P` of `FiniteOrderMixing.HLWord` give measures `μ n` on the words of length `n`.  Their
windows are consistent, so Kolmogorov's extension gives a law `ν4` on `ℤ → Fin 4` whose windows
of length `n` have law `μ n`.  It is stationary, proper, and one-dependent: cylinder
probabilities factorise over sets at distance at least two.
-/

open MeasureTheory Finset

namespace FiniteOrderMixing.HL

/-! ## The measures on words -/

/-- The law of the word of length `n`. -/
noncomputable def μ (n : ℕ) : Measure (Fin n → Fin 4) :=
  ∑ f, ENNReal.ofReal (P (List.ofFn f)) • Measure.dirac f

lemma μ_apply (n : ℕ) (S : Set (Fin n → Fin 4)) :
    μ n S = ∑ f, ENNReal.ofReal (P (List.ofFn f)) * S.indicator 1 f := by
  simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (Set.toFinite S).measurableSet]

lemma μ_singleton (n : ℕ) (g : Fin n → Fin 4) : μ n {g} = ENNReal.ofReal (P (List.ofFn g)) := by
  rw [μ_apply, Finset.sum_eq_single g]
  · simp
  · intro f _ hf; simp [hf]
  · simp

instance (n : ℕ) : IsProbabilityMeasure (μ n) := by
  constructor
  rw [μ_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun f _ => P_nonneg _, sum_all, ENNReal.ofReal_one]

lemma sum_fun_last (p : ℕ) (F : (Fin (p + 1) → Fin 4) → ℝ) :
    ∑ f, F f = ∑ a : Fin 4, ∑ g : Fin p → Fin 4, F (Fin.snoc g a) := by
  rw [← (Fin.snocEquiv fun _ => Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

lemma μ_map_tail (n : ℕ) : (μ (n + 1)).map Fin.tail = μ n := by
  refine Measure.ext_of_singleton fun g => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton g), μ_singleton,
    μ_apply]
  rw [← sum_cons (List.ofFn g)]
  have e : ∀ f : Fin (n + 1) → Fin 4, ENNReal.ofReal (P (List.ofFn f)) *
      ((Fin.tail (α := fun _ => Fin 4)) ⁻¹' {g}).indicator 1 f =
        ENNReal.ofReal (if Fin.tail f = g then P (List.ofFn f) else 0) := fun f => by
    by_cases h : Fin.tail f = g <;> simp [h, Set.indicator]
  rw [Finset.sum_congr rfl fun f _ => e f, ← ENNReal.ofReal_sum_of_nonneg fun f _ => by
    split_ifs <;> simp [P_nonneg], sum_fun_succ]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single g]
  · simp [List.ofFn_succ]
  · intro h _ hh; simp [hh]
  · simp

lemma μ_map_init (n : ℕ) : (μ (n + 1)).map Fin.init = μ n := by
  refine Measure.ext_of_singleton fun g => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton g), μ_singleton,
    μ_apply]
  rw [← sum_snoc (List.ofFn g)]
  have e : ∀ f : Fin (n + 1) → Fin 4, ENNReal.ofReal (P (List.ofFn f)) *
      ((Fin.init (α := fun _ => Fin 4)) ⁻¹' {g}).indicator 1 f =
        ENNReal.ofReal (if Fin.init f = g then P (List.ofFn f) else 0) := fun f => by
    by_cases h : Fin.init f = g <;> simp [h, Set.indicator]
  rw [Finset.sum_congr rfl fun f _ => e f, ← ENNReal.ofReal_sum_of_nonneg fun f _ => by
    split_ifs <;> simp [P_nonneg], sum_fun_last]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single g]
  · rw [ite_eq_left (Fin.init_snoc _ _), List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
  · intro h _ hh; simp [hh]
  · simp

/-- The window of length `n` at offset `p` of a word of length `N`. -/
def win (N p n : ℕ) (h : p + n ≤ N) (f : Fin N → Fin 4) : Fin n → Fin 4 :=
  fun j => f ⟨p + j, by omega⟩

/-- Windows of the word of length `N` have the law of the shorter words. -/
theorem μ_map_win : ∀ (N p n : ℕ) (h : p + n ≤ N), (μ N).map (win N p n h) = μ n := by
  intro N
  induction N with
  | zero =>
    intro p n h
    obtain rfl : n = 0 := by omega
    have : win 0 p 0 h = id := funext fun f => funext fun j => j.elim0
    rw [this, Measure.map_id]
  | succ N ih =>
    intro p n h
    rcases p with _ | p
    · by_cases hn : n = N + 1
      · subst hn
        have : win (N + 1) 0 (N + 1) h = id := funext fun f => funext fun j => by
          simp [win]
        rw [this, Measure.map_id]
      · have : win (N + 1) 0 n h = win N 0 n (by omega) ∘ Fin.init := funext fun f =>
          funext fun j => by simp [win, Fin.init]
        rw [this, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
          μ_map_init, ih]
    · have : win (N + 1) (p + 1) n h = win N p n (by omega) ∘ Fin.tail := funext fun f =>
        funext fun j => by
          simp only [win, Function.comp, Fin.tail]
          congr 1; ext; simp; omega
      rw [this, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
        μ_map_tail, ih]

/-! ## Splitting a word into blocks -/

lemma win_append_left {m k p n : ℕ} (h : p + n ≤ m) (h' : p + n ≤ m + k)
    (w : Fin m → Fin 4) (v : Fin k → Fin 4) :
    win (m + k) p n h' (Fin.append w v) = win m p n h w := funext fun j => by
  simp only [win]
  have : (⟨p + j, by omega⟩ : Fin (m + k)) = Fin.castAdd k ⟨p + j, by omega⟩ := Fin.ext rfl
  rw [this, Fin.append_left]

lemma win_append_right {m k : ℕ} (h : m + k ≤ m + k) (w : Fin m → Fin 4) (v : Fin k → Fin 4) :
    win (m + k) m k h (Fin.append w v) = v := funext fun j => by
  simp only [win]
  have : (⟨m + j, by omega⟩ : Fin (m + k)) = Fin.natAdd m j := Fin.ext rfl
  rw [this, Fin.append_right]

lemma win_self {m : ℕ} (h : 0 + m ≤ m) (w : Fin m → Fin 4) : win m 0 m h w = w :=
  funext fun j => by simp [win]

lemma sum_fun_add (m : ℕ) : ∀ (n : ℕ) (F : (Fin (m + n) → Fin 4) → ℝ),
    ∑ f, F f = ∑ u : Fin m → Fin 4, ∑ v : Fin n → Fin 4, F (Fin.append u v) := by
  intro n
  induction n with
  | zero =>
    intro F
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Fintype.sum_unique]
    congr 1
    exact (Fin.append_right_nil u _ rfl).symm
  | succ n ih =>
    intro F
    refine (sum_fun_last (m + n) F).trans ?_
    rw [Finset.sum_comm]
    simp_rw [ih]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [sum_fun_last n, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun v _ => ?_
    rw [Fin.append_snoc]

/-- The two outer blocks of a word, separated by a nonempty gap, are independent. -/
theorem μ_map_pair (n₁ t n₂ : ℕ) :
    (μ (n₁ + (t + 1) + n₂)).map (fun f => (win _ 0 n₁ (by omega) f,
      win _ (n₁ + (t + 1)) n₂ le_rfl f)) = (μ n₁).prod (μ n₂) := by
  refine Measure.ext_of_singleton fun ⟨u, v⟩ => ?_
  conv_rhs => rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    μ_singleton, μ_singleton, μ_apply,
    ← ENNReal.ofReal_mul (P_nonneg _), ← sum_gap t (List.ofFn u) (List.ofFn v)]
  have e : ∀ f : Fin (n₁ + (t + 1) + n₂) → Fin 4, ENNReal.ofReal (P (List.ofFn f)) *
      ((fun f => (win _ 0 n₁ (by omega) f, win _ (n₁ + (t + 1)) n₂ le_rfl f)) ⁻¹'
        {(u, v)}).indicator 1 f =
      ENNReal.ofReal (if win _ 0 n₁ (by omega) f = u ∧ win _ (n₁ + (t + 1)) n₂ le_rfl f = v
        then P (List.ofFn f) else 0) := fun f => by
    by_cases h : win _ 0 n₁ (by omega) f = u ∧ win _ (n₁ + (t + 1)) n₂ le_rfl f = v
    · simp [Set.indicator, h]
    · simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
      rw [ite_eq_right h, ite_eq_right h]; simp
  rw [Finset.sum_congr rfl fun f _ => e f, ← ENNReal.ofReal_sum_of_nonneg fun f _ => by
    split_ifs <;> simp [P_nonneg]]
  congr 1
  rw [sum_fun_add (n₁ + (t + 1)) n₂, sum_fun_add n₁ (t + 1)]
  simp only [win_append_right,
    win_append_left (m := n₁ + (t + 1)) (k := n₂) (p := 0) (n := n₁) (by omega),
    win_append_left (m := n₁) (k := t + 1) (p := 0) (n := n₁) (by omega), win_self]
  rw [Finset.sum_eq_single u (fun u' _ hu' => by simp [hu']) (by simp)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_eq_single v (fun v' _ hv' => by simp [hv']) (by simp)]
  rw [ite_eq_left ⟨rfl, rfl⟩, List.ofFn_fin_append, List.ofFn_fin_append]

/-! ## The process on `ℤ` -/

/-- Reading the coordinates of `E ⊆ [a, a+n)` off a word of length `n`. -/
def ext (E : Finset ℤ) (a : ℤ) (n : ℕ) (h : ∀ e ∈ E, a ≤ e ∧ e < a + n)
    (f : Fin n → Fin 4) : E → Fin 4 :=
  fun e => f ⟨(e.1 - a).toNat, by have := h e.1 e.2; omega⟩

/-- The law of the coordinates in `E`, read off any interval containing `E`. -/
noncomputable def Q (E : Finset ℤ) (a : ℤ) (n : ℕ) (h : ∀ e ∈ E, a ≤ e ∧ e < a + n) :
    Measure (E → Fin 4) :=
  (μ n).map (ext E a n h)

instance (E : Finset ℤ) (a : ℤ) (n : ℕ) (h : ∀ e ∈ E, a ≤ e ∧ e < a + n) :
    IsProbabilityMeasure (Q E a n h) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2 inferInstance

lemma Q_sub {E : Finset ℤ} {a b : ℤ} {n m : ℕ} (h : ∀ e ∈ E, a ≤ e ∧ e < a + n)
    (h' : ∀ e ∈ E, b ≤ e ∧ e < b + m) (hab : a ≤ b) (hbm : b + m ≤ a + n) :
    Q E a n h = Q E b m h' := by
  have hw : (b - a).toNat + m ≤ n := by omega
  have : ext E a n h = ext E b m h' ∘ win n (b - a).toNat m hw := funext fun f => funext fun e => by
    have := h' e.1 e.2
    simp only [ext, win, Function.comp]
    congr 1; ext; simp only; omega
  rw [Q, Q, this, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    μ_map_win]

lemma Q_indep {E : Finset ℤ} {a a' : ℤ} {n n' : ℕ} (h : ∀ e ∈ E, a ≤ e ∧ e < a + n)
    (h' : ∀ e ∈ E, a' ≤ e ∧ e < a' + n') : Q E a n h = Q E a' n' h' := by
  rcases E.eq_empty_or_nonempty with hE | ⟨e0, he0⟩
  · subst hE
    refine Measure.ext_of_singleton fun x => ?_
    rw [show ({x} : Set ((∅ : Finset ℤ) → Fin 4)) = Set.univ from
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _]
    simp
  have h0 := h e0 he0
  have h0' := h' e0 he0
  set b := max a a'
  set c := min (a + n) (a' + n')
  have hb : ∀ e ∈ E, b ≤ e ∧ e < b + (c - b).toNat := fun e he => by
    have := h e he; have := h' e he; omega
  rw [Q_sub h hb (by omega) (by omega), Q_sub h' hb (by omega) (by omega)]

/-- The size of a symmetric interval containing `E`. -/
def NE (E : Finset ℤ) : ℕ := E.sup Int.natAbs

lemma mem_NE {E : Finset ℤ} : ∀ e ∈ E, -(NE E : ℤ) ≤ e ∧ e < -(NE E : ℤ) + (2 * NE E + 1 : ℕ) :=
  fun e he => by
    have := Finset.le_sup (f := Int.natAbs) he
    simp only [NE] at *
    omega

/-- The finite-dimensional laws. -/
noncomputable def PE (E : Finset ℤ) : Measure (E → Fin 4) := Q E _ _ (mem_NE (E := E))

instance (E : Finset ℤ) : IsProbabilityMeasure (PE E) := by unfold PE; infer_instance

lemma PE_eq {E : Finset ℤ} {a : ℤ} {n : ℕ} (h : ∀ e ∈ E, a ≤ e ∧ e < a + n) : PE E = Q E a n h :=
  Q_indep _ _

lemma PE_projective : IsProjectiveMeasureFamily (α := fun _ : ℤ => Fin 4) PE := by
  intro I J hJI
  have hJ : ∀ e ∈ J, -(NE I : ℤ) ≤ e ∧ e < -(NE I : ℤ) + (2 * NE I + 1 : ℕ) :=
    fun e he => mem_NE e (hJI he)
  rw [PE_eq hJ]
  unfold PE Q
  exact (Measure.map_map (measurable_of_countable (Finset.restrict₂ (π := fun _ : ℤ => Fin 4) hJI))
    (measurable_of_countable (ext I _ _ (mem_NE (E := I))))).symm

lemma exists_ν4 : ∃ ν : Measure (ℤ → Fin 4), IsProbabilityMeasure ν ∧ IsProjectiveLimit ν PE :=
  kolmogorov_extension_finite PE PE_projective

/-- The Holroyd–Liggett four-colouring of `ℤ`. -/
noncomputable def ν4 : Measure (ℤ → Fin 4) := Classical.choose exists_ν4

instance : IsProbabilityMeasure ν4 := (Classical.choose_spec exists_ν4).1

lemma ν4_lim : IsProjectiveLimit ν4 PE := (Classical.choose_spec exists_ν4).2

/-- The window of length `n` at `a`. -/
def W (a : ℤ) (n : ℕ) (ω : ℤ → Fin 4) : Fin n → Fin 4 := fun j => ω (a + j)

lemma measurable_W (a : ℤ) (n : ℕ) : Measurable (W a n) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- Every window has the law of the words. -/
theorem ν4_map_W (a : ℤ) (n : ℕ) : ν4.map (W a n) = μ n := by
  set E := Finset.Ico a (a + n)
  have hE : ∀ e ∈ E, a ≤ e ∧ e < a + n := fun e he => by simpa [E] using he
  set r : (E → Fin 4) → (Fin n → Fin 4) := fun σ j => σ ⟨a + j, by simp [E]⟩
  have hW : W a n = r ∘ E.restrict := rfl
  have hr : r ∘ ext E a n hE = id := funext fun f => funext fun j => by
    simp only [r, ext, Function.comp, id]
    congr 1; ext; simp
  rw [hW, ← Measure.map_map (measurable_of_countable r) (Finset.measurable_restrict E), ν4_lim E,
    PE_eq hE, Q, Measure.map_map (measurable_of_countable _) (measurable_of_countable _), hr,
    Measure.map_id]

/-- The shift of a colouring. -/
def sh (ω : ℤ → Fin 4) : ℤ → Fin 4 := fun j => ω (j + 1)

lemma measurable_sh : Measurable sh := measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- **Stationarity.** -/
theorem ν4_stationary : MeasurePreserving sh ν4 ν4 := by
  refine ⟨measurable_sh, ?_⟩
  refine IsProjectiveLimit.unique (P := PE) (fun E => ?_) ν4_lim
  set E' := E.image (· + 1)
  have hE' : ∀ e ∈ E', -(NE E : ℤ) + 1 ≤ e ∧ e < -(NE E : ℤ) + 1 + (2 * NE E + 1 : ℕ) :=
    fun e he => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 he
      have := mem_NE x hx; omega
  set r : (E' → Fin 4) → (E → Fin 4) := fun σ e => σ ⟨e.1 + 1, Finset.mem_image_of_mem _ e.2⟩
  have hc : E.restrict ∘ sh = r ∘ E'.restrict := rfl
  have hr : r ∘ ext E' _ _ hE' = ext E _ _ (mem_NE (E := E)) := funext fun f => funext fun e => by
    simp only [r, ext, Function.comp]
    congr 1; ext; simp only; omega
  rw [Measure.map_map (Finset.measurable_restrict E) measurable_sh, hc,
    ← Measure.map_map (measurable_of_countable r) (Finset.measurable_restrict E'), ν4_lim E',
    PE_eq hE', Q, Measure.map_map (measurable_of_countable _) (measurable_of_countable _), hr]
  rfl

/-- **Properness**: adjacent colours differ almost surely. -/
theorem ν4_proper : ∀ᵐ ω ∂ν4, ∀ i : ℤ, ω i ≠ ω (i + 1) := by
  refine ae_all_iff.2 fun i => ?_
  have hS : {ω : ℤ → Fin 4 | ω i = ω (i + 1)} = W i 2 ⁻¹' {f | f 0 = f 1} := by
    ext ω; simp [W]
  have h0 : μ 2 {f | f 0 = f 1} = 0 := by
    rw [μ_apply]
    refine Finset.sum_eq_zero fun f _ => ?_
    by_cases hf : f 0 = f 1
    · have : List.ofFn f = [] ++ f 0 :: f 0 :: [] := by
        rw [List.ofFn_succ, List.ofFn_succ]; simp [hf]
      rw [this, P_dup]; simp
    · simp [Set.indicator, hf]
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [hS, ← Measure.map_apply (measurable_W i 2) (Set.toFinite _).measurableSet, ν4_map_W, h0]

/-! ## One-dependence of cylinder probabilities -/

/-- The cylinder of the colourings agreeing with `σ` on `S`. -/
def cyl (S : Finset ℤ) (σ : ℤ → Fin 4) : Set (ℤ → Fin 4) := {ω | ∀ s ∈ S, ω s = σ s}

@[simp] lemma cyl_empty (σ : ℤ → Fin 4) : cyl ∅ σ = Set.univ := by ext; simp [cyl]

lemma ν4_cyl_win (S : Finset ℤ) (σ : ℤ → Fin 4) (a : ℤ) (n : ℕ)
    (h : ∀ s ∈ S, a ≤ s ∧ s < a + n) :
    ν4 (cyl S σ) = μ n {f | ∀ j : Fin n, a + j ∈ S → f j = σ (a + j)} := by
  have hc : cyl S σ = W a n ⁻¹' {f | ∀ j : Fin n, a + j ∈ S → f j = σ (a + j)} := by
    ext ω
    simp only [cyl, W, Set.mem_ofPred_eq, Set.mem_preimage]
    refine ⟨fun hω j hj => hω _ hj, fun hω s hs => ?_⟩
    have := h s hs
    have e : a + ((⟨(s - a).toNat, by omega⟩ : Fin n) : ℕ) = s := by simp; omega
    have := hω ⟨(s - a).toNat, by omega⟩ (by rw [e]; exact hs)
    rwa [e] at this
  rw [hc, ← Measure.map_apply (measurable_W a n) (Set.toFinite _).measurableSet, ν4_map_W]

/-- **Splitting**: cylinders on sets at distance at least two are independent. -/
theorem ν4_split (E₁ E₂ : Finset ℤ) (σ : ℤ → Fin 4) (h : ∀ x ∈ E₁, ∀ y ∈ E₂, x + 2 ≤ y) :
    ν4 (cyl (E₁ ∪ E₂) σ) = ν4 (cyl E₁ σ) * ν4 (cyl E₂ σ) := by
  rcases E₁.eq_empty_or_nonempty with rfl | h₁
  · simp
  rcases E₂.eq_empty_or_nonempty with rfl | h₂
  · simp
  set a := E₁.min' h₁
  set b₁ := E₁.max' h₁
  set a₂ := E₂.min' h₂
  set b₂ := E₂.max' h₂
  have hab : a ≤ b₁ := E₁.min'_le _ (E₁.max'_mem h₁)
  have hab₂ : a₂ ≤ b₂ := E₂.min'_le _ (E₂.max'_mem h₂)
  have hgap : b₁ + 2 ≤ a₂ := h _ (E₁.max'_mem h₁) _ (E₂.min'_mem h₂)
  set n₁ := (b₁ - a + 1).toNat
  set t := (a₂ - b₁ - 2).toNat
  set n₂ := (b₂ - a₂ + 1).toNat
  have hn₁ : a + n₁ = b₁ + 1 := by omega
  have ht : a + n₁ + (t + 1 : ℕ) = a₂ := by omega
  have hn₂ : a₂ + n₂ = b₂ + 1 := by omega
  have hS₁ : ∀ s ∈ E₁, a ≤ s ∧ s < a + n₁ := fun s hs =>
    ⟨E₁.min'_le s hs, by have := E₁.le_max' s hs; omega⟩
  have hS₂ : ∀ s ∈ E₂, a₂ ≤ s ∧ s < a₂ + n₂ := fun s hs =>
    ⟨E₂.min'_le s hs, by have := E₂.le_max' s hs; omega⟩
  have hS : ∀ s ∈ E₁ ∪ E₂, a ≤ s ∧ s < a + (n₁ + (t + 1) + n₂ : ℕ) := fun s hs => by
    rcases Finset.mem_union.1 hs with hs | hs
    · have := hS₁ s hs; push_cast; omega
    · have := hS₂ s hs; push_cast; omega
  rw [ν4_cyl_win _ σ a _ hS, ν4_cyl_win E₁ σ a n₁ hS₁, ν4_cyl_win E₂ σ a₂ n₂ hS₂,
    ← Measure.prod_prod, ← μ_map_pair n₁ t n₂,
    Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet]
  congr 1
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, win]
  constructor
  · intro hf
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have e : a + ((⟨0 + j, by omega⟩ : Fin (n₁ + (t + 1) + n₂)) : ℕ) = a + j := by simp
      have := hf ⟨0 + j, by omega⟩ (by rw [e]; exact Finset.mem_union_left _ hj)
      rwa [e] at this
    · have e : a + ((⟨n₁ + (t + 1) + j, by omega⟩ : Fin (n₁ + (t + 1) + n₂)) : ℕ) = a₂ + j := by
        simp only; push_cast; omega
      have := hf ⟨n₁ + (t + 1) + j, by omega⟩ (by rw [e]; exact Finset.mem_union_right _ hj)
      rwa [e] at this
  · rintro ⟨hf₁, hf₂⟩ j hj
    rcases Finset.mem_union.1 hj with hj | hj
    · have hjn : (j : ℕ) < n₁ := by have := hS₁ _ hj; omega
      have := hf₁ ⟨j, hjn⟩ hj
      simpa using this
    · have hjn : n₁ + (t + 1) ≤ (j : ℕ) := by have := hS₂ _ hj; omega
      have e : a₂ + ((⟨(j : ℕ) - (n₁ + (t + 1)), by omega⟩ : Fin n₂) : ℕ) = a + j := by
        simp only; push_cast [Nat.cast_sub hjn]; omega
      have := hf₂ ⟨(j : ℕ) - (n₁ + (t + 1)), by omega⟩ (by rw [e]; exact hj)
      rw [e] at this
      convert this using 2
      ext; simp only; omega

/-- **One-dependence**: cylinder probabilities factorise over sets at distance at least two. -/
theorem ν4_indep_cyl (σ : ℤ → Fin 4) : ∀ (n : ℕ) (A B : Finset ℤ), (A ∪ B).card = n →
    (∀ a ∈ A, ∀ b ∈ B, 1 < |a - b|) → ν4 (cyl (A ∪ B) σ) = ν4 (cyl A σ) * ν4 (cyl B σ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  -- the case where the largest point lies in `B`
  have key : ∀ A B : Finset ℤ, (hA : A.Nonempty) → (hB : B.Nonempty) → (A ∪ B).card = n →
      (∀ a ∈ A, ∀ b ∈ B, 1 < |a - b|) → A.max' hA < B.max' hB →
      ν4 (cyl (A ∪ B) σ) = ν4 (cyl A σ) * ν4 (cyl B σ) := by
    intro A B hA hB hn hsep hmax
    set m := A.max' hA
    set B₁ := B.filter (· < m)
    set B₂ := B.filter (m < ·)
    have hB12 : B = B₁ ∪ B₂ := by
      ext b
      simp only [B₁, B₂, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hb
        have := hsep m (A.max'_mem hA) b hb
        rcases lt_trichotomy b m with h | h | h
        · exact Or.inl ⟨hb, h⟩
        · subst h; simp at this
        · exact Or.inr ⟨hb, h⟩
      · rintro (⟨hb, -⟩ | ⟨hb, -⟩) <;> exact hb
    have hB₂2 : ∀ y ∈ B₂, m + 2 ≤ y := fun y hy => by
      obtain ⟨hy, hmy⟩ := Finset.mem_filter.1 hy
      have := hsep m (A.max'_mem hA) y hy
      rw [abs_sub_comm, abs_of_pos (by omega)] at this
      omega
    have hsplit : ∀ x ∈ A ∪ B₁, ∀ y ∈ B₂, x + 2 ≤ y := fun x hx y hy => by
      have := hB₂2 y hy
      rcases Finset.mem_union.1 hx with hx | hx
      · have := A.le_max' x hx; omega
      · have := (Finset.mem_filter.1 hx).2; omega
    have hB1B2 : ∀ x ∈ B₁, ∀ y ∈ B₂, x + 2 ≤ y := fun x hx y hy =>
      hsplit x (Finset.mem_union_right _ hx) y hy
    have hU : A ∪ B = (A ∪ B₁) ∪ B₂ := by rw [hB12, Finset.union_assoc]
    have hmemB₂ : B.max' hB ∈ B₂ := Finset.mem_filter.2 ⟨B.max'_mem hB, hmax⟩
    have hcard : (A ∪ B₁).card < n := by
      rw [← hn]
      refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
      · rw [hU]; exact Finset.mem_union_left _ hx
      · have := hsub (Finset.mem_union_right _ (B.max'_mem hB))
        have h2 := hsplit _ this _ hmemB₂
        omega
    rw [hU, ν4_split _ _ σ hsplit,
      ih _ hcard A B₁ rfl fun a ha b hb => hsep a ha b (Finset.mem_filter.1 hb).1,
      hB12, ν4_split _ _ σ hB1B2, mul_assoc]
  intro A B hn hsep
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  rcases lt_or_gt_of_ne (show A.max' hA ≠ B.max' hB from fun h => by
    have := hsep _ (A.max'_mem hA) _ (B.max'_mem hB); rw [h] at this; simp at this) with h | h
  · exact key A B hA hB hn hsep h
  · rw [Finset.union_comm, mul_comm]
    exact key B A hB hA (by rw [Finset.union_comm]; exact hn)
      (fun b hb a ha => by rw [abs_sub_comm]; exact hsep a ha b hb) h

/-- **Holroyd–Liggett**: a stationary, proper, one-dependent four-colouring of `ℤ`. -/
theorem hl_four : ∃ ν : Measure (ℤ → Fin 4), IsProbabilityMeasure ν ∧ MeasurePreserving sh ν ν ∧
    (∀ᵐ ω ∂ν, ∀ i : ℤ, ω i ≠ ω (i + 1)) ∧
    ∀ (A B : Finset ℤ) (σ : ℤ → Fin 4), (∀ a ∈ A, ∀ b ∈ B, 1 < |a - b|) →
      ν (cyl (A ∪ B) σ) = ν (cyl A σ) * ν (cyl B σ) :=
  ⟨ν4, inferInstance, ν4_stationary, ν4_proper,
    fun A B σ hsep => ν4_indep_cyl σ _ A B rfl hsep⟩

end FiniteOrderMixing.HL
