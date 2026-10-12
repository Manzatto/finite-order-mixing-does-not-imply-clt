import FiniteOrderMixing.Construction

/-!
# Stationarity of the nested marker sets (Lemma `lem:stationarity-geometry`)

Translating the marker sets by `m` amounts to re-anchoring the enumeration of the old markers at
every level, i.e. to shifting the level-`(k+1)` colouring by `c_k = idx (𝓜_k) m`, a quantity
determined by the previous levels.  The map `tau L m` performs these shifts; it preserves the
product law of the colourings (a skew-product argument using the stationarity and the
independence of the colourings), and `Mh ∘ tau = shiftH m ∘ Mh`.
-/

open MeasureTheory ProbabilityTheory Finset

namespace FiniteOrderMixing

variable {L q : ℕ}

/-- The law of the independent colourings of all levels. -/
noncomputable def POmega (PV : Measure (ℤ → Fin q)) [IsProbabilityMeasure PV] :
    Measure (ℕ → ℤ → Fin q) :=
  Measure.infinitePi fun _ : ℕ => PV

instance (PV : Measure (ℤ → Fin q)) [IsProbabilityMeasure PV] :
    IsProbabilityMeasure (POmega PV) := by
  unfold POmega; infer_instance

@[fun_prop]
lemma measurable_shiftZ (z : ℤ) : Measurable (shiftZ (q := q) z) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

lemma shiftZ_add (a b : ℤ) (v : ℤ → Fin q) : shiftZ b (shiftZ a v) = shiftZ (a + b) v := by
  funext i; simp only [shiftZ]; congr 1; ring

lemma shiftZ_zero : shiftZ (q := q) 0 = id := by funext v i; simp [shiftZ]

/-- All integer shifts preserve the law of the colouring. -/
lemma shiftZ_mp {PV : Measure (ℤ → Fin q)} (hstat : MeasurePreserving (shiftZ 1) PV PV)
    (z : ℤ) : MeasurePreserving (shiftZ z) PV PV := by
  have hneg : MeasurePreserving (shiftZ (-1)) PV PV := by
    refine ⟨measurable_shiftZ _, ?_⟩
    conv_lhs => rw [← hstat.map_eq]
    rw [Measure.map_map (measurable_shiftZ _) (measurable_shiftZ _)]
    have : shiftZ (-1) ∘ shiftZ 1 = (id : (ℤ → Fin q) → _) :=
      funext fun v => by simp [Function.comp, shiftZ_add, shiftZ_zero]
    rw [this, Measure.map_id]
  refine Int.induction_on z ?_ ?_ ?_
  · rw [shiftZ_zero]; exact MeasurePreserving.id PV
  · intro n ih
    have : shiftZ ((n : ℤ) + 1) = shiftZ 1 ∘ shiftZ (q := q) (n : ℤ) :=
      funext fun v => (shiftZ_add _ _ v).symm
    rw [this]; exact hstat.comp ih
  · intro n ih
    have : shiftZ (-(n : ℤ) - 1) = shiftZ (-1) ∘ shiftZ (q := q) (-(n : ℤ)) :=
      funext fun v => by rw [Function.comp, shiftZ_add]; ring_nf
    rw [this]; exact hneg.comp ih

variable (L) in
/-- The level-`k` markers depend only on the colourings of levels `≤ k`. -/
lemma mk_congr {ω ω' : ℕ → ℤ → Fin q} (k : ℕ) (h : ∀ j ≤ k, ω j = ω' j) :
    mk L ω k = mk L ω' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [mk]
    rw [ih fun j hj => h j (by omega), h (k + 1) le_rfl]

variable (L) in
/-- The re-anchoring shifts. -/
def cc (m : ℤ) (ω : ℕ → ℤ → Fin q) : ℕ → ℤ
  | 0 => 0
  | k + 1 => idx (mk L ω k) m

variable (L) in
/-- The re-anchoring map on the colourings. -/
def tau (m : ℤ) (ω : ℕ → ℤ → Fin q) : ℕ → ℤ → Fin q := fun n => shiftZ (cc L m ω n) (ω n)

lemma mk_tau (m : ℤ) (ω : ℕ → ℤ → Fin q) (k : ℕ) :
    mk L (tau L m ω) k = fun x => mk L ω k (x + m) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    simp only [mk]
    rw [ih]
    exact sel_shift (mk L ω k) (ω (k + 1)) (sc L (k + 1)) m x

lemma Mh_tau (m : ℤ) (ω : ℕ → ℤ → Fin q) : Mh L (tau L m ω) = shiftH m (Mh L ω) := by
  funext k j; simp [Mh, shiftH, mk_tau]

lemma measurable_idx (m : ℤ) : Measurable (fun o : ℤ → Bool => idx o m) := by
  classical
  let W := Finset.Icc (-|m|) |m|
  let r : (ℤ → Bool) → (W → Bool) := fun o i => o i
  let ext : (W → Bool) → (ℤ → Bool) := fun y x => if h : x ∈ W then y ⟨x, h⟩ else false
  have hr : Measurable r := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  have : (fun o : ℤ → Bool => idx o m) = (fun y => idx (ext y) m) ∘ r := by
    funext o
    refine idx_congr fun x hx => ?_
    have : x ∈ W := by simp only [W, Finset.mem_Icc]; rw [abs_le] at hx; exact hx
    simp [ext, r, this]
  rw [this]; exact (measurable_of_countable _).comp hr

lemma measurable_cc (hq : 1 ≤ q) (m : ℤ) (n : ℕ) :
    Measurable (fun ω : ℕ → ℤ → Fin q => cc L m ω n) := by
  cases n with
  | zero => exact measurable_const
  | succ k => exact (measurable_idx m).comp (measurable_mk L hq k)

lemma measurable_shiftApply : Measurable (fun p : ℤ × (ℤ → Fin q) => shiftZ p.1 p.2) :=
  measurable_pi_iff.mpr fun i =>
    measurable_from_prod_countable_right fun z => measurable_pi_apply (i + z)

lemma measurable_tau (hq : 1 ≤ q) (m : ℤ) : Measurable (tau (q := q) L m) :=
  measurable_pi_iff.mpr fun n =>
    measurable_shiftApply.comp ((measurable_cc hq m n).prodMk (measurable_pi_apply n))

section MP

variable {PV : Measure (ℤ → Fin q)} [IsProbabilityMeasure PV] (hC : ColouringLaw L q PV)
  (hq : 1 ≤ q)
include hC hq

omit hC hq in
/-- The restriction to the first `n` levels and the `n`-th level are independent. -/
lemma map_pair_eq_prod (n : ℕ) :
    (POmega PV).map (fun ω => ((fun i : Finset.range n => ω i), ω n)) =
      ((POmega PV).map fun ω (i : Finset.range n) => ω i).prod PV := by
  have hiid : iIndepFun (fun i (ω : ℕ → ℤ → Fin q) => ω i) (POmega PV) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => PV) (X := fun _ v => v) fun _ => measurable_id
  have h2 := hiid.indepFun_finset (Finset.range n) {n} (by simp)
    fun i => measurable_pi_apply i
  have h3 := h2.comp (measurable_id) (measurable_pi_apply (⟨n, Finset.mem_singleton_self n⟩ :
    ({n} : Finset ℕ)))
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_iff.mpr fun _ =>
    measurable_pi_apply _).aemeasurable (measurable_pi_apply n).aemeasurable).1 h3]
  congr 1
  exact Measure.infinitePi_map_eval _ n

/-- The re-anchoring map preserves the law of the colourings. -/
theorem tau_mp (m : ℤ) : MeasurePreserving (tau L m) (POmega PV) (POmega PV) := by
  classical
  refine ⟨measurable_tau hq m, ?_⟩
  set X := ℤ → Fin q
  set v0 : X := fun _ => ⟨0, hq⟩
  -- the statement for boxes over `range n`
  have Q : ∀ (n : ℕ) (t : ℕ → Set X), (∀ i, MeasurableSet (t i)) →
      POmega PV ((tau L m) ⁻¹' Set.pi ↑(Finset.range n) t) = ∏ i ∈ Finset.range n, PV (t i) := by
    intro n
    induction n with
    | zero => intro t _; simp
    | succ n ih =>
      intro t ht
      set R : (ℕ → X) → (Finset.range n → X) := fun ω i => ω i
      have hR : Measurable R := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
      set ext : (Finset.range n → X) → (ℕ → X) :=
        fun x j => if h : j < n then x ⟨j, Finset.mem_range.2 h⟩ else v0
      have hext : Measurable ext := measurable_pi_iff.mpr fun j => by
        by_cases h : j < n
        · simp only [ext, h, dite_true]; exact measurable_pi_apply _
        · simp only [ext, h, dite_false]; exact measurable_const
      have hag : ∀ ω j, j < n → ext (R ω) j = ω j := fun ω j hj => by simp [ext, R, hj]
      have hcc : ∀ ω (i : ℕ), i ≤ n → cc L m ω i = cc L m (ext (R ω)) i := by
        intro ω i hi
        cases i with
        | zero => rfl
        | succ k =>
          simp only [cc]
          rw [mk_congr L k fun j hj => (hag ω j (by omega)).symm]
      have htau : ∀ ω i, i < n → tau L m ω i = tau L m (ext (R ω)) i := fun ω i hi => by
        simp only [tau]; rw [hcc ω i hi.le, hag ω i hi]
      set A := {x : Finset.range n → X | ∀ i ∈ Finset.range n, tau L m (ext x) i ∈ t i}
      have hA : MeasurableSet A := by
        have : A = ⋂ i ∈ Finset.range n, (fun x => tau L m (ext x) i) ⁻¹' t i := by
          ext x; simp [A]
        rw [this]
        exact Finset.measurableSet_biInter _ fun i _ =>
          ((measurable_pi_apply i).comp ((measurable_tau hq m).comp hext)) (ht i)
      have hRA : R ⁻¹' A = (tau L m) ⁻¹' Set.pi ↑(Finset.range n) t := by
        ext ω
        simp only [A, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_range,
          Set.mem_Iio, Finset.mem_range]
        exact forall₂_congr fun i hi => by rw [← htau ω i hi]
      set c' : (Finset.range n → X) → ℤ := fun x => cc L m (ext x) n
      have hc' : Measurable c' := (measurable_cc hq m n).comp hext
      set skew : (Finset.range n → X) × X → (Finset.range n → X) × X :=
        fun p => (p.1, shiftZ (c' p.1) p.2)
      have hskew : MeasurePreserving skew (((POmega PV).map R).prod PV)
          (((POmega PV).map R).prod PV) :=
        MeasurePreserving.skew_product (f := id) (g := fun x v => shiftZ (c' x) v)
          (MeasurePreserving.id _)
          (measurable_shiftApply.comp ((hc'.comp measurable_fst).prodMk measurable_snd))
          (Filter.Eventually.of_forall fun x => (shiftZ_mp hC.stat (c' x)).map_eq)
      have hset : (tau L m) ⁻¹' Set.pi ↑(Finset.range (n + 1)) t =
          (fun ω => (R ω, ω n)) ⁻¹' (skew ⁻¹' (A ×ˢ t n)) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_prod,
          skew, A, Set.mem_ofPred_eq, Finset.mem_range]
        constructor
        · intro h
          refine ⟨fun i hi => ?_, ?_⟩
          · rw [← htau ω i hi]; exact h i (by omega)
          · have := h n (by omega)
            simp only [tau] at this
            rw [hcc ω n le_rfl] at this
            exact this
        · rintro ⟨h1, h2⟩ i hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [htau ω i hi]; exact h1 i hi
          · simp only [tau]; rw [hcc ω i le_rfl]; exact h2
      have hpair : Measurable fun ω : ℕ → X => (R ω, ω n) := hR.prodMk (measurable_pi_apply n)
      rw [hset, ← Measure.map_apply hpair (hskew.measurable (hA.prod (ht n))),
        map_pair_eq_prod n, hskew.measure_preimage (hA.prod (ht n)).nullMeasurableSet,
        Measure.prod_prod, Measure.map_apply hR hA, hRA, ih t ht, Finset.prod_range_succ]
  show (POmega PV).map (tau L m) = Measure.infinitePi fun _ => PV
  refine Measure.eq_infinitePi (fun _ => PV) fun s t ht => ?_
  set n := s.sup id + 1
  have hsn : s ⊆ Finset.range n := fun i hi =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  set t' : ℕ → Set X := fun i => if i ∈ s then t i else Set.univ
  have ht' : ∀ i, MeasurableSet (t' i) := fun i => by
    simp only [t']; split_ifs
    · exact ht i
    · exact MeasurableSet.univ
  have hpi : Set.pi ↑s t = Set.pi ↑(Finset.range n) t' := by
    ext ω
    simp only [Set.mem_pi, Finset.mem_coe, t']
    constructor
    · intro h i _; split_ifs with his
      · exact h i his
      · trivial
    · intro h i hi; have := h i (hsn hi); rwa [ite_eq_left hi] at this
  rw [Measure.map_apply (measurable_tau hq m) (MeasurableSet.pi s.countable_toSet fun i _ => ht i),
    hpi, Q n t' ht']
  rw [← Finset.prod_subset hsn fun i _ his => by simp [t', his]]
  exact Finset.prod_congr rfl fun i hi => by simp [t', hi]

end MP

end FiniteOrderMixing
