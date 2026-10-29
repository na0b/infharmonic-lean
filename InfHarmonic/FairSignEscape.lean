module

public import InfHarmonic.Preamble
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The fair-sign space of the proof of Proposition 6.7, part 1.  For every
block length `q ≥ 1` there are a probability space, a filtration `𝒢`, a
sequence `ξ` of fair signs (each `±1` pointwise, `𝒢 (n+1)`-measurable and
conditionally centred on `𝒢 n`), and an index `G` such that at every point of
the space the `q` signs `ξ (q G), …, ξ (q G + q - 1)` are all `+1`, with `G`
integrable and `E G ≤ 2 ^ q`. -/
theorem FairSignEscape (q : ℕ) :
    ∃ (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (𝒢 : Filtration ℕ m0)
      (ξ : ℕ → Ω → ℝ) (G : Ω → ℕ),
      μ Set.univ = 1 ∧
      (∀ n ω, ξ n ω = 1 ∨ ξ n ω = -1) ∧
      (∀ n, StronglyMeasurable[𝒢 (n + 1)] (ξ n)) ∧
      (∀ n, μ[ξ n | 𝒢 n] =ᵐ[μ] 0) ∧
      (∀ ω, ∀ i < q, ξ (q * G ω + i) ω = 1) ∧
      Integrable (fun ω => (G ω : ℝ)) μ ∧
      ∫ ω, (G ω : ℝ) ∂μ ≤ 2 ^ q := by
  classical
  -- ### the fair coin and the product measure
  set cn : Measure Bool :=
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac true + (2 : ℝ≥0∞)⁻¹ • Measure.dirac false with hcn
  have hcntrue : cn {true} = (2 : ℝ≥0∞)⁻¹ := by
    simp [hcn, Measure.coe_add, Measure.coe_smul]
  have hcnfalse : cn {false} = (2 : ℝ≥0∞)⁻¹ := by
    simp [hcn, Measure.coe_add, Measure.coe_smul]
  have hcnprob : IsProbabilityMeasure cn := by
    constructor
    rw [hcn, Measure.coe_add, Pi.add_apply, Measure.coe_smul, Measure.coe_smul, Pi.smul_apply,
      Pi.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      Measure.dirac_apply_of_mem (Set.mem_univ _)]
    simp [ENNReal.inv_two_add_inv_two]
  have hall : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ => cn) i) := fun _ => hcnprob
  set P : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => cn) with hP
  have hPprob : IsProbabilityMeasure P := by rw [hP]; infer_instance
  -- ### the signs on the product space, shifted by one coordinate
  set sg : ℕ → Bool → ℝ := fun k b => if k = 0 then 0 else (if b then 1 else -1) with hsg
  set Z : ℕ → (ℕ → Bool) → ℝ := fun k ω => sg k (ω k) with hZ
  have hmb : ∀ f : Bool → ℝ, Measurable f := fun _ => Measurable.of_discrete
  have hZmeas : ∀ k, Measurable (Z k) := fun k => (hmb (sg k)).comp (measurable_pi_apply k)
  have hZsm : ∀ k, StronglyMeasurable (Z k) := fun k => (hZmeas k).stronglyMeasurable
  have hZindep : iIndepFun Z P := by
    rw [hZ, hP]
    exact iIndepFun_infinitePi (fun k => hmb (sg k))
  -- ### the escape blocks
  set blk : ℕ → Finset ℕ := fun m => (Finset.range q).image (fun i => q * m + i + 1) with hblk
  have hcard : ∀ m, (blk m).card = q := by
    intro m
    rw [hblk, Finset.card_image_of_injective _ (fun a b hab => by omega), Finset.card_range]
  set A : ℕ → Set (ℕ → Bool) := fun m => {ω | ∀ i < q, ω (q * m + i + 1) = true} with hA
  have hApi : ∀ m, A m = Set.pi (blk m : Set ℕ) (fun _ => ({true} : Set Bool)) := by
    intro m
    have hmem : ∀ k : ℕ, k ∈ (blk m : Set ℕ) ↔ ∃ i < q, q * m + i + 1 = k := by
      intro k
      rw [hblk]
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    ext ω
    rw [hA]
    constructor
    · intro h
      refine Set.mem_pi.2 (fun k hk => ?_)
      obtain ⟨i, hi, hik⟩ := (hmem k).1 hk
      rw [← hik]
      exact Set.mem_singleton_iff.2 (h i hi)
    · intro h i hi
      have hk : (q * m + i + 1) ∈ (blk m : Set ℕ) := (hmem _).2 ⟨i, hi, rfl⟩
      exact Set.mem_singleton_iff.1 (Set.mem_pi.1 h _ hk)
  have hAmeas : ∀ m, MeasurableSet (A m) := by
    intro m
    rw [hApi m]
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => measurableSet_singleton true)
  set p : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ q with hpdef
  have hAP : ∀ m, P (A m) = p := by
    intro m
    rw [hApi m, hP, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton true),
      Finset.prod_congr rfl (fun i _ => hcntrue), Finset.prod_const, hcard m, hpdef]
  -- ### the coordinate σ-algebras and their independence
  set mc : ℕ → MeasurableSpace (ℕ → Bool) :=
    fun k => MeasurableSpace.comap (fun ω : ℕ → Bool => ω k) inferInstance with hmc
  have hmcle : ∀ k, mc k ≤ (inferInstance : MeasurableSpace (ℕ → Bool)) := by
    intro k
    rw [hmc]
    exact (measurable_pi_apply k).comap_le
  have hcind : iIndep mc P := by
    rw [hmc, hP]
    exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hcoordmeas : ∀ k : ℕ, MeasurableSet[mc k] {ω : ℕ → Bool | ω k = true} := by
    intro k
    rw [hmc]
    exact ⟨{true}, measurableSet_singleton true, rfl⟩
  have hpast : ∀ n : ℕ,
      Indep (⨆ k ∈ {k : ℕ | k ≤ n}, mc k) (⨆ k ∈ {k : ℕ | n < k}, mc k) P := by
    intro n
    refine indep_iSup_of_disjoint hmcle hcind ?_
    rw [Set.disjoint_left]
    intro k hk hk'
    have hk1 : k ≤ n := hk
    have hk2 : n < k := hk'
    omega
  -- ### the escape estimate
  set E : ℕ → Set (ℕ → Bool) :=
    fun m => {ω | ∀ j < m, ¬ (∀ i < q, ω (q * j + i + 1) = true)} with hE
  have hEsucc : ∀ m, E (m + 1) = E m ∩ (A m)ᶜ := by
    intro m
    ext ω
    rw [hE, hA]
    constructor
    · intro h
      exact ⟨fun j hj => h j (by omega), fun hc => h m (by omega) hc⟩
    · intro h j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
      · exact h.1 j hj'
      · rw [hj']; exact h.2
  have hAfut : ∀ m : ℕ, MeasurableSet[⨆ k ∈ {k : ℕ | q * m < k}, mc k] (A m) := by
    intro m
    have h1 : A m = ⋂ i ∈ Set.Iio q, {ω : ℕ → Bool | ω (q * m + i + 1) = true} := by
      ext ω
      rw [hA]
      constructor
      · intro h
        exact Set.mem_iInter₂.2 (fun i hi => h i hi)
      · intro h i hi
        exact Set.mem_iInter₂.1 h i hi
    rw [h1]
    refine MeasurableSet.biInter (Set.to_countable _) (fun i _ => ?_)
    have hle : mc (q * m + i + 1) ≤ ⨆ k ∈ {k : ℕ | q * m < k}, mc k :=
      le_iSup₂ (f := fun k (_ : k ∈ {k : ℕ | q * m < k}) => mc k) (q * m + i + 1)
        (show q * m < q * m + i + 1 by omega)
    exact hle _ (hcoordmeas _)
  have hEpast : ∀ m : ℕ, MeasurableSet[⨆ k ∈ {k : ℕ | k ≤ q * m}, mc k] (E m) := by
    intro m
    have h1 : E m = ⋂ j ∈ Set.Iio m, (A j)ᶜ := by
      ext ω
      rw [hE]
      constructor
      · intro h
        exact Set.mem_iInter₂.2 (fun j hj => h j hj)
      · intro h j hj
        exact Set.mem_iInter₂.1 h j hj
    rw [h1]
    refine MeasurableSet.biInter (Set.to_countable _) (fun j hj => ?_)
    refine MeasurableSet.compl ?_
    have h2 : A j = ⋂ i ∈ Set.Iio q, {ω : ℕ → Bool | ω (q * j + i + 1) = true} := by
      ext ω
      rw [hA]
      constructor
      · intro h
        exact Set.mem_iInter₂.2 (fun i hi => h i hi)
      · intro h i hi
        exact Set.mem_iInter₂.1 h i hi
    rw [h2]
    refine MeasurableSet.biInter (Set.to_countable _) (fun i hi => ?_)
    have hjm : j < m := hj
    have hiq : i < q := hi
    have hle : mc (q * j + i + 1) ≤ ⨆ k ∈ {k : ℕ | k ≤ q * m}, mc k :=
      le_iSup₂ (f := fun k (_ : k ∈ {k : ℕ | k ≤ q * m}) => mc k) (q * j + i + 1)
        (show q * j + i + 1 ≤ q * m by
          have : q * j + q ≤ q * m := by
            have : q * (j + 1) ≤ q * m := Nat.mul_le_mul_left q (by omega)
            simpa [Nat.mul_succ] using this
          omega)
    exact hle _ (hcoordmeas _)
  have hp1 : p ≤ 1 := by
    rw [hpdef]
    exact pow_le_one₀ (by norm_num) (by
      rw [ENNReal.inv_le_one]
      exact one_le_two)
  have hACP : ∀ m, P ((A m)ᶜ) = 1 - p := by
    intro m
    rw [prob_compl_eq_one_sub (hAmeas m), hAP m]
  have hEP : ∀ m : ℕ, P (E m) = (1 - p) ^ m := by
    intro m
    induction m with
    | zero =>
      have h0 : E 0 = Set.univ := by
        ext ω
        rw [hE]
        simp
      rw [h0, pow_zero, measure_univ]
    | succ m ih =>
      rw [hEsucc m]
      have hind := ((hpast (q * m)).indepSet_of_measurableSet (hEpast m)
        (MeasurableSet.compl (hAfut m))).measure_inter_eq_mul
      rw [hind, ih, hACP m, pow_succ]
  -- ### the full-measure escape set
  set Sset : Set (ℕ → Bool) := {ω | ∃ m, ∀ i < q, ω (q * m + i + 1) = true} with hSs
  have hSmeas : MeasurableSet Sset := by
    have h1 : Sset = ⋃ m, A m := by
      ext ω
      rw [hSs, hA]
      constructor
      · intro h
        obtain ⟨m, hm⟩ := h
        exact Set.mem_iUnion.2 ⟨m, hm⟩
      · intro h
        obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h
        exact ⟨m, hm⟩
    rw [h1]
    exact MeasurableSet.iUnion hAmeas
  have hpne : p ≠ 0 := by
    rw [hpdef]
    exact pow_ne_zero _ (by simp)
  have h1p : 1 - p < 1 := by
    refine ENNReal.sub_lt_self (by simp) (by simp) hpne
  have hSc : P Ssetᶜ = 0 := by
    have hsub : ∀ m, Ssetᶜ ⊆ E m := by
      intro m ω hω
      rw [hE]
      intro j _ hj
      exact hω ⟨j, hj⟩
    have h1 : ∀ m, P Ssetᶜ ≤ (1 - p) ^ m := by
      intro m
      rw [← hEP m]
      exact measure_mono (hsub m)
    have h2 : Tendsto (fun m : ℕ => (1 - p) ^ m) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h1p
    exact le_antisymm (ge_of_tendsto h2 (Filter.Eventually.of_forall h1)) (by simp)
  have hSP : P Sset = 1 := (prob_compl_eq_zero_iff hSmeas).1 hSc
  have hSae : ∀ᵐ ω ∂P, ω ∈ Sset := by
    rw [ae_iff]
    exact hSc
  have hEmeas : ∀ m, MeasurableSet (E m) := by
    intro m
    exact (iSup₂_le (fun k (_ : k ∈ {k : ℕ | k ≤ q * m}) => hmcle k)) _ (hEpast m)
  -- ### the restricted space
  set μ' : Measure {ω : ℕ → Bool // ω ∈ Sset} := Measure.comap Subtype.val P with hμ'
  have hmv : ∀ B : Set (ℕ → Bool), MeasurableSet B → μ' (Subtype.val ⁻¹' B) = P B := by
    intro B hB
    rw [hμ', (MeasurableEmbedding.subtype_coe hSmeas).comap_apply P, Subtype.image_preimage_coe]
    refine measure_congr ?_
    rw [Filter.eventuallyEq_set]
    filter_upwards [hSae] with ω hω
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨hω, h⟩
  have hμ'univ : μ' Set.univ = 1 := by
    rw [hμ', (MeasurableEmbedding.subtype_coe hSmeas).comap_apply P, Subtype.coe_image_univ]
    exact hSP
  have hμ'prob : IsProbabilityMeasure μ' := ⟨hμ'univ⟩
  -- ### the signs and the filtration on the restricted space
  set ζ : ℕ → {ω : ℕ → Bool // ω ∈ Sset} → ℝ := fun k ω => Z k ω.val with hζ
  have hζsm : ∀ k, StronglyMeasurable (ζ k) := by
    intro k
    rw [hζ]
    exact ((hZmeas k).comp measurable_subtype_coe).stronglyMeasurable
  set FF : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Bool)) :=
    Filtration.natural Z hZsm with hFF
  set FFs : Filtration ℕ (inferInstance : MeasurableSpace {ω : ℕ → Bool // ω ∈ Sset}) :=
    Filtration.natural ζ hζsm with hFFs
  have hζcomap : ∀ k : ℕ, MeasurableSpace.comap (ζ k) (inferInstance : MeasurableSpace ℝ)
      = MeasurableSpace.comap (Subtype.val : {ω : ℕ → Bool // ω ∈ Sset} → (ℕ → Bool))
        (MeasurableSpace.comap (Z k) inferInstance) := by
    intro k
    rw [MeasurableSpace.comap_comp, hζ]
    rfl
  have hFFcomap : ∀ n : ℕ, (FFs n : MeasurableSpace {ω : ℕ → Bool // ω ∈ Sset})
      = MeasurableSpace.comap Subtype.val (FF n) := by
    intro n
    rw [hFFs, hFF]
    show (⨆ k ≤ n, MeasurableSpace.comap (ζ k) (inferInstance : MeasurableSpace ℝ))
        = MeasurableSpace.comap Subtype.val
          (⨆ k ≤ n, MeasurableSpace.comap (Z k) (inferInstance : MeasurableSpace ℝ))
    rw [MeasurableSpace.comap_iSup]
    refine iSup_congr (fun k => ?_)
    rw [MeasurableSpace.comap_iSup]
    exact iSup_congr (fun _ => hζcomap k)
  -- ### the signs are conditionally centred
  have hζint : ∀ k : ℕ, ∫ ω, ζ (k + 1) ω ∂μ' = 0 := by
    intro k
    have h1 : ∫ ω, ζ (k + 1) ω ∂μ' = ∫ ω in Sset, Z (k + 1) ω ∂P := by
      rw [hζ, hμ']
      exact integral_subtype_comap hSmeas (Z (k + 1))
    have h2 : ∫ ω in Sset, Z (k + 1) ω ∂P = ∫ ω, Z (k + 1) ω ∂P := by
      rw [setIntegral_congr_set (ae_eq_univ.2 hSc), setIntegral_univ]
    have hmap : P.map (fun ω : ℕ → Bool => ω (k + 1)) = cn := by
      rw [hP]
      exact Measure.infinitePi_map_eval _ _
    have h3 : ∫ ω, Z (k + 1) ω ∂P = ∫ b, sg (k + 1) b ∂cn := by
      rw [← hmap, integral_map (measurable_pi_apply _).aemeasurable
        ((hmb (sg (k + 1))).stronglyMeasurable.aestronglyMeasurable), hZ]
    have h4 : ∫ b, sg (k + 1) b ∂cn = 0 := by
      rw [integral_fintype Integrable.of_finite, Fintype.sum_bool]
      rw [Measure.real, Measure.real, hcntrue, hcnfalse, hsg]
      simp
    rw [h1, h2, h3, h4]
  have hce : ∀ n : ℕ, μ'[ζ (n + 1) | FFs n] =ᵐ[μ'] 0 := by
    intro n
    have hindbig : Indep (MeasurableSpace.comap (Z (n + 1)) inferInstance) (FF n) P := by
      rw [hFF]
      exact hZindep.indep_comap_natural_of_lt hZsm (lt_add_one n)
    have hindsub : Indep (MeasurableSpace.comap (ζ (n + 1)) inferInstance) (FFs n) μ' := by
      rw [hζcomap (n + 1), hFFcomap n, indep_iff_forall_indepSet]
      intro t₁ t₂ ht₁ ht₂
      obtain ⟨B₁, hB₁, hB₁'⟩ := ht₁
      obtain ⟨B₂, hB₂, hB₂'⟩ := ht₂
      have hB₁m : MeasurableSet B₁ := (hZsm (n + 1)).measurable.comap_le _ hB₁
      have hB₂m : MeasurableSet B₂ := FF.le n _ hB₂
      have hmt₁ : MeasurableSet t₁ := by
        rw [← hB₁']
        exact hB₁m.preimage measurable_subtype_coe
      have hmt₂ : MeasurableSet t₂ := by
        rw [← hB₂']
        exact hB₂m.preimage measurable_subtype_coe
      refine (indepSet_iff_measure_inter_eq_mul hmt₁ hmt₂ _).2 ?_
      rw [← hB₁', ← hB₂', ← Set.preimage_inter, hmv _ (hB₁m.inter hB₂m), hmv _ hB₁m, hmv _ hB₂m]
      exact (hindbig.indepSet_of_measurableSet hB₁ hB₂).measure_inter_eq_mul
    have h1 := condExp_indep_eq ((hζsm (n + 1)).measurable.comap_le) (FFs.le n)
      (comap_measurable (ζ (n + 1))).stronglyMeasurable hindsub
    have h2 : (fun _ : {ω : ℕ → Bool // ω ∈ Sset} => ∫ ω, ζ (n + 1) ω ∂μ')
        = (0 : {ω : ℕ → Bool // ω ∈ Sset} → ℝ) := by
      funext ω
      rw [hζint n]
      rfl
    rw [← h2]
    exact h1
  -- ### the escape index
  have hex : ∀ ω : {ω : ℕ → Bool // ω ∈ Sset},
      ∃ m, ∀ i < q, ω.val (q * m + i + 1) = true := fun ω => ω.2
  set G : {ω : ℕ → Bool // ω ∈ Sset} → ℕ := fun ω => Nat.find (hex ω) with hG
  have hGspec : ∀ (ω : {ω : ℕ → Bool // ω ∈ Sset}) (i : ℕ), i < q →
      ω.val (q * G ω + i + 1) = true := by
    intro ω i hi
    rw [hG]
    exact Nat.find_spec (hex ω) i hi
  have hGpre : ∀ m : ℕ, G ⁻¹' {m} = Subtype.val ⁻¹' (E m ∩ A m) := by
    intro m
    ext ω
    have hiff : G ω = m ↔ (∀ i < q, ω.val (q * m + i + 1) = true) ∧
        ∀ j < m, ¬ (∀ i < q, ω.val (q * j + i + 1) = true) := Nat.find_eq_iff (hex ω)
    constructor
    · intro h
      have h' := hiff.1 h
      exact ⟨fun j hj hj' => h'.2 j hj hj', h'.1⟩
    · intro h
      exact hiff.2 ⟨h.2, fun j hj hj' => h.1 j hj hj'⟩
  have hGmeas : Measurable G := by
    refine measurable_to_countable' (fun m => ?_)
    rw [hGpre m]
    exact ((hEmeas m).inter (hAmeas m)).preimage measurable_subtype_coe
  have hGtail : ∀ m : ℕ, {ω | m < G ω} = Subtype.val ⁻¹' (E (m + 1)) := by
    intro m
    ext ω
    have hiff : m < G ω ↔ ∀ j ≤ m, ¬ (∀ i < q, ω.val (q * j + i + 1) = true) :=
      Nat.lt_find_iff (hex ω) m
    constructor
    · intro h j hj hj'
      exact hiff.1 h j (by omega) hj'
    · intro h
      exact hiff.2 (fun j hj hj' => h j (by omega) hj')
  have hGtailmeas : ∀ m : ℕ, MeasurableSet {ω : {ω : ℕ → Bool // ω ∈ Sset} | m < G ω} := by
    intro m
    rw [hGtail m]
    exact (hEmeas (m + 1)).preimage measurable_subtype_coe
  have hlint : ∫⁻ ω, (G ω : ℝ≥0∞) ∂μ' = ∑' m : ℕ, μ' {ω | m < G ω} := by
    have hpt : ∀ ω : {ω : ℕ → Bool // ω ∈ Sset}, ((G ω : ℕ) : ℝ≥0∞)
        = ∑' m : ℕ, Set.indicator {ω | m < G ω} (1 : {ω : ℕ → Bool // ω ∈ Sset} → ℝ≥0∞) ω := by
      intro ω
      have hzero : ∀ m ∉ Finset.range (G ω),
          Set.indicator {ω | m < G ω} (1 : {ω : ℕ → Bool // ω ∈ Sset} → ℝ≥0∞) ω = 0 := by
        intro m hm
        refine Set.indicator_of_notMem ?_ _
        simpa using hm
      rw [tsum_eq_sum hzero]
      have hone : ∀ m ∈ Finset.range (G ω),
          Set.indicator {ω | m < G ω} (1 : {ω : ℕ → Bool // ω ∈ Sset} → ℝ≥0∞) ω = 1 := by
        intro m hm
        refine Set.indicator_of_mem ?_ _
        simpa using hm
      rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [lintegral_congr hpt, lintegral_tsum (fun m =>
      ((measurable_one.indicator (hGtailmeas m)).aemeasurable))]
    exact tsum_congr (fun m => lintegral_indicator_one (hGtailmeas m))
  have hGbound : ∫⁻ ω, (G ω : ℝ≥0∞) ∂μ' ≤ 2 ^ q := by
    rw [hlint]
    have h1 : ∀ m : ℕ, μ' {ω | m < G ω} = (1 - p) ^ (m + 1) := by
      intro m
      rw [hGtail m, hmv _ (hEmeas (m + 1)), hEP (m + 1)]
    rw [tsum_congr h1, ENNReal.tsum_geometric_add_one,
      ENNReal.sub_sub_cancel (by simp) hp1]
    have hsub : (1 : ℝ≥0∞) - p ≤ 1 := by simp
    calc (1 - p) * p⁻¹ ≤ 1 * p⁻¹ := by
          exact mul_le_mul' hsub le_rfl
      _ = p⁻¹ := one_mul _
      _ = 2 ^ q := by rw [hpdef, ENNReal.inv_pow, inv_inv]
  have hGnn : ∀ ω : {ω : ℕ → Bool // ω ∈ Sset}, (0 : ℝ) ≤ (G ω : ℝ) :=
    fun ω => Nat.cast_nonneg _
  have hGcast : Measurable (fun ω : {ω : ℕ → Bool // ω ∈ Sset} => (G ω : ℝ)) := by
    have h1 : Measurable (fun n : ℕ => (n : ℝ)) := Measurable.of_discrete
    exact h1.comp hGmeas
  have hGsm : AEStronglyMeasurable (fun ω => (G ω : ℝ)) μ' :=
    hGcast.stronglyMeasurable.aestronglyMeasurable
  have hofreal : ∀ ω : {ω : ℕ → Bool // ω ∈ Sset},
      ENNReal.ofReal ((G ω : ℝ)) = (G ω : ℝ≥0∞) := by
    intro ω
    rw [ENNReal.ofReal_natCast]
  have hGint : Integrable (fun ω => (G ω : ℝ)) μ' := by
    refine ⟨hGsm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hGnn), lintegral_congr hofreal]
    exact lt_of_le_of_lt hGbound (by finiteness)
  have hGintbound : ∫ ω, (G ω : ℝ) ∂μ' ≤ 2 ^ q := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hGnn) hGsm,
      lintegral_congr hofreal]
    have h2 : (∫⁻ ω, (G ω : ℝ≥0∞) ∂μ').toReal ≤ ((2 : ℝ≥0∞) ^ q).toReal :=
      ENNReal.toReal_mono (by finiteness) hGbound
    calc (∫⁻ ω, (G ω : ℝ≥0∞) ∂μ').toReal ≤ ((2 : ℝ≥0∞) ^ q).toReal := h2
      _ = 2 ^ q := by
          rw [ENNReal.toReal_pow]
          norm_num
  refine ⟨{ω : ℕ → Bool // ω ∈ Sset}, inferInstance, μ', FFs, (fun n => ζ (n + 1)), G,
    hμ'univ, ?_, ?_, ?_, ?_, hGint, hGintbound⟩
  · intro n ω
    rw [hζ, hZ, hsg]
    by_cases h : ω.val (n + 1) = true
    · left
      simp [h]
    · right
      simp [h]
  · intro n
    exact Filtration.stronglyAdapted_natural hζsm (n + 1)
  · exact hce
  · intro ω i hi
    have h1 : ζ (q * G ω + i + 1) ω = 1 := by
      rw [hζ, hZ, hsg]
      simp [hGspec ω i hi]
    exact h1
