import InfHarmonic.IsContactWalk
import InfHarmonic.DPSpatialRegularity
import InfHarmonic.QuadEnvAttained
import InfHarmonic.EnvHamiltonianSolution
import InfHarmonic.UniformSubquadratic
import InfHarmonic.OptimizerLocalization
import InfHarmonic.FairSignEscape
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Proposition 6.7, the existence half of part 1: for the pair supplied by the
extremal envelope contact and for every box `(T, R, N)` there are a step size
`ε`, a probability space with a filtration, fair signs, and a stopped contact
walk on it in the sense of `IsContactWalk`. -/
theorem ContactWalkExists (C₀ κ H : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 < κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJbd : HasJensenBound Set.univ v κ)
    (hWcont : ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2})
    (hWgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ))
    (hW0 : ContactEnv v κ (toLp 2 ((0 : F), (1 : ℝ))) = 0)
    (hv0 : v (toLp 2 ((0 : F), (1 : ℝ))) = 0)
    (hham : EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) = (H : EReal))
    (hslope : Tendsto (fun l => EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 H)) :
    ∀ T : ℕ, 2 ≤ T → ∀ R : ℝ, 2 ≤ R → ∀ N : ℕ, 1 ≤ N →
      ∃ (ε : ℝ) (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω)
        (𝒢 : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ)
        (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ),
        IsContactWalk κ H T R v N ε μ 𝒢 ξ z zp zm Q₀ τ ∧
          ∀ n : ℕ, (Set.range (z n)).Countable := by
  classical
  -- ## Step 0: standing facts about `v`
  have hvcontOn : ContinuousOn v (Set.univ : Set (WithLp 2 (F × ℝ))) := hv.1.1.2.1
  have hvcont : Continuous v := continuousOn_univ.mp hvcontOn
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc e he
    obtain ⟨M, hM0, hMb⟩ := UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ)))
      (Or.inr rfl) J hJc e he
    exact ⟨M, hM0, fun z hz ht => hMb v hv hcent z hz ht⟩
  -- ## Step 1: the small-length behaviour of `J_ε(z_*)`
  have hstar : (ofLp (toLp 2 ((0 : F), (1 : ℝ))) : F × ℝ) = ((0 : F), (1 : ℝ)) := by
    simp
  have hMslope : ∀ l : ℝ, 0 < l → H ≤ EnvSlopeM v l (toLp 2 ((0 : F), (1 : ℝ))) := by
    intro l hl
    have hEHS := (EnvHamiltonianSolution (Set.univ : Set ℝ) isOpen_univ v
      (by simpa using hvcontOn) hvgrow (by simpa using hv.1)).2.1
      (toLp 2 ((0 : F), (1 : ℝ))) (fun _ => Set.mem_univ _)
    have hle : (⨅ l' ∈ Set.Ioi (0 : ℝ),
        ((EnvSlopeM v l' (toLp 2 ((0 : F), (1 : ℝ))) : ℝ) : EReal))
        ≤ ((EnvSlopeM v l (toLp 2 ((0 : F), (1 : ℝ))) : ℝ) : EReal) :=
      iInf₂_le l hl
    rw [hEHS, hham] at hle
    exact EReal.coe_le_coe_iff.mp hle
  have hJeps : ∀ l : ℝ, 0 < l →
      JGap v κ l (toLp 2 ((0 : F), (1 : ℝ)))
        = (EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ)))
            + EnvSlopeM v l (toLp 2 ((0 : F), (1 : ℝ)))) / 2 := by
    intro l hl
    rw [JGap, EnvSlopeP, EnvSlopeM, hW0, hv0]
    field_simp
    ring
  have hl0 : ∃ l0 : ℝ, 0 < l0 ∧ ∀ l : ℝ, 0 < l → l ≤ l0 →
      H - 1 ≤ JGap v κ l (toLp 2 ((0 : F), (1 : ℝ))) := by
    have h1 : ∀ᶠ l in 𝓝[>] (0 : ℝ),
        H - 2 ≤ EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))) :=
      hslope.eventually (eventually_ge_nhds (by linarith))
    obtain ⟨l1, hl1pos, hl1sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h1
    have hl1 : (0 : ℝ) < l1 := hl1pos
    refine ⟨l1 / 2, by linarith, fun l hl hle => ?_⟩
    have h2 : H - 2 ≤ EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))) :=
      hl1sub (Set.mem_Ioo.mpr ⟨hl, by linarith⟩)
    have h3 := hMslope l hl
    rw [hJeps l hl]
    linarith
  obtain ⟨l0, hl0pos, hl0bd⟩ := hl0
  intro T hT R hR N hN
  -- ## Step 2: the uniform localization of the optimizers
  obtain ⟨A, hA1, hAloc⟩ := OptimizerLocalization v (ContactEnv v κ) hvcont hvgrow hWcont hWgrow
    (T : ℝ) R hR N hN
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  -- ## the grid
  set d : ℝ := (1 / 2 : ℝ) ^ N with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hdle : d ≤ 1 / 2 := by
    rw [hd]
    calc (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
      _ = 1 / 2 := by norm_num
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by
    have : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  -- ## the choice of ε
  obtain ⟨k1, hk1⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < min l0 (1 / (32 * A)) by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  set k : ℕ := max (N + 2) k1 with hk
  set ε : ℝ := (1 / 2 : ℝ) ^ k with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hkN : N + 2 ≤ k := le_max_left _ _
  have hεmono : ∀ j : ℕ, j ≤ k → ε ≤ (1 / 2 : ℝ) ^ j := by
    intro j hj
    rw [hε]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have hεd4 : ε ≤ d / 4 := by
    have h1 : ε ≤ (1 / 2 : ℝ) ^ (N + 2) := hεmono _ hkN
    rw [hd]
    calc ε ≤ (1 / 2 : ℝ) ^ (N + 2) := h1
      _ = (1 / 2 : ℝ) ^ N / 4 := by rw [pow_add]; ring
  have hεk1 : ε < min l0 (1 / (32 * A)) := lt_of_le_of_lt (hεmono _ (le_max_right _ _)) hk1
  have hεl0 : ε ≤ l0 := le_of_lt (lt_of_lt_of_le hεk1 (min_le_left _ _))
  have hεA : 32 * A * ε ≤ 1 := by
    have h1 : ε < 1 / (32 * A) := lt_of_lt_of_le hεk1 (min_le_right _ _)
    have h2 : (0 : ℝ) < 32 * A := by linarith
    rw [lt_div_iff₀ h2] at h1
    linarith
  have hεhalf : ε ≤ 1 / 2 := le_trans hεd4 (by linarith)
  -- ## the grid
  have hupgrade : ∀ (a b : ℝ) (m1 m2 : ℤ), a = (m1 : ℝ) * ε → b = (m2 : ℝ) * ε → a < b →
      a + ε ≤ b := by
    intro a b m1 m2 ha hb hab
    have hm : m1 < m2 := by
      rcases le_or_gt m2 m1 with hcc | hcc
      · exfalso
        have h1 : (m2 : ℝ) ≤ (m1 : ℝ) := by exact_mod_cast hcc
        have h2 : b ≤ a := by
          rw [ha, hb]
          exact mul_le_mul_of_nonneg_right h1 hε0.le
        linarith
      · exact hcc
    have h2 : (m1 : ℝ) + 1 ≤ (m2 : ℝ) := by exact_mod_cast hm
    rw [ha, hb]
    nlinarith [hε0]
  have hhalfpow : ∀ j : ℕ, (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 := by
    intro j
    rw [← mul_pow]
    norm_num
  have hpowk : (2 : ℝ) ^ k * ε = 1 := by
    rw [hε, mul_comm]
    exact hhalfpow k
  have h1grid : ∃ m : ℤ, (1 : ℝ) = (m : ℝ) * ε := by
    refine ⟨2 ^ k, ?_⟩
    push_cast
    rw [← hpowk]
  have hdgrid : ∃ m : ℤ, d = (m : ℝ) * ε := by
    refine ⟨2 ^ (k - N), ?_⟩
    have hNk : N ≤ k := by omega
    have h2 : (2 : ℝ) ^ (k - N) * (2 : ℝ) ^ N = (2 : ℝ) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hNk]
    have hcancel : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    have hA : d * (2 : ℝ) ^ k = (2 : ℝ) ^ (k - N) := by
      rw [hd]
      calc (1 / 2 : ℝ) ^ N * (2 : ℝ) ^ k
          = (1 / 2 : ℝ) ^ N * ((2 : ℝ) ^ N * (2 : ℝ) ^ (k - N)) := by
            rw [← pow_add, Nat.add_sub_cancel' hNk]
        _ = ((1 / 2 : ℝ) ^ N * (2 : ℝ) ^ N) * (2 : ℝ) ^ (k - N) := by ring
        _ = (2 : ℝ) ^ (k - N) := by rw [hhalfpow N, one_mul]
    have hB : ((2 : ℝ) ^ (k - N) * ε) * (2 : ℝ) ^ k = (2 : ℝ) ^ (k - N) := by
      rw [mul_assoc, mul_comm ε ((2 : ℝ) ^ k), hpowk, mul_one]
    have hC : d = (2 : ℝ) ^ (k - N) * ε := mul_right_cancel₀ hcancel (hA.trans hB.symm)
    push_cast
    exact hC
  have hTgrid : ∃ m : ℤ, (T : ℝ) = (m : ℝ) * ε := by
    refine ⟨(T : ℤ) * 2 ^ k, ?_⟩
    push_cast
    rw [mul_assoc, hpowk, mul_one]
  -- ## Step 3: the optimizers, the step functions and the walk
  have hYpex : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 → ∃ y : F,
      QuadEnvP (ContactEnv v κ) (2 * ε) z
        = ContactEnv v κ (toLp 2 (y, (ofLp z).2 + 2 * ε))
            - ‖y - (ofLp z).1‖ ^ 2 / (2 * (2 * ε)) := by
    intro z hz
    exact (QuadEnvAttained (Set.Ioi (0 : ℝ)) isOpen_Ioi (ContactEnv v κ) hWcont hWgrow).1
      (2 * ε) z (by linarith) hz (by simp only [Set.mem_Ioi]; linarith)
  have hYmex : ∀ z : WithLp 2 (F × ℝ), ∃ y : F,
      QuadEnvM v (2 * ε) z
        = v (toLp 2 (y, (ofLp z).2 - 2 * ε)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * (2 * ε)) := by
    intro z
    exact (QuadEnvAttained (Set.univ : Set ℝ) isOpen_univ v (by simpa using hvcontOn) hvgrow).2.1
      (2 * ε) z (by linarith) (Set.mem_univ _) (Set.mem_univ _)
  have hQex : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 → ∃ Q : F,
      HasGradientAt (fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', (ofLp z).2)))
        Q (ofLp z).1 := by
    intro z hz
    obtain ⟨y, -, -, hgrad, -⟩ := DPSpatialRegularity C₀ κ hC₀ hκ.le v hv hcent hJbd
      (ofLp z).2 ε hz hε0 (ofLp z).1
    exact ⟨ε⁻¹ • (y - (ofLp z).1), hgrad⟩
  set lv : WithLp 2 (F × ℝ) → Prop := fun z =>
    d < (ofLp z).2 ∧ (ofLp z).2 < (T : ℝ) ∧ ‖(ofLp z).1‖ < R with hlv
  set Ypf : WithLp 2 (F × ℝ) → F :=
    fun z => if h : 0 < (ofLp z).2 then (hYpex z h).choose else 0 with hYpf
  set Ymf : WithLp 2 (F × ℝ) → F := fun z => (hYmex z).choose with hYmf
  set Q0f : WithLp 2 (F × ℝ) → F :=
    fun z => if h : 0 < (ofLp z).2 then (hQex z h).choose else 0 with hQ0f
  set zpf : WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ) := fun z =>
    if lv z then toLp 2 ((2 : ℝ)⁻¹ • ((ofLp z).1 + Ypf z), (ofLp z).2 + ε) else z with hzpf
  set zmf : WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ) := fun z =>
    if lv z then toLp 2 ((2 : ℝ)⁻¹ • ((ofLp z).1 + Ymf z), (ofLp z).2 - ε) else z with hzmf
  set nxt : WithLp 2 (F × ℝ) → Bool → WithLp 2 (F × ℝ) := fun z b =>
    if lv z then (if b = true then zpf z else zmf z) else z with hnxt
  set zst : WithLp 2 (F × ℝ) := toLp 2 ((0 : F), (1 : ℝ)) with hzst
  set wk : (ℕ → Bool) → ℕ → WithLp 2 (F × ℝ) :=
    fun hb => Nat.rec zst (fun n z => nxt z (hb n)) with hwk
  have hwk0 : ∀ hb : ℕ → Bool, wk hb 0 = zst := fun hb => rfl
  have hwkS : ∀ (hb : ℕ → Bool) (n : ℕ), wk hb (n + 1) = nxt (wk hb n) (hb n) := fun hb n => rfl
  -- the time coordinates of the two steps
  have hzpt : ∀ z : WithLp 2 (F × ℝ), lv z → (ofLp (zpf z)).2 = (ofLp z).2 + ε := by
    intro z hz
    rw [hzpf]
    simp only [if_pos hz]
  have hzmt : ∀ z : WithLp 2 (F × ℝ), lv z → (ofLp (zmf z)).2 = (ofLp z).2 - ε := by
    intro z hz
    rw [hzmf]
    simp only [if_pos hz]
  have hzpx : ∀ z : WithLp 2 (F × ℝ), lv z →
      (ofLp (zpf z)).1 = (2 : ℝ)⁻¹ • ((ofLp z).1 + Ypf z) := by
    intro z hz
    rw [hzpf]
    simp only [if_pos hz]
  have hzmx : ∀ z : WithLp 2 (F × ℝ), lv z →
      (ofLp (zmf z)).1 = (2 : ℝ)⁻¹ • ((ofLp z).1 + Ymf z) := by
    intro z hz
    rw [hzmf]
    simp only [if_pos hz]
  -- ## the numerical invariants
  have hinv : ∀ (hb : ℕ → Bool) (n : ℕ),
      (∃ m : ℤ, (ofLp (wk hb n)).2 = (m : ℝ) * ε) ∧
        d ≤ (ofLp (wk hb n)).2 ∧ (ofLp (wk hb n)).2 ≤ (T : ℝ) := by
    intro hb n
    induction n with
    | zero =>
      rw [hwk0, hzst]
      have h1 : (ofLp (toLp 2 ((0 : F), (1 : ℝ))) : F × ℝ).2 = 1 := by simp
      rw [h1]
      exact ⟨h1grid, by linarith, hT1⟩
    | succ n ih =>
      obtain ⟨⟨m, hm⟩, hdle', hTle'⟩ := ih
      rw [hwkS]
      by_cases hlive : lv (wk hb n)
      · -- live: the two cases
        obtain ⟨md, hmd⟩ := hdgrid
        obtain ⟨mT, hmT⟩ := hTgrid
        have hdt : d + ε ≤ (ofLp (wk hb n)).2 := hupgrade _ _ md m hmd hm hlive.1
        have htT : (ofLp (wk hb n)).2 + ε ≤ (T : ℝ) := hupgrade _ _ m mT hm hmT hlive.2.1
        rw [hnxt]
        simp only [if_pos hlive]
        by_cases hbn : hb n = true
        · simp only [if_pos hbn]
          rw [hzpt _ hlive]
          exact ⟨⟨m + 1, by rw [hm]; push_cast; ring⟩, by linarith, by linarith⟩
        · simp only [if_neg hbn]
          rw [hzmt _ hlive]
          exact ⟨⟨m - 1, by rw [hm]; push_cast; ring⟩, by linarith, by linarith⟩
      · rw [hnxt]
        simp only [if_neg hlive]
        exact ⟨⟨m, hm⟩, hdle', hTle'⟩
  -- ## the steps are short
  have hstepsmall : ∀ z : WithLp 2 (F × ℝ), lv z →
      ‖(ofLp (zpf z)).1 - (ofLp z).1‖ ≤ 1 / 4 ∧
        ‖(ofLp (zmf z)).1 - (ofLp z).1‖ ≤ 1 / 4 := by
    intro z hz
    have ht0 : 0 < (ofLp z).2 := lt_trans hd0 hz.1
    have h2e : 0 < 2 * ε := by linarith
    have h2emin : 2 * ε ≤ min 1 (d / 2) := le_min (by linarith) (by linarith)
    have hloc := hAloc (2 * ε) h2e h2emin z hz.2.2.le hz.1.le hz.2.1.le
    have hYp : ‖Ypf z - (ofLp z).1‖ ≤ 2 * Real.sqrt (A * (2 * ε)) := by
      refine (hloc (Ypf z)).1 ?_
      rw [hYpf]
      simp only [dif_pos ht0]
      exact (hYpex z ht0).choose_spec
    have hYm : ‖Ymf z - (ofLp z).1‖ ≤ 2 * Real.sqrt (A * (2 * ε)) := by
      refine (hloc (Ymf z)).2 ?_
      rw [hYmf]
      exact (hYmex z).choose_spec
    have hsq : Real.sqrt (A * (2 * ε)) ≤ 1 / 4 := by
      have h16 : Real.sqrt (1 / 16) = 1 / 4 := by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [← h16]
      exact Real.sqrt_le_sqrt (by linarith)
    have hhalf : ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos]
      norm_num
    constructor
    · rw [hzpx z hz]
      have halg : (2 : ℝ)⁻¹ • ((ofLp z).1 + Ypf z) - (ofLp z).1
          = (2 : ℝ)⁻¹ • (Ypf z - (ofLp z).1) := by module
      rw [halg, norm_smul, hhalf]
      linarith
    · rw [hzmx z hz]
      have halg : (2 : ℝ)⁻¹ • ((ofLp z).1 + Ymf z) - (ofLp z).1
          = (2 : ℝ)⁻¹ • (Ymf z - (ofLp z).1) := by module
      rw [halg, norm_smul, hhalf]
      linarith
  -- ## the walk depends only on the signs read so far
  have hdep : ∀ (n : ℕ) (hb hb' : ℕ → Bool), (∀ k, k < n → hb k = hb' k) →
      wk hb n = wk hb' n := by
    intro n
    induction n with
    | zero =>
      intro hb hb' _
      rw [hwk0, hwk0]
    | succ n ih =>
      intro hb hb' h
      rw [hwkS, hwkS, ih hb hb' (fun k hk => h k (by omega)), h n (by omega)]
  -- ## the probability space
  set q : ℕ := ⌈((T : ℝ) - d) / ε⌉₊ + 1 with hq
  obtain ⟨Ω, m0, μ, 𝒢, ξ, G, hμ1, hξpm, hξsm, hξce, hblock, hGint, hGbd⟩ :=
    FairSignEscape q
  set hist : Ω → ℕ → Bool := fun ω k => if ξ k ω = 1 then true else false with hhist
  have hhistT : ∀ (ω : Ω) (k : ℕ), hist ω k = true ↔ ξ k ω = 1 := by
    intro ω k
    rw [hhist]
    by_cases h : ξ k ω = 1 <;> simp [h]
  have hxi1 : ∀ (k n : ℕ), k < n → MeasurableSet[𝒢 n] {ω | ξ k ω = 1} := by
    intro k n hkn
    have h1 : MeasurableSet[𝒢 (k + 1)] {ω | ξ k ω = 1} :=
      (hξsm k).measurable (measurableSet_singleton (1 : ℝ))
    exact 𝒢.mono (by omega) _ h1
  have hhk : ∀ (k n : ℕ), k < n → ∀ b : Bool, MeasurableSet[𝒢 n] {ω | hist ω k = b} := by
    intro k n hkn b
    cases b with
    | true =>
      have heq : {ω | hist ω k = true} = {ω | ξ k ω = 1} := by
        ext ω
        exact hhistT ω k
      rw [heq]
      exact hxi1 k n hkn
    | false =>
      have heq : {ω | hist ω k = false} = {ω | ξ k ω = 1}ᶜ := by
        ext ω
        show hist ω k = false ↔ ¬ (ξ k ω = 1)
        constructor
        · intro h hc
          have h2 := (hhistT ω k).mpr hc
          rw [h] at h2
          exact Bool.noConfusion h2
        · intro h
          rcases Bool.eq_false_or_eq_true (hist ω k) with hb | hb
          · exact absurd ((hhistT ω k).mp hb) h
          · exact hb
      rw [heq]
      exact ((hxi1 k n hkn).compl)
  have hcyl : ∀ (n : ℕ) (s : ℕ → Bool),
      MeasurableSet[𝒢 n] {ω | ∀ k, k < n → hist ω k = s k} := by
    intro n s
    have heq : {ω | ∀ k, k < n → hist ω k = s k}
        = ⋂ k ∈ Finset.range n, {ω | hist ω k = s k} := by
      ext ω
      simp only [Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq]
    rw [heq]
    exact MeasurableSet.biInter (Finset.range n).countable_toSet
      (fun k hk => hhk k n (Finset.mem_range.mp hk) (s k))
  -- ## finite-history functions are adapted
  have hSM : ∀ (g : (ℕ → Bool) → WithLp 2 (F × ℝ)) (n : ℕ),
      (∀ hb hb' : ℕ → Bool, (∀ k, k < n → hb k = hb' k) → g hb = g hb') →
      StronglyMeasurable[𝒢 n] (fun ω => g (hist ω)) := by
    intro g n hgdep
    classical
    set ex : (Fin n → Bool) → (ℕ → Bool) :=
      fun s k => if h : k < n then s ⟨k, h⟩ else true with hex
    set AA : (Fin n → Bool) → Set Ω := fun s => {ω | ∀ k, k < n → hist ω k = ex s k} with hAA
    have hAm : ∀ s, MeasurableSet[𝒢 n] (AA s) := fun s => hcyl n (ex s)
    have hrep : ∀ ω : Ω,
        g (hist ω) = ∑ s : Fin n → Bool, (AA s).indicator (fun _ => g (ex s)) ω := by
      intro ω
      set s0 : Fin n → Bool := fun i => hist ω (i : ℕ) with hs0
      have hmem : ω ∈ AA s0 := by
        intro k hk
        rw [hex]
        simp only [dif_pos hk, hs0]
      have hval : g (ex s0) = g (hist ω) := by
        refine hgdep _ _ (fun k hk => ?_)
        rw [hex]
        simp only [dif_pos hk, hs0]
      have hsingle : ∀ s : Fin n → Bool, s ≠ s0 → (AA s).indicator (fun _ => g (ex s)) ω = 0 := by
        intro s hs
        refine Set.indicator_of_notMem ?_ _
        intro hw
        refine hs (funext fun i => ?_)
        have h1 : hist ω (i : ℕ) = ex s (i : ℕ) := hw (i : ℕ) i.2
        rw [hex] at h1
        simp only [dif_pos i.2] at h1
        rw [hs0]
        exact h1.symm
      rw [Finset.sum_eq_single_of_mem s0 (Finset.mem_univ _) (fun s _ hs => hsingle s hs),
        Set.indicator_of_mem hmem, hval]
    have hfun : (fun ω => g (hist ω))
        = fun ω => ∑ s : Fin n → Bool, (AA s).indicator (fun _ => g (ex s)) ω := funext hrep
    rw [hfun]
    exact Finset.stronglyMeasurable_fun_sum _ (fun s _ => stronglyMeasurable_const.indicator (hAm s))
  have hSMF : ∀ (g : (ℕ → Bool) → F) (n : ℕ),
      (∀ hb hb' : ℕ → Bool, (∀ k, k < n → hb k = hb' k) → g hb = g hb') →
      StronglyMeasurable[𝒢 n] (fun ω => g (hist ω)) := by
    intro g n hgdep
    have h1 : StronglyMeasurable[𝒢 n]
        (fun ω => (toLp 2 (g (hist ω), (0 : ℝ)) : WithLp 2 (F × ℝ))) :=
      hSM (fun hb => toLp 2 (g hb, (0 : ℝ))) n (fun hb hb' h => by rw [hgdep hb hb' h])
    have hc : Continuous (fun w : WithLp 2 (F × ℝ) => (ofLp w).1) := by fun_prop
    have heqf : (fun ω : Ω => g (hist ω))
        = fun ω : Ω => (ofLp (toLp 2 (g (hist ω), (0 : ℝ)) : WithLp 2 (F × ℝ))).1 := by
      funext ω
      simp
    rw [heqf]
    exact hc.comp_stronglyMeasurable h1
  -- ## the walk as a process, and its adaptedness
  set zw : ℕ → Ω → WithLp 2 (F × ℝ) := fun n ω => wk (hist ω) n with hzw
  set zpw : ℕ → Ω → WithLp 2 (F × ℝ) := fun n ω => zpf (wk (hist ω) n) with hzpw
  set zmw : ℕ → Ω → WithLp 2 (F × ℝ) := fun n ω => zmf (wk (hist ω) n) with hzmw
  set Q0w : ℕ → Ω → F := fun n ω => Q0f (wk (hist ω) n) with hQ0w
  have hzSM : ∀ n, StronglyMeasurable[𝒢 n] (zw n) :=
    fun n => hSM (fun hb => wk hb n) n (fun hb hb' h => hdep n hb hb' h)
  have hzpSM : ∀ n, StronglyMeasurable[𝒢 n] (zpw n) :=
    fun n => hSM (fun hb => zpf (wk hb n)) n (fun hb hb' h => by rw [hdep n hb hb' h])
  have hzmSM : ∀ n, StronglyMeasurable[𝒢 n] (zmw n) :=
    fun n => hSM (fun hb => zmf (wk hb n)) n (fun hb hb' h => by rw [hdep n hb hb' h])
  have hQSM : ∀ n, StronglyMeasurable[𝒢 n] (Q0w n) :=
    fun n => hSMF (fun hb => Q0f (wk hb n)) n (fun hb hb' h => by rw [hdep n hb hb' h])
  -- real-valued coordinates of the walk
  have htmeas : ∀ n, Measurable[𝒢 n] (fun ω => (ofLp (zw n ω)).2) := by
    intro n
    have hc : Continuous (fun w : WithLp 2 (F × ℝ) => (ofLp w).2) := by fun_prop
    exact (hc.comp_stronglyMeasurable (hzSM n)).measurable
  have hxmeas : ∀ n, Measurable[𝒢 n] (fun ω => ‖(ofLp (zw n ω)).1‖) := by
    intro n
    have hc : Continuous (fun w : WithLp 2 (F × ℝ) => ‖(ofLp w).1‖) := by fun_prop
    exact (hc.comp_stronglyMeasurable (hzSM n)).measurable
  have hlvmeas : ∀ n, MeasurableSet[𝒢 n] {ω | lv (zw n ω)} := by
    intro n
    have h1 : {ω | lv (zw n ω)}
        = ((fun ω => (ofLp (zw n ω)).2) ⁻¹' (Set.Ioo d (T : ℝ)))
            ∩ ((fun ω => ‖(ofLp (zw n ω)).1‖) ⁻¹' (Set.Iio R)) := by
      ext ω
      show lv (zw n ω) ↔ _
      rw [hlv]
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
      · intro h
        exact ⟨h.1.1, h.1.2, h.2⟩
    rw [h1]
    exact ((htmeas n) measurableSet_Ioo).inter ((hxmeas n) measurableSet_Iio)
  -- ## the escape: the walk cannot stay live through a block of `+1` signs
  have hnostop : ∀ ω : Ω, ¬ (∀ n, n ≤ q * G ω + q → lv (wk (hist ω) n)) := by
    intro ω hall
    have hblk : ∀ i, i < q → hist ω (q * G ω + i) = true :=
      fun i hi => (hhistT ω _).mpr (hblock ω i hi)
    have htime : ∀ j, j ≤ q →
        (ofLp (wk (hist ω) (q * G ω + j))).2
          = (ofLp (wk (hist ω) (q * G ω))).2 + (j : ℝ) * ε := by
      intro j
      induction j with
      | zero =>
        intro _
        simp
      | succ j ih =>
        intro hj
        have h1 := ih (by omega)
        have hlive := hall (q * G ω + j) (by omega)
        have hbit : hist ω (q * G ω + j) = true := hblk j (by omega)
        rw [show q * G ω + (j + 1) = (q * G ω + j) + 1 by ring, hwkS, hnxt]
        simp only [if_pos hlive, if_pos hbit]
        rw [hzpt _ hlive, h1]
        push_cast
        ring
    have hq1 : ((T : ℝ) - d) < (q : ℝ) * ε := by
      have h1 : ((T : ℝ) - d) / ε ≤ (⌈((T : ℝ) - d) / ε⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((T : ℝ) - d) / ε < (q : ℝ) := by
        rw [hq]
        push_cast
        linarith
      rw [div_lt_iff₀ hε0] at h2
      linarith
    have hup := (hinv (hist ω) (q * G ω + q)).2.2
    have hlow := (hinv (hist ω) (q * G ω)).2.1
    rw [htime q le_rfl] at hup
    linarith
  have hstopex : ∀ ω : Ω, ∃ n : ℕ, ¬ lv (wk (hist ω) n) := by
    intro ω
    by_contra hc
    refine hnostop ω (fun n _ => ?_)
    by_contra hn
    exact hc ⟨n, hn⟩
  set τw : Ω → ℕ := fun ω => Nat.find (hstopex ω) with hτw
  have hτspec : ∀ ω : Ω, ¬ lv (wk (hist ω) (τw ω)) := fun ω => Nat.find_spec (hstopex ω)
  have hτlt : ∀ (ω : Ω) (n : ℕ), n < τw ω → lv (wk (hist ω) n) := by
    intro ω n hn
    by_contra hc
    have h1 : τw ω ≤ n := Nat.find_le hc
    omega
  have hτbd : ∀ ω : Ω, τw ω ≤ q * G ω + q := by
    intro ω
    by_contra hc
    exact hnostop ω (fun n hn => hτlt ω n (by omega))
  have hfrozen : ∀ (ω : Ω) (n : ℕ), τw ω ≤ n → wk (hist ω) n = wk (hist ω) (τw ω) := by
    intro ω n hn
    induction n with
    | zero =>
      have : τw ω = 0 := by omega
      rw [this]
    | succ n ih =>
      rcases Nat.lt_or_ge (τw ω) (n + 1) with h | h
      · have hn' : τw ω ≤ n := by omega
        rw [hwkS, ih hn', hnxt]
        simp only [if_neg (hτspec ω)]
      · have : τw ω = n + 1 := by omega
        rw [this]
  have hτge : ∀ (ω : Ω) (n : ℕ), τw ω ≤ n → ¬ lv (wk (hist ω) n) := by
    intro ω n hn
    rw [hfrozen ω n hn]
    exact hτspec ω
  have hlviff : ∀ (ω : Ω) (n : ℕ), lv (wk (hist ω) n) ↔ n < τw ω := by
    intro ω n
    constructor
    · intro h
      rcases Nat.lt_or_ge n (τw ω) with hc | hc
      · exact hc
      · exact absurd h (hτge ω n hc)
    · exact hτlt ω n
  have hprob : IsProbabilityMeasure μ := ⟨hμ1⟩
  -- ## the positions stay in the closed ball of radius `R + 1`
  have hxbd : ∀ (ω : Ω) (n : ℕ), n ≤ τw ω → ‖(ofLp (wk (hist ω) n)).1‖ ≤ R + 1 := by
    intro ω n hn
    rcases Nat.lt_or_ge n (τw ω) with h | h
    · have h1 := (hτlt ω n h).2.2
      linarith
    · have hnt : n = τw ω := by omega
      rcases Nat.eq_zero_or_pos (τw ω) with h0 | h0
      · rw [hnt, h0, hwk0, hzst]
        have h1 : ‖(ofLp (toLp 2 ((0 : F), (1 : ℝ))) : F × ℝ).1‖ = 0 := by simp
        rw [h1]
        linarith
      · obtain ⟨m, hm⟩ : ∃ m, τw ω = m + 1 := ⟨τw ω - 1, by omega⟩
        have hlive : lv (wk (hist ω) m) := hτlt ω m (by omega)
        have hstep := hstepsmall (wk (hist ω) m) hlive
        have hxm : ‖(ofLp (wk (hist ω) m)).1‖ < R := hlive.2.2
        have htri : ∀ w : WithLp 2 (F × ℝ),
            ‖(ofLp w).1‖ ≤ ‖(ofLp w).1 - (ofLp (wk (hist ω) m)).1‖
              + ‖(ofLp (wk (hist ω) m)).1‖ := by
          intro w
          calc ‖(ofLp w).1‖
              = ‖((ofLp w).1 - (ofLp (wk (hist ω) m)).1) + (ofLp (wk (hist ω) m)).1‖ := by
                rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        rw [hnt, hm, hwkS, hnxt]
        by_cases hb : hist ω m = true
        · simp only [if_pos hlive, if_pos hb]
          have h1 := hstep.1
          have h2 := htri (zpf (wk (hist ω) m))
          linarith
        · simp only [if_pos hlive, if_neg hb]
          have h1 := hstep.2
          have h2 := htri (zmf (wk (hist ω) m))
          linarith
  -- ## the stop is exactly at a cutoff
  have hexit : ∀ ω : Ω,
      (ofLp (wk (hist ω) (τw ω))).2 = d ∨ (ofLp (wk (hist ω) (τw ω))).2 = (T : ℝ) ∨
        R ≤ ‖(ofLp (wk (hist ω) (τw ω))).1‖ := by
    intro ω
    have h1 := hτspec ω
    have h2 := hinv (hist ω) (τw ω)
    rw [hlv] at h1
    by_cases ht1 : d < (ofLp (wk (hist ω) (τw ω))).2
    · by_cases ht2 : (ofLp (wk (hist ω) (τw ω))).2 < (T : ℝ)
      · refine Or.inr (Or.inr ?_)
        by_contra hc
        exact h1 ⟨ht1, ht2, not_le.mp hc⟩
      · exact Or.inr (Or.inl (le_antisymm h2.2.2 (not_lt.mp ht2)))
    · exact Or.inl (le_antisymm (not_lt.mp ht1) h2.2.1)
  -- ## the step pairs
  have hsteppair : ∀ (n : ℕ) (ω : Ω), n < τw ω →
      IsStepPair v κ ε (wk (hist ω) n) (zpf (wk (hist ω) n)) (zmf (wk (hist ω) n)) := by
    intro n ω hn
    have hlive := hτlt ω n hn
    have ht0 : 0 < (ofLp (wk (hist ω) n)).2 := lt_trans hd0 hlive.1
    refine ⟨Ypf (wk (hist ω) n), Ymf (wk (hist ω) n), ?_, ?_, ?_, ?_⟩
    · rw [hYpf]
      simp only [dif_pos ht0]
      exact (hYpex _ ht0).choose_spec
    · rw [hYmf]
      exact (hYmex _).choose_spec
    · rw [hzpf]
      simp only [if_pos hlive]
    · rw [hzmf]
      simp only [if_pos hlive]
  -- ## the reference velocities are gradients
  have hgradQ : ∀ (n : ℕ) (ω : Ω),
      HasGradientAt
        (fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', (ofLp (wk (hist ω) n)).2)))
        (Q0f (wk (hist ω) n)) (ofLp (wk (hist ω) n)).1 := by
    intro n ω
    have ht0 : 0 < (ofLp (wk (hist ω) n)).2 := lt_of_lt_of_le hd0 (hinv (hist ω) n).2.1
    rw [hQ0f]
    simp only [dif_pos ht0]
    exact (hQex _ ht0).choose_spec
  -- ## the recursion in the form of clause 7
  have hrec : ∀ (n : ℕ) (ω : Ω), wk (hist ω) (n + 1)
      = if n < τw ω then (if ξ n ω = 1 then zpf (wk (hist ω) n) else zmf (wk (hist ω) n))
        else wk (hist ω) n := by
    intro n ω
    rw [hwkS]
    simp only [hnxt]
    by_cases hlive : lv (wk (hist ω) n)
    · rw [if_pos hlive, if_pos ((hlviff ω n).mp hlive)]
      by_cases hb : ξ n ω = 1
      · rw [if_pos hb, if_pos ((hhistT ω n).mpr hb)]
      · rw [if_neg hb]
        have hbf : hist ω n ≠ true := fun hc => hb ((hhistT ω n).mp hc)
        rw [if_neg hbf]
    · rw [if_neg hlive, if_neg (fun hc => hlive ((hlviff ω n).mpr hc))]
  -- ## `τ` is a stopping time and is integrable
  have hτset : ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | τw ω ≤ n} := by
    intro n
    have heq : {ω | τw ω ≤ n} = ⋃ m ∈ Finset.range (n + 1), {ω | ¬ lv (zw m ω)} := by
      ext ω
      show τw ω ≤ n ↔ _
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨τw ω, by omega, by simpa only [hzw] using hτspec ω⟩
      · intro h
        obtain ⟨m, hm, hmlv⟩ := h
        have h1 : τw ω ≤ m := Nat.find_le (by simpa only [hzw] using hmlv)
        omega
    rw [heq]
    refine MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet (fun m hm => ?_)
    have hmn : m ≤ n := by
      have := Finset.mem_range.mp hm
      omega
    exact 𝒢.mono hmn _ (hlvmeas m).compl
  have hτmeas : Measurable τw := by
    refine measurable_to_countable' (fun n => ?_)
    have heq : τw ⁻¹' {n} = {ω | ¬ lv (zw n ω)} ∩ ⋂ m ∈ Finset.range n, {ω | lv (zw m ω)} := by
      ext ω
      show τw ω = n ↔ _
      simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq]
      constructor
      · intro h
        refine ⟨by simpa only [hzw, h] using hτspec ω, fun m hm => ?_⟩
        simpa only [hzw] using hτlt ω m (by omega)
      · intro h
        have h1 : τw ω ≤ n := Nat.find_le (by simpa only [hzw] using h.1)
        rcases Nat.lt_or_ge (τw ω) n with hc | hc
        · exact absurd (by simpa only [hzw] using h.2 (τw ω) hc) (hτspec ω)
        · omega
    rw [heq]
    refine MeasurableSet.inter (𝒢.le n _ (hlvmeas n).compl) ?_
    exact MeasurableSet.biInter (Finset.range n).countable_toSet
      (fun m _ => 𝒢.le m _ (hlvmeas m))
  have hτint : Integrable (fun ω => (τw ω : ℝ)) μ := by
    have hcast : Measurable (fun n : ℕ => (n : ℝ)) := Measurable.of_discrete
    refine Integrable.mono' (g := fun ω => (q : ℝ) * (G ω : ℝ) + (q : ℝ))
      ((hGint.const_mul _).add (integrable_const _))
      ((hcast.comp hτmeas).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have h1 : τw ω ≤ q * G ω + q := hτbd ω
    have h2 : ((τw ω : ℝ)) ≤ (q : ℝ) * (G ω : ℝ) + (q : ℝ) := by
      have h3 := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at h3
      linarith
    calc ‖((τw ω : ℝ))‖ = (τw ω : ℝ) := Real.norm_natCast _
      _ ≤ _ := h2
  -- ## the walk takes countably many values at each index
  have hcount : ∀ n : ℕ, (Set.range (zw n)).Countable := by
    intro n
    have hsub : Set.range (zw n) ⊆ Set.range (fun s : Fin n → Bool =>
        wk (fun k => if h : k < n then s ⟨k, h⟩ else true) n) := by
      rintro w ⟨ω, rfl⟩
      refine ⟨fun i => hist ω (i : ℕ), ?_⟩
      exact hdep n _ _ (fun k hk => by simp only [dif_pos hk])
    exact Set.Countable.mono hsub (Set.countable_range _)
  -- ## the assembly
  refine ⟨ε, Ω, m0, μ, 𝒢, ξ, zw, zpw, zmw, Q0w, τw, ⟨hμ1, ⟨k, hε⟩, hε0, hεd4, hξpm, hξsm, hξce,
    hzSM, hzpSM, hzmSM, hQSM, fun ω => (hwk0 (hist ω)).trans hzst,
    fun n ω hn => hsteppair n ω hn, fun n ω => hrec n ω, fun n ω => hgradQ n ω, ?_, hτint,
    fun n ω hn => hτlt ω n hn, fun ω => hexit ω, fun n ω hn => hxbd ω n hn,
    hl0bd ε hε0 hεl0⟩, hcount⟩
  intro n
  show MeasurableSet[𝒢 n] {ω | ((τw ω : ℕ∞)) ≤ (n : ℕ∞)}
  have heq : {ω | ((τw ω : ℕ∞)) ≤ (n : ℕ∞)} = {ω | τw ω ≤ n} := by
    ext ω
    show ((τw ω : ℕ∞)) ≤ (n : ℕ∞) ↔ τw ω ≤ n
    exact Nat.cast_le
  rw [heq]
  exact hτset n
