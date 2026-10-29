import InfHarmonic.Preamble
open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The dyadic slope tail and the Hölder--Taylor estimate it produces (Theorem 1.1,
Steps 5 and 6 of the paper).  Along the dyadic scales `r_j = 2^{-j} r₀`, suppose a slope
`P_j` fits `U` at `z` on the inscribed ball of radius `ρ_j = √A₀ r_j^{1+γ/2}` with error
`A₀ r_j^{1+γ}`.  Comparing two consecutive fits on the SMALLER ball gives
`|P_j - P_{j+1}| ≤ C r_j^{γ/2}`, a geometric decay, so the slopes converge; and choosing
the scale with `ρ_{j+1} < |h| ≤ ρ_j` converts `r_j^{γ/2}` into `|h|^α` through the exponent
identity `(1 + γ/2)α = γ/2` with `α = γ/(2+γ)`.  The constant depends only on
`(A₀, γ, r₀)` -- not on `U`, not on the centre -- which is what makes the resulting
estimate uniform over a family.  Only `γ > 0` is needed: the paper's `γ ≤ 1`, which pins
`α ≤ 1/3`, is used where `α` is named and not in this block. -/
theorem DyadicFitTaylorEstimate
    (A₀ gam r₀ : ℝ) (hA₀ : 0 < A₀) (hgam0 : 0 < gam) (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : E → ℝ) (zc : E) (P : ℕ → E),
        (∀ j : ℕ, ∀ h : E,
            ‖h‖ ≤ Real.sqrt A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam / 2) →
            |U (zc + h) - U zc - (inner ℝ (P j) h : ℝ)|
              ≤ A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam)) →
        ∃ Pinf : E,
          (∀ j : ℕ, ‖P j - Pinf‖ ≤ C * ((1 / 2 : ℝ) ^ j * r₀) ^ (gam / 2)) ∧
          (∀ h : E, ‖h‖ ≤ Real.sqrt A₀ * r₀ ^ (1 + gam / 2) →
            |U (zc + h) - U zc - (inner ℝ Pinf h : ℝ)|
              ≤ C * ‖h‖ ^ (1 + gam / (2 + gam))) := by
  classical
  -- the exponents, and the one identity that drives Step 6
  have hhalf0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  obtain ⟨pw, hpwdef⟩ : ∃ pw : ℝ, pw = 1 + gam / 2 := ⟨_, rfl⟩
  have hpw0 : 0 < pw := by rw [hpwdef]; linarith only [hgam0]
  obtain ⟨al, haldef⟩ : ∃ al : ℝ, al = gam / (2 + gam) := ⟨_, rfl⟩
  have hal0 : 0 < al := by
    rw [haldef]; exact div_pos hgam0 (by linarith only [hgam0])
  have hpwal : pw * al = gam / 2 := by
    rw [hpwdef, haldef]
    field_simp
  have hsA : 0 < Real.sqrt A₀ := Real.sqrt_pos.mpr hA₀
  -- the two geometric ratios: `t` for the radii `ρ_j`, `q` for the slope increments
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (1 / 2 : ℝ) ^ pw := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; exact Real.rpow_pos_of_pos (by norm_num) pw
  have ht1 : t < 1 := by
    rw [htdef]; exact Real.rpow_lt_one hhalf0 (by norm_num) hpw0
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (1 / 2 : ℝ) ^ (gam / 2) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hqdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := by
    rw [hqdef]
    exact Real.rpow_lt_one hhalf0 (by norm_num) (by linarith only [hgam0])
  -- `(2^{-j} r₀)^p = ((1/2)^p)^j r₀^p` for every real exponent `p`
  have hpowbase : ∀ (p : ℝ) (j : ℕ), ((1 / 2 : ℝ) ^ j) ^ p = ((1 / 2 : ℝ) ^ p) ^ j := by
    intro p j
    rw [← Real.rpow_natCast ((1 / 2 : ℝ)) j, ← Real.rpow_natCast ((1 / 2 : ℝ) ^ p) j,
      ← Real.rpow_mul hhalf0, ← Real.rpow_mul hhalf0, mul_comm (j : ℝ) p]
  have hsplit : ∀ (p : ℝ) (j : ℕ),
      ((1 / 2 : ℝ) ^ j * r₀) ^ p = ((1 / 2 : ℝ) ^ p) ^ j * r₀ ^ p := by
    intro p j
    rw [Real.mul_rpow (by positivity) (le_of_lt hr₀), hpowbase p j]
  -- the inscribed radii, and their geometric form
  obtain ⟨rho, hrhodef⟩ : ∃ rho : ℕ → ℝ,
      rho = fun j => Real.sqrt A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ pw := ⟨_, rfl⟩
  obtain ⟨Bq, hBqdef⟩ : ∃ Bq : ℝ, Bq = Real.sqrt A₀ * r₀ ^ pw := ⟨_, rfl⟩
  have hBq0 : 0 < Bq := by
    rw [hBqdef]; exact mul_pos hsA (Real.rpow_pos_of_pos hr₀ pw)
  have hrhogeo : ∀ j : ℕ, rho j = Bq * t ^ j := by
    intro j
    rw [hrhodef, hBqdef, htdef]
    show Real.sqrt A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ pw
      = Real.sqrt A₀ * r₀ ^ pw * ((1 / 2 : ℝ) ^ pw) ^ j
    rw [hsplit pw j]; ring
  have hrhoapp : ∀ k : ℕ, Real.sqrt A₀ * ((1 / 2 : ℝ) ^ k * r₀) ^ pw = rho k := by
    intro k; rw [hrhodef]
  have hrho0pos : ∀ j : ℕ, 0 < rho j := by
    intro j; rw [hrhogeo j]; positivity
  have hrhostep : ∀ j : ℕ, rho (j + 1) = t * rho j := by
    intro j; rw [hrhogeo, hrhogeo, pow_succ]; ring
  have hrhomono : ∀ j : ℕ, rho (j + 1) ≤ rho j := by
    intro j
    rw [hrhostep j]
    nlinarith only [ht1, ht0, hrho0pos j]
  have hrho0 : rho 0 = Real.sqrt A₀ * r₀ ^ (1 + gam / 2) := by
    rw [hrhogeo 0, hBqdef, hpwdef]; ring
  -- the slope-increment scale, and its geometric form
  obtain ⟨aq, haqdef⟩ : ∃ aq : ℝ, aq = r₀ ^ (gam / 2) := ⟨_, rfl⟩
  have haq0 : 0 < aq := by rw [haqdef]; exact Real.rpow_pos_of_pos hr₀ _
  have hqgeo : ∀ j : ℕ, ((1 / 2 : ℝ) ^ j * r₀) ^ (gam / 2) = q ^ j * aq := by
    intro j; rw [hsplit (gam / 2) j, hqdef, haqdef]
  -- the two constants
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = 2 * Real.sqrt A₀ / t := ⟨_, rfl⟩
  have hC₁0 : 0 < C₁ := by
    rw [hC₁def]; exact div_pos (by linarith only [hsA]) ht0
  obtain ⟨C₂, hC₂def⟩ : ∃ C₂ : ℝ, C₂ = C₁ * aq / (1 - q) := ⟨_, rfl⟩
  have hC₂0 : 0 < C₂ := by
    rw [hC₂def]; exact div_pos (mul_pos hC₁0 haq0) (by linarith only [hq1])
  obtain ⟨C₃, hC₃def⟩ : ∃ C₃ : ℝ, C₃ = Real.sqrt A₀ / t + C₂ / aq := ⟨_, rfl⟩
  have hC₃0 : 0 < C₃ := by
    rw [hC₃def]; exact add_pos (div_pos hsA ht0) (div_pos hC₂0 haq0)
  obtain ⟨C₄, hC₄def⟩ : ∃ C₄ : ℝ,
      C₄ = C₃ * (1 / (t * Real.sqrt A₀)) ^ al := ⟨_, rfl⟩
  have hC₄0 : 0 < C₄ := by
    rw [hC₄def]
    exact mul_pos hC₃0 (Real.rpow_pos_of_pos (by positivity) al)
  refine ⟨max 1 (max (C₂ / aq) C₄), by positivity, ?_⟩
  intro U zc P hfit
  -- ===================== STEP 5: THE CONSECUTIVE COMPARISON ==================
  -- Evaluate the difference of the two affine fits along the unit vector in the direction
  -- of `P j - P (j+1)`, on the SMALLER inscribed ball.  That is where `ρ_{j+1}` in the
  -- denominator comes from, and it is the only place the two fits are both used.
  have hcons : ∀ j : ℕ, ‖P j - P (j + 1)‖ ≤ (C₁ * aq) * q ^ j := by
    intro j
    obtain ⟨vv, hvvdef⟩ : ∃ vv : E, vv = P j - P (j + 1) := ⟨_, rfl⟩
    rw [← hvvdef]
    rcases eq_or_ne vv 0 with hv0 | hv0
    · rw [hv0, norm_zero]; positivity
    · have hvn : 0 < ‖vv‖ := norm_pos_iff.mpr hv0
      obtain ⟨hh, hhdef⟩ : ∃ hh : E, hh = (rho (j + 1) * ‖vv‖⁻¹) • vv := ⟨_, rfl⟩
      have hrnn : (0 : ℝ) ≤ rho (j + 1) * ‖vv‖⁻¹ :=
        mul_nonneg (le_of_lt (hrho0pos (j + 1))) (by positivity)
      have hhn : ‖hh‖ = rho (j + 1) := by
        rw [hhdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg hrnn]
        field_simp
      -- the inner product against the chosen direction
      have hinnv : (inner ℝ vv hh : ℝ) = rho (j + 1) * ‖vv‖ := by
        rw [hhdef, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      -- both fits apply at `hh`, since `‖hh‖ = ρ_{j+1} ≤ ρ_j`
      have hdom1 : ‖hh‖ ≤ Real.sqrt A₀ * ((1 / 2 : ℝ) ^ (j + 1) * r₀) ^ (1 + gam / 2) := by
        rw [hhn, ← hpwdef, hrhoapp (j + 1)]
      have hdom2 : ‖hh‖ ≤ Real.sqrt A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam / 2) := by
        rw [hhn, ← hpwdef, hrhoapp j]
        exact hrhomono j
      have hb1 := hfit j hh hdom2
      have hb2 := hfit (j + 1) hh hdom1
      -- the difference of the two fits is the inner product of the slope difference
      have hdiff : (inner ℝ vv hh : ℝ)
          = (U (zc + hh) - U zc - (inner ℝ (P (j + 1)) hh : ℝ))
            - (U (zc + hh) - U zc - (inner ℝ (P j) hh : ℝ)) := by
        rw [hvvdef, inner_sub_left]
        ring
      -- the radii, compared
      have hrjle : ((1 / 2 : ℝ) ^ (j + 1) * r₀) ^ (1 + gam)
          ≤ ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by linarith only [hgam0])
        have h : ((1 : ℝ) / 2) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ j := by
          rw [pow_succ]
          nlinarith only [pow_pos (show (0:ℝ) < 1/2 by norm_num) j]
        nlinarith only [h, hr₀]
      have hkey : rho (j + 1) * ‖vv‖ ≤ 2 * (A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam)) := by
        rw [← hinnv, hdiff]
        have ha1 := abs_le.mp hb1
        have ha2 := abs_le.mp hb2
        have h2 : A₀ * ((1 / 2 : ℝ) ^ (j + 1) * r₀) ^ (1 + gam)
            ≤ A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam) :=
          mul_le_mul_of_nonneg_left hrjle (le_of_lt hA₀)
        linarith only [ha1.1, ha1.2, ha2.1, ha2.2, h2]
      -- `A₀ r_j^{1+γ} = √A₀ (q^j a) ρ_j`, which is where the `ρ_{j+1}` cancels
      have hAsq : Real.sqrt A₀ * Real.sqrt A₀ = A₀ := Real.mul_self_sqrt (le_of_lt hA₀)
      have hexp : A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam)
          = Real.sqrt A₀ * (q ^ j * aq) * rho j := by
        have h1 : ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam)
            = ((1 / 2 : ℝ) ^ j * r₀) ^ (gam / 2) * ((1 / 2 : ℝ) ^ j * r₀) ^ pw := by
          rw [← Real.rpow_add (by positivity), hpwdef]
          congr 1
          ring
        rw [h1, hqgeo j, ← hrhoapp j]
        linear_combination
          (-(q ^ j * aq * ((1 / 2 : ℝ) ^ j * r₀) ^ pw)) * hAsq
      have hrhs : rho (j + 1) * ((C₁ * aq) * q ^ j)
          = 2 * (Real.sqrt A₀ * (q ^ j * aq) * rho j) := by
        rw [hrhostep j, hC₁def]
        field_simp
      have hfin : rho (j + 1) * ‖vv‖ ≤ rho (j + 1) * ((C₁ * aq) * q ^ j) := by
        rw [hrhs, ← hexp]
        exact hkey
      exact le_of_mul_le_mul_left hfin (hrho0pos (j + 1))
  -- ===================== THE GEOMETRIC TAIL AND THE LIMIT SLOPE ==============
  -- `|P_j - P_{j+1}| ≤ (C₁ a) q^j` with `0 < q < 1`, so the sequence is Cauchy; `E` is
  -- finite-dimensional hence complete, so it converges, and the geometric tail bound is
  -- the standard one.
  have hdistcons : ∀ j : ℕ, dist (P j) (P (j + 1)) ≤ (C₁ * aq) * q ^ j := by
    intro j
    rw [dist_eq_norm]
    exact hcons j
  obtain ⟨Pinf, hPinf⟩ :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q (C₁ * aq) hq1 hdistcons)
  have htail : ∀ j : ℕ, ‖P j - Pinf‖ ≤ (C₂ / aq) * (q ^ j * aq) := by
    intro j
    have h := dist_le_of_le_geometric_of_tendsto q (C₁ * aq) hq1 hdistcons hPinf j
    rw [dist_eq_norm] at h
    refine h.trans (le_of_eq ?_)
    rw [hC₂def]
    field_simp
  refine ⟨Pinf, ?_, ?_⟩
  · intro j
    rw [hqgeo j]
    refine (htail j).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  -- ===================== STEP 6: THE UNIFORM TAYLOR ESTIMATE =================
  intro h hhle
  rcases eq_or_ne h 0 with hh0 | hh0
  · rw [hh0, add_zero, inner_zero_right, norm_zero, Real.zero_rpow (by positivity)]
    simp
  have hhn0 : 0 < ‖h‖ := norm_pos_iff.mpr hh0
  rw [← hrho0] at hhle
  -- THE SCALE CHOICE: the least `m` with `ρ_m < ‖h‖` is a successor, because `ρ_0 ≥ ‖h‖`
  have hex : ∃ m : ℕ, rho m < ‖h‖ := by
    have hlim : Tendsto (fun m : ℕ => rho m) atTop (𝓝 0) := by
      have hp : Tendsto (fun m : ℕ => t ^ m) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt ht0) ht1
      have hc := hp.const_mul Bq
      rw [mul_zero] at hc
      exact hc.congr (fun m => (hrhogeo m).symm)
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const hhn0)
    exact ⟨m, hm m (le_refl m)⟩
  obtain ⟨m, hmlt, hmmin⟩ : ∃ m : ℕ, rho m < ‖h‖ ∧ ∀ k < m, ‖h‖ ≤ rho k := by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk => ?_⟩
    exact not_lt.mp (Nat.find_min hex hk)
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hmlt
    linarith only [hmlt, hhle]
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, m = j + 1 := ⟨m - 1, by omega⟩
  have hjle : ‖h‖ ≤ rho j := hmmin j (by omega)
  have hjlt : rho (j + 1) < ‖h‖ := by rw [← hjdef]; exact hmlt
  -- the two contributions at that scale
  have hdomj : ‖h‖ ≤ Real.sqrt A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam / 2) := by
    rw [← hpwdef, hrhoapp j]
    exact hjle
  have hbj := hfit j h hdomj
  have hinnb : |(inner ℝ (P j - Pinf) h : ℝ)| ≤ ‖P j - Pinf‖ * ‖h‖ :=
    abs_real_inner_le_norm _ _
  have hsplit2 : (inner ℝ (P j - Pinf) h : ℝ)
      = (U (zc + h) - U zc - (inner ℝ Pinf h : ℝ))
        - (U (zc + h) - U zc - (inner ℝ (P j) h : ℝ)) := by
    rw [inner_sub_left]; ring
  -- `A₀ r_j^{1+γ} ≤ (√A₀/t) (q^j a) ‖h‖`, from `ρ_{j+1} < ‖h‖`
  have hAsq2 : Real.sqrt A₀ * Real.sqrt A₀ = A₀ := Real.mul_self_sqrt (le_of_lt hA₀)
  have hexp2 : A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam)
      = Real.sqrt A₀ * (q ^ j * aq) * rho j := by
    have h1 : ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam)
        = ((1 / 2 : ℝ) ^ j * r₀) ^ (gam / 2) * ((1 / 2 : ℝ) ^ j * r₀) ^ pw := by
      rw [← Real.rpow_add (by positivity), hpwdef]
      congr 1
      ring
    rw [h1, hqgeo j, ← hrhoapp j]
    linear_combination (-(q ^ j * aq * ((1 / 2 : ℝ) ^ j * r₀) ^ pw)) * hAsq2
  have hrhojlt : rho j < ‖h‖ / t := by
    rw [lt_div_iff₀ ht0, mul_comm]
    rw [hrhostep j] at hjlt
    exact hjlt
  have hfirst : A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam)
      ≤ (Real.sqrt A₀ / t) * (q ^ j * aq) * ‖h‖ := by
    rw [hexp2]
    have hco : (0 : ℝ) ≤ Real.sqrt A₀ * (q ^ j * aq) := by positivity
    have h1 : Real.sqrt A₀ * (q ^ j * aq) * rho j
        ≤ Real.sqrt A₀ * (q ^ j * aq) * (‖h‖ / t) :=
      mul_le_mul_of_nonneg_left (le_of_lt hrhojlt) hco
    refine h1.trans (le_of_eq ?_)
    field_simp
  -- the combined bound, still at the scale `r_j`
  have hcomb : |U (zc + h) - U zc - (inner ℝ Pinf h : ℝ)| ≤ C₃ * (q ^ j * aq) * ‖h‖ := by
    have hb := abs_le.mp hbj
    have hi := abs_le.mp hinnb
    have ht := htail j
    have hq0j : (0 : ℝ) < q ^ j * aq := by positivity
    have hsec : ‖P j - Pinf‖ * ‖h‖ ≤ (C₂ / aq) * (q ^ j * aq) * ‖h‖ :=
      mul_le_mul_of_nonneg_right ht (le_of_lt hhn0)
    rw [abs_le]
    rw [hC₃def]
    constructor
    · nlinarith only [hb.1, hb.2, hi, hsec, hfirst, hsplit2, abs_nonneg
        (inner ℝ (P j - Pinf) h : ℝ), neg_abs_le (inner ℝ (P j - Pinf) h : ℝ),
        le_abs_self (inner ℝ (P j - Pinf) h : ℝ)]
    · nlinarith only [hb.1, hb.2, hi, hsec, hfirst, hsplit2, abs_nonneg
        (inner ℝ (P j - Pinf) h : ℝ), neg_abs_le (inner ℝ (P j - Pinf) h : ℝ),
        le_abs_self (inner ℝ (P j - Pinf) h : ℝ)]
  -- THE EXPONENT IDENTITY: `(1 + γ/2) α = γ/2` turns `r_j^{γ/2}` into `‖h‖^α`
  have hrjpw : ((1 / 2 : ℝ) ^ j * r₀) ^ pw < ‖h‖ / (t * Real.sqrt A₀) := by
    rw [lt_div_iff₀ (by positivity)]
    rw [← hrhoapp j] at hrhojlt
    rw [lt_div_iff₀ ht0] at hrhojlt
    nlinarith only [hrhojlt]
  have hqjal : q ^ j * aq ≤ (1 / (t * Real.sqrt A₀)) ^ al * ‖h‖ ^ al := by
    have hbase : q ^ j * aq = (((1 / 2 : ℝ) ^ j * r₀) ^ pw) ^ al := by
      rw [← Real.rpow_mul (by positivity) pw al, hpwal, hqgeo j]
    rw [hbase]
    have h1 : (((1 / 2 : ℝ) ^ j * r₀) ^ pw) ^ al
        ≤ (‖h‖ / (t * Real.sqrt A₀)) ^ al :=
      Real.rpow_le_rpow (by positivity) (le_of_lt hrjpw) (le_of_lt hal0)
    refine h1.trans (le_of_eq ?_)
    rw [div_eq_mul_inv, Real.mul_rpow (le_of_lt hhn0) (by positivity),
      show ((t * Real.sqrt A₀)⁻¹ : ℝ) = 1 / (t * Real.sqrt A₀) from by rw [one_div]]
    ring
  -- assemble
  have hC₃nn : (0 : ℝ) ≤ C₃ := le_of_lt hC₃0
  have hstep : C₃ * (q ^ j * aq) * ‖h‖
      ≤ C₄ * ‖h‖ ^ (1 + gam / (2 + gam)) := by
    have h1 : C₃ * (q ^ j * aq) ≤ C₃ * ((1 / (t * Real.sqrt A₀)) ^ al * ‖h‖ ^ al) :=
      mul_le_mul_of_nonneg_left hqjal hC₃nn
    have h2 : C₃ * (q ^ j * aq) * ‖h‖
        ≤ C₃ * ((1 / (t * Real.sqrt A₀)) ^ al * ‖h‖ ^ al) * ‖h‖ :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hhn0)
    refine h2.trans (le_of_eq ?_)
    rw [hC₄def, ← haldef]
    have hpow : ‖h‖ ^ al * ‖h‖ = ‖h‖ ^ (1 + al) := by
      rw [Real.rpow_add hhn0, Real.rpow_one]
      ring
    rw [show C₃ * ((1 / (t * Real.sqrt A₀)) ^ al * ‖h‖ ^ al) * ‖h‖
        = C₃ * (1 / (t * Real.sqrt A₀)) ^ al * (‖h‖ ^ al * ‖h‖) from by ring, hpow]
  refine (hcomb.trans hstep).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact le_trans (le_max_right _ _) (le_max_right _ _)
