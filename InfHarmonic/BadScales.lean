import InfHarmonic.IsBadScaleData
import InfHarmonic.FamilyFlatness
open Set Metric Filter Topology WithLp

/-- Selection of bad scales (paper Lemma 3.4): if the uniform power bound on the
family flatness modulus fails for every positive exponent, then selected
bad-scale data exists, with the enlarged parameter `32 λ i` good at every nearby
center and every comparable radius. -/
theorem BadScales (d : ℕ) (hd : 1 ≤ d)
    (hfail : ∀ B : ℝ, 0 < B → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ s₀ : ℝ, 0 < s₀ → s₀ ≤ 1 / 8 →
      ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧ B * s ^ γ < FlatnessModulus d hd s) :
    ∃ (γ s r lam : ℕ → ℝ) (U : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (z : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)),
      IsBadScaleData d hd γ s r lam U z := by
  classical
  -- ===================== NOTATION =====================
  -- `bd` is the family flatness modulus of eq:bs-bdef, `Dd` the distance to `∂G`.  Both are
  -- introduced with their defining equations so that no hole has to re-elaborate the
  -- underlying `sSup` / `infDist` term, and so that every hole's goal reads as in the .tex.
  obtain ⟨bd, hbddef⟩ : ∃ bd : ℝ → ℝ, bd = FlatnessModulus d hd := ⟨_, rfl⟩
  obtain ⟨Dd, hDddef⟩ : ∃ Dd : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ,
      Dd = fun zv => infDist zv
        (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) := ⟨_, rfl⟩
  -- ===================== PRELIMINARIES =====================
  -- `β_u(z,r) ∈ [0,1]`: it is the supremum of a subset of `(0,1)`, and pm-0026's junk value
  -- `sSup ∅ = 0` lies in that range, so NO nonemptiness is needed for these two bounds.
  have hbeta0 : ∀ (u : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
      0 ≤ BetaFlatness u zv rv := by
    intro u zv rv
    rw [BetaFlatness]
    exact Real.sSup_nonneg (fun x hx => le_of_lt hx.1.1)
  have hbeta1 : ∀ (u : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
      BetaFlatness u zv rv ≤ 1 := by
    intro u zv rv
    rw [BetaFlatness]
    exact Real.sSup_le (fun x hx => le_of_lt hx.1.2) zero_le_one
  -- the defining set of `b_d(s)` is bounded above by `1`; this is ALL the `≤ b_d(s)`
  -- comparisons need, and the .tex says so explicitly
  have hbdd : ∀ s : ℝ, BddAbove {b : ℝ | ∃ (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
      NormalizedInfFamily d U ∧
      zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
      0 < rv ∧
      rv ≤ s * infDist zv
        (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) ∧
      b = BetaFlatness U zv rv} := by
    intro s
    refine ⟨1, fun x hx => ?_⟩
    obtain ⟨U, zv, rv, -, -, -, -, rfl⟩ := hx
    exact hbeta1 U zv rv
  have hbd0 : ∀ s : ℝ, 0 ≤ bd s := by
    intro s
    rw [hbddef, FlatnessModulus]
    refine Real.sSup_nonneg (fun x hx => ?_)
    obtain ⟨U, zv, rv, -, -, -, -, rfl⟩ := hx
    exact hbeta0 U zv rv
  have hbd1 : ∀ s : ℝ, bd s ≤ 1 := by
    intro s
    rw [hbddef, FlatnessModulus]
    refine Real.sSup_le (fun x hx => ?_) zero_le_one
    obtain ⟨U, zv, rv, -, -, -, -, rfl⟩ := hx
    exact hbeta1 U zv rv
  -- `β_U(z,r) ≤ b_d(s)` for every triple admissible at the scale `s`
  have hbetale : ∀ (s : ℝ) (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
      NormalizedInfFamily d U →
      zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) →
      0 < rv → rv ≤ s * Dd zv → BetaFlatness U zv rv ≤ bd s := by
    intro s U zv rv hU hzv hrv hrle
    rw [hDddef] at hrle
    rw [hbddef, FlatnessModulus]
    exact le_csSup (hbdd s) ⟨U, zv, rv, hU, hzv, hrv, hrle, rfl⟩
  -- every parameter strictly between `β_u(z,r)` and `1` is GOOD: otherwise it would sit in
  -- the set whose supremum is `β_u(z,r)`
  have hgood : ∀ (u : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv lamv : ℝ),
      0 < lamv → lamv < 1 → BetaFlatness u zv rv < lamv →
      ∃ P, IsCylinderFit u zv rv lamv P := by
    intro u zv rv lamv hlam0 hlam1 hlt
    by_contra hno
    have hmem : lamv ∈ {lam : ℝ | lam ∈ Set.Ioo (0 : ℝ) 1 ∧
        ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          IsCylinderFit u zv rv lam P} := ⟨⟨hlam0, hlam1⟩, hno⟩
    have hle : lamv ≤ BetaFlatness u zv rv := by
      rw [BetaFlatness]
      exact le_csSup ⟨1, fun x hx => le_of_lt hx.1.2⟩ hmem
    exact absurd hlt (not_lt.mpr hle)
  -- eq:bs-D: `D(z) = 3/4 - |z|` on `G`, the frontier being the sphere of radius `3/4`
  have hDeq : ∀ zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4),
      Dd zv = 3 / 4 - ‖zv‖ := by
    intro zv hzv
    rw [mem_ball, dist_zero_right] at hzv
    rw [hDddef]
    show infDist zv
      (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4)))
      = 3 / 4 - ‖zv‖
    rw [frontier_ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
      (by norm_num : (3 : ℝ) / 4 ≠ 0)]
    -- the radial projection: a point of the sphere at distance exactly `3/4 - |z|`
    obtain ⟨w, hwn, hwd⟩ : ∃ w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        ‖w‖ = 3 / 4 ∧ ‖zv - w‖ = 3 / 4 - ‖zv‖ := by
      rcases eq_or_ne zv 0 with h0 | h0
      · obtain ⟨v, hv⟩ := exists_ne (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
        have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
        have hwvn : ‖(3 / 4 * ‖v‖⁻¹) • v‖ = 3 / 4 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc,
            inv_mul_cancel₀ hvn, mul_one]
        refine ⟨(3 / 4 * ‖v‖⁻¹) • v, hwvn, ?_⟩
        rw [h0, zero_sub, norm_neg, hwvn, norm_zero]
        ring
      · have hzn : (0 : ℝ) < ‖zv‖ := norm_pos_iff.mpr h0
        refine ⟨(3 / 4 / ‖zv‖) • zv, ?_, ?_⟩
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
            div_mul_cancel₀ _ (ne_of_gt hzn)]
        · rw [show zv - (3 / 4 / ‖zv‖) • zv = (1 - 3 / 4 / ‖zv‖) • zv from by
            rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
          have hneg : 1 - 3 / 4 / ‖zv‖ ≤ 0 := by
            rw [sub_nonpos, le_div_iff₀ hzn]
            linarith only [hzv]
          rw [abs_of_nonpos hneg]
          field_simp
          ring
    have hwmem : w ∈ sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) := by
      rw [mem_sphere, dist_zero_right, hwn]
    refine le_antisymm ?_ ?_
    · refine le_trans (infDist_le_dist_of_mem hwmem) ?_
      rw [dist_eq_norm, hwd]
    · rw [Metric.le_infDist ⟨w, hwmem⟩]
      intro y hy
      rw [mem_sphere, dist_zero_right] at hy
      rw [dist_eq_norm, norm_sub_rev zv y]
      linarith only [norm_sub_norm_le y zv, hy]
  -- `D` is `1`-Lipschitz, being a distance to a fixed set
  have hDlip : ∀ (zv wv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)),
      Dd zv ≤ Dd wv + ‖zv - wv‖ := by
    intro zv wv
    rw [hDddef]
    show infDist zv _ ≤ infDist wv _ + ‖zv - wv‖
    rw [← dist_eq_norm]
    exact infDist_le_infDist_add_dist
  -- ===================== THE EXPONENTS =====================
  -- `γ_i = 1/(i+1)`: positive, at most `1`, and tending to `0`.
  obtain ⟨gam, hgamdef⟩ : ∃ gam : ℕ → ℝ, gam = fun i : ℕ => 1 / ((i : ℝ) + 1) := ⟨_, rfl⟩
  have hgam0 : ∀ i, 0 < gam i := by
    intro i; rw [hgamdef]; positivity
  have hgam1 : ∀ i, gam i ≤ 1 := by
    intro i
    rw [hgamdef]
    show 1 / ((i : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    linarith only [Nat.cast_nonneg (α := ℝ) i]
  have hgamlim : Tendsto gam atTop (𝓝 0) := by
    rw [hgamdef]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- ===================== STEP 1: THE RUNNING MAXIMUM =====================
  -- eq:bs-sigma, eq:bs-approxmax, eq:bs-running, eq:bs-si and eq:bs-bpos.  The auxiliary
  -- quantities `N`, `T`, `σ` and `M` are local to the index, so the whole step is one block
  -- that delivers exactly the five facts about `s_i` that Steps 2-4 consume.
  have step1 : ∀ i : ℕ, ∃ si : ℝ,
      0 < si ∧ si < 1 / ((i : ℝ) + 1) ∧ si ≤ 1 / 8 ∧ 0 < bd si ∧
      (∀ s : ℝ, si ≤ s → s ≤ 1 / 8 →
        bd s / s ^ gam i ≤ 2 * (bd si / si ^ gam i)) := by
    intro i
    -- `N ≥ max(8, i+1)`, so `1/N ≤ 1/8` and `1/N ≤ 1/(i+1)`
    obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = max 8 (i + 1) := ⟨_, rfl⟩
    have hN8 : (8 : ℕ) ≤ N := by rw [hNdef]; exact le_max_left _ _
    have hNi : i + 1 ≤ N := by rw [hNdef]; exact le_max_right _ _
    have hN8r : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
    have hNir : (i : ℝ) + 1 ≤ (N : ℝ) := by
      have h : ((i + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNi
      rw [Nat.cast_add, Nat.cast_one] at h
      exact h
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith only [hN8r]
    have hinvN0 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hinvN8 : 1 / (N : ℝ) ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) hN8r
    have hinvNi : 1 / (N : ℝ) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hNir
    -- `g s = b_d(s)/s^{γ_i}`, nonnegative wherever `s > 0`
    obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun s : ℝ => bd s / s ^ gam i := ⟨_, rfl⟩
    have hg0 : ∀ s : ℝ, 0 < s → 0 ≤ g s := by
      intro s hs
      rw [hgdef]
      show 0 ≤ bd s / s ^ gam i
      exact div_nonneg (hbd0 s) (le_of_lt (Real.rpow_pos_of_pos hs _))
    -- `T = sup g on [1/N, 1/8]`, finite because `b_d ≤ 1` and `s^{γ_i} ≥ (1/N)^{γ_i}` there
    obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = sSup (g '' Set.Icc (1 / (N : ℝ)) (1 / 8)) := ⟨_, rfl⟩
    have hTbdd : BddAbove (g '' Set.Icc (1 / (N : ℝ)) (1 / 8)) := by
      refine ⟨((1 / (N : ℝ)) ^ gam i)⁻¹, ?_⟩
      rintro y ⟨s, ⟨hs1, hs2⟩, rfl⟩
      have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hinvN0 hs1
      have hrp : (0 : ℝ) < s ^ gam i := Real.rpow_pos_of_pos hs0 _
      have hbase : (1 / (N : ℝ)) ^ gam i ≤ s ^ gam i :=
        Real.rpow_le_rpow (le_of_lt hinvN0) hs1 (le_of_lt (hgam0 i))
      have hbase0 : (0 : ℝ) < (1 / (N : ℝ)) ^ gam i := Real.rpow_pos_of_pos hinvN0 _
      rw [hgdef]
      show bd s / s ^ gam i ≤ ((1 / (N : ℝ)) ^ gam i)⁻¹
      rw [div_le_iff₀ hrp, inv_mul_eq_div, le_div_iff₀ hbase0]
      nlinarith only [hbd1 s, hbase, hbase0, hrp]
    have hT0 : 0 ≤ T := by
      rw [hTdef]
      refine Real.sSup_nonneg ?_
      rintro y ⟨s, ⟨hs1, -⟩, rfl⟩
      exact hg0 s (lt_of_lt_of_le hinvN0 hs1)
    have hTle : ∀ s : ℝ, 1 / (N : ℝ) ≤ s → s ≤ 1 / 8 → g s ≤ T := by
      intro s hs1 hs2
      rw [hTdef]
      exact le_csSup hTbdd ⟨s, ⟨hs1, hs2⟩, rfl⟩
    -- eq:bs-sigma: the failure hypothesis at `B = 2T+2` and `s₀ = 1/N` produces a scale
    -- STRICTLY below `1/N`, because `g σ > T` while `g ≤ T` on `[1/N, 1/8]`
    obtain ⟨sg, hsg0, hsgN, hsgg⟩ : ∃ sg : ℝ, 0 < sg ∧ sg < 1 / (N : ℝ) ∧ 2 * T + 2 < g sg := by
      obtain ⟨sg, hsg0, hsgle, hsgb⟩ := hfail (2 * T + 2) (by linarith only [hT0]) (gam i)
        (hgam0 i) (hgam1 i) (1 / (N : ℝ)) hinvN0 hinvN8
      have hrp : (0 : ℝ) < sg ^ gam i := Real.rpow_pos_of_pos hsg0 _
      have hgsg : 2 * T + 2 < g sg := by
        rw [hgdef]
        show 2 * T + 2 < bd sg / sg ^ gam i
        rw [lt_div_iff₀ hrp, hbddef]
        exact hsgb
      refine ⟨sg, hsg0, ?_, hgsg⟩
      rcases lt_or_eq_of_le hsgle with h | h
      · exact h
      · exact absurd (hTle sg (le_of_eq h.symm) (by rw [h]; exact hinvN8))
          (not_le.mpr (by linarith only [hgsg, hT0]))
    -- `M = sup g on [σ, 1/8]`; its defining set is NONEMPTY with witness `σ` itself,
    -- which is what makes the approximation property available (pm-0026)
    obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = sSup (g '' Set.Icc sg (1 / 8)) := ⟨_, rfl⟩
    have hsg8 : sg ≤ 1 / 8 := le_of_lt (lt_of_lt_of_le hsgN hinvN8)
    have hMbdd : BddAbove (g '' Set.Icc sg (1 / 8)) := by
      refine ⟨(sg ^ gam i)⁻¹, ?_⟩
      rintro y ⟨s, ⟨hs1, hs2⟩, rfl⟩
      have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hsg0 hs1
      have hrp : (0 : ℝ) < s ^ gam i := Real.rpow_pos_of_pos hs0 _
      have hbase : sg ^ gam i ≤ s ^ gam i :=
        Real.rpow_le_rpow (le_of_lt hsg0) hs1 (le_of_lt (hgam0 i))
      have hbase0 : (0 : ℝ) < sg ^ gam i := Real.rpow_pos_of_pos hsg0 _
      rw [hgdef]
      show bd s / s ^ gam i ≤ (sg ^ gam i)⁻¹
      rw [div_le_iff₀ hrp, inv_mul_eq_div, le_div_iff₀ hbase0]
      nlinarith only [hbd1 s, hbase, hbase0, hrp]
    have hMne : (g '' Set.Icc sg (1 / 8)).Nonempty :=
      ⟨g sg, ⟨sg, ⟨le_refl sg, hsg8⟩, rfl⟩⟩
    have hMge : g sg ≤ M := by
      rw [hMdef]
      exact le_csSup hMbdd ⟨sg, ⟨le_refl sg, hsg8⟩, rfl⟩
    have hMle : ∀ s : ℝ, sg ≤ s → s ≤ 1 / 8 → g s ≤ M := by
      intro s hs1 hs2
      rw [hMdef]
      exact le_csSup hMbdd ⟨s, ⟨hs1, hs2⟩, rfl⟩
    have hMgt2 : 2 < M := by linarith only [hMge, hsgg, hT0]
    -- eq:bs-approxmax: the approximation property of `M`
    obtain ⟨si, hsi1, hsi8, hsiapp⟩ : ∃ si : ℝ, sg ≤ si ∧ si ≤ 1 / 8 ∧ M / 2 < g si := by
      obtain ⟨y, hy, hylt⟩ := exists_lt_of_lt_csSup hMne
        (show M / 2 < sSup (g '' Set.Icc sg (1 / 8)) by rw [← hMdef]; linarith only [hMgt2])
      obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := hy
      exact ⟨s, hs1, hs2, hylt⟩
    have hsi0 : 0 < si := lt_of_lt_of_le hsg0 hsi1
    have hsirp : (0 : ℝ) < si ^ gam i := Real.rpow_pos_of_pos hsi0 _
    -- eq:bs-si: `g s_i > T` while `g ≤ T` on `[1/N, 1/8]`, so `s_i < 1/N ≤ 1/(i+1)`
    have hsiT : T < g si := by linarith only [hsiapp, hMge, hsgg, hT0]
    have hsiN : si < 1 / (N : ℝ) := by
      rcases lt_or_ge si (1 / (N : ℝ)) with h | h
      · exact h
      · exact absurd (hTle si h hsi8) (not_le.mpr hsiT)
    -- eq:bs-bpos: `g s_i > M/2 > 1 > 0`
    have hbdsi : 0 < bd si := by
      have h1 : 1 < g si := by linarith only [hsiapp, hMgt2]
      rw [hgdef] at h1
      have h2 : 1 < bd si / si ^ gam i := h1
      rw [lt_div_iff₀ hsirp] at h2
      linarith only [h2, hsirp]
    -- eq:bs-running: `g s ≤ M < 2 g s_i` for `s ∈ [s_i, 1/8] ⊆ [σ, 1/8]`
    refine ⟨si, hsi0, lt_of_lt_of_le hsiN hinvNi, hsi8, hbdsi, ?_⟩
    intro s hs1 hs2
    have h := hMle s (le_trans hsi1 hs1) hs2
    rw [hgdef] at h hsiapp
    have h' : bd s / s ^ gam i ≤ M := h
    have h'' : M / 2 < bd si / si ^ gam i := hsiapp
    linarith only [h', h'']
  choose sq hsq0 hsqi hsq8 hbdsq hrunning using step1
  -- ===================== STEP 2: THE BAD TRIPLE AND THE BAD PARAMETER ==============
  -- eq:bs-triple, eq:bs-lam and eq:bs-sandwich.  BOTH approximation properties live here,
  -- and both are licensed by a strict positivity rather than obstructed by pm-0026: the
  -- junk value `sSup ∅ = 0` is exactly what turns `b_d(s_i) > 0` into nonemptiness of the
  -- set of eq:bs-bdef, and `β_{U_i}(z_i,r_i) > 0` does the same one level down.
  have step2 : ∀ i : ℕ, ∃ (Uv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv lamv : ℝ),
      NormalizedInfFamily d Uv ∧
      zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
      0 < rv ∧ rv ≤ sq i * Dd zv ∧
      0 < lamv ∧ lamv < 1 ∧
      (¬ ∃ P, IsCylinderFit Uv zv rv lamv P) ∧
      bd (sq i) / 4 < lamv ∧ lamv ≤ bd (sq i) := by
    intro i
    -- eq:bs-triple
    obtain ⟨Uv, zv, rv, hUv, hzv, hrv0, hrvle, hbeta⟩ :
        ∃ (Uv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
          (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
          NormalizedInfFamily d Uv ∧
          zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
          0 < rv ∧ rv ≤ sq i * Dd zv ∧
          bd (sq i) / 2 < BetaFlatness Uv zv rv := by
      have hsup : bd (sq i) = sSup {b : ℝ | ∃ (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
          (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
          NormalizedInfFamily d U ∧
          zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
          0 < rv ∧
          rv ≤ sq i * infDist zv
            (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) ∧
          b = BetaFlatness U zv rv} := by
        rw [hbddef, FlatnessModulus]
      have hne : {b : ℝ | ∃ (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
          (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
          NormalizedInfFamily d U ∧
          zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
          0 < rv ∧
          rv ≤ sq i * infDist zv
            (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) ∧
          b = BetaFlatness U zv rv}.Nonempty := by
        rcases Set.eq_empty_or_nonempty {b : ℝ | ∃ (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
            (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
            NormalizedInfFamily d U ∧
            zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
            0 < rv ∧
            rv ≤ sq i * infDist zv
              (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) ∧
            b = BetaFlatness U zv rv} with hemp | hne'
        · exfalso
          have h0 := hbdsq i
          rw [hsup, hemp, Real.sSup_empty] at h0
          exact lt_irrefl 0 h0
        · exact hne'
      obtain ⟨b, hbmem, hblt⟩ := exists_lt_of_lt_csSup hne
        (show bd (sq i) / 2 < sSup _ by rw [← hsup]; linarith only [hbdsq i])
      obtain ⟨Uv, zv, rv, hUv, hzv, hrv0, hrvle, rfl⟩ := hbmem
      exact ⟨Uv, zv, rv, hUv, hzv, hrv0, by rw [hDddef]; exact hrvle, hblt⟩
    have hbetapos : 0 < BetaFlatness Uv zv rv := by linarith only [hbeta, hbdsq i]
    -- eq:bs-lam: the same argument one level down, inside `BetaFlatness`
    obtain ⟨lamv, hlam0, hlam1, hlambad, hlamgt⟩ :
        ∃ lamv : ℝ, 0 < lamv ∧ lamv < 1 ∧
          (¬ ∃ P, IsCylinderFit Uv zv rv lamv P) ∧
          BetaFlatness Uv zv rv / 2 < lamv := by
      have hsup : BetaFlatness Uv zv rv = sSup {lam : ℝ | lam ∈ Set.Ioo (0 : ℝ) 1 ∧
          ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
            IsCylinderFit Uv zv rv lam P} := by
        rw [BetaFlatness]
      have hne : {lam : ℝ | lam ∈ Set.Ioo (0 : ℝ) 1 ∧
          ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
            IsCylinderFit Uv zv rv lam P}.Nonempty := by
        rcases Set.eq_empty_or_nonempty {lam : ℝ | lam ∈ Set.Ioo (0 : ℝ) 1 ∧
            ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
              IsCylinderFit Uv zv rv lam P} with hemp | hne'
        · exfalso
          rw [hsup, hemp, Real.sSup_empty] at hbetapos
          exact lt_irrefl 0 hbetapos
        · exact hne'
      obtain ⟨lamv, hlamvmem, hlamvgt⟩ := exists_lt_of_lt_csSup hne
        (show BetaFlatness Uv zv rv / 2 < sSup _ by rw [← hsup]; linarith only [hbetapos])
      exact ⟨lamv, hlamvmem.1.1, hlamvmem.1.2, hlamvmem.2, hlamvgt⟩
    -- eq:bs-sandwich: `λ_i ≤ β_{U_i}(z_i,r_i) ≤ b_d(s_i)`, the first because `λ_i` sits in
    -- the set whose supremum is `β`, the second because the triple is admissible for `s_i`
    have hlamle : lamv ≤ BetaFlatness Uv zv rv := by
      rw [BetaFlatness]
      exact le_csSup ⟨1, fun x hx => le_of_lt hx.1.2⟩ ⟨⟨hlam0, hlam1⟩, hlambad⟩
    have hbetale' : BetaFlatness Uv zv rv ≤ bd (sq i) :=
      hbetale (sq i) Uv zv rv hUv hzv hrv0 hrvle
    exact ⟨Uv, zv, rv, lamv, hUv, hzv, hrv0, hrvle, hlam0, hlam1, hlambad,
      by linarith only [hlamgt, hbeta], le_trans hlamle hbetale'⟩
  choose Uq zq rq lamq hUq hzq hrq0 hrqle hlam0 hlam1 hlambad hsand1 hsand2 using step2
  -- ===================== STEP 3: `λ_i → 0` =====================
  -- eq:bs-lamzero.  `s_i → 0` by eq:bs-si, `b_d(s_i) → 0` by `FamilyFlatness`, and
  -- `λ_i ≤ b_d(s_i)` by eq:bs-sandwich.
  have hsqlim : Tendsto sq atTop (𝓝 0) :=
    squeeze_zero (fun i => le_of_lt (hsq0 i)) (fun i => le_of_lt (hsqi i))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hbdlim : Tendsto (fun i => bd (sq i)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨s0, hs00, -, hs0b⟩ := FamilyFlatness d hd (ε / 2) (by linarith only [hε])
    obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp (hsqlim.eventually_lt_const hs00)
    refine ⟨i₀, fun i hi => ?_⟩
    have h1 : bd (sq i) ≤ ε / 2 := by
      rw [hbddef]
      exact hs0b (sq i) (hsq0 i) (le_of_lt (hi₀ i hi))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hbd0 (sq i))]
    linarith only [h1, hε]
  have hlamlim : Tendsto lamq atTop (𝓝 0) :=
    squeeze_zero (fun i => le_of_lt (hlam0 i)) (fun i => hsand2 i) hbdlim
  -- ===================== STEP 4: THE UNIFORMITY WITH `Λ = 32` =====================
  -- eq:bs-thresholds, eq:bs-Mr, eq:bs-rho and the three conclusions (4a), (4b), (4c).
  -- The factor `32 = 2 · 4 · 4` is: `2` from eq:bs-running, `4` from `b_d(s_i) < 4 λ_i`
  -- (the left half of eq:bs-sandwich), and `4` from `(2 M_*)^{γ_i} < 4`.
  have step4 : ∀ Ms : ℝ, 2 ≤ Ms → ∃ i₀ : ℕ, ∀ i ≥ i₀,
      ∀ w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖w - zq i‖ ≤ Ms * rq i →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ Ms * rq i →
          w ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
          ρ ≤ 1 / 8 * Dd w ∧
          ∃ P, IsCylinderFit (Uq i) w ρ (32 * lamq i) P := by
    intro Ms hMs
    have hMs0 : (0 : ℝ) < Ms := by linarith only [hMs]
    -- eq:bs-thresholds
    obtain ⟨i₀, hthr⟩ : ∃ i₀ : ℕ, ∀ i ≥ i₀,
        Ms * sq i < 1 / 2 ∧ 2 * Ms * sq i ≤ 1 / 8 ∧
        (2 * Ms) ^ gam i < 4 ∧ 32 * lamq i < 1 := by
      have e1 : ∀ᶠ i in atTop, Ms * sq i < 1 / 2 := by
        have h : Tendsto (fun i => Ms * sq i) atTop (𝓝 0) := by
          have h' := hsqlim.const_mul Ms
          rw [mul_zero] at h'
          exact h'
        exact h.eventually_lt_const (by norm_num)
      have e2 : ∀ᶠ i in atTop, 2 * Ms * sq i ≤ 1 / 8 := by
        have h : Tendsto (fun i => 2 * Ms * sq i) atTop (𝓝 0) := by
          have h' := hsqlim.const_mul (2 * Ms)
          rw [mul_zero] at h'
          exact h'
        filter_upwards [h.eventually_lt_const (show (0:ℝ) < 1 / 8 by norm_num)] with i hi
        exact le_of_lt hi
      have e3 : ∀ᶠ i in atTop, (2 * Ms) ^ gam i < 4 := by
        have hcont : ContinuousAt (fun x : ℝ => (2 * Ms) ^ x) 0 :=
          Real.continuousAt_const_rpow (by positivity)
        have h : Tendsto (fun i => (2 * Ms) ^ gam i) atTop (𝓝 ((2 * Ms) ^ (0 : ℝ))) :=
          hcont.tendsto.comp hgamlim
        rw [Real.rpow_zero] at h
        exact h.eventually_lt_const (by norm_num)
      have e4 : ∀ᶠ i in atTop, 32 * lamq i < 1 := by
        have h : Tendsto (fun i => 32 * lamq i) atTop (𝓝 0) := by
          have h' := hlamlim.const_mul (32 : ℝ)
          rw [mul_zero] at h'
          exact h'
        exact h.eventually_lt_const (by norm_num)
      obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (e3.and e4)))
      exact ⟨i₀, fun i hi => ⟨(hi₀ i hi).1, (hi₀ i hi).2.1, (hi₀ i hi).2.2.1,
        (hi₀ i hi).2.2.2⟩⟩
    refine ⟨i₀, fun i hi w hw ρ hρ0 hρle => ?_⟩
    obtain ⟨ht1, ht2, ht3, ht4⟩ := hthr i hi
    have hzn : ‖zq i‖ < 3 / 4 := by
      have h := hzq i
      rw [mem_ball, dist_zero_right] at h
      exact h
    have hDz : Dd (zq i) = 3 / 4 - ‖zq i‖ := hDeq (zq i) (hzq i)
    have hDz0 : 0 < Dd (zq i) := by rw [hDz]; linarith only [hzn]
    -- eq:bs-Mr
    have hMr : Ms * rq i < 1 / 2 * Dd (zq i) := by
      have h1 : Ms * rq i ≤ Ms * (sq i * Dd (zq i)) :=
        mul_le_mul_of_nonneg_left (hrqle i) (le_of_lt hMs0)
      have h2 : Ms * sq i * Dd (zq i) < 1 / 2 * Dd (zq i) :=
        mul_lt_mul_of_pos_right ht1 hDz0
      nlinarith only [h1, h2]
    -- (4a)
    have h4a : w ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) := by
      rw [mem_ball, dist_zero_right]
      have h1 : ‖w‖ ≤ ‖zq i‖ + ‖w - zq i‖ := by
        have := norm_add_le (zq i) (w - zq i)
        rwa [add_sub_cancel] at this
      rw [hDz] at hMr
      linarith only [h1, hw, hMr, hzn]
    -- (4b) eq:bs-rho, through the 1-Lipschitz bound on `D`
    have hDw0 : 0 ≤ Dd w := by
      rw [hDddef]
      exact infDist_nonneg
    have hDw : Dd (zq i) ≤ 2 * Dd w := by
      have h1 := hDlip (zq i) w
      have h2 : ‖zq i - w‖ = ‖w - zq i‖ := norm_sub_rev _ _
      rw [h2] at h1
      rw [hDz] at h1 hMr ⊢
      linarith only [h1, hw, hMr]
    have hρstep : ρ ≤ 2 * Ms * sq i * Dd w := by
      have h1 : ρ ≤ Ms * (sq i * Dd (zq i)) :=
        le_trans hρle (mul_le_mul_of_nonneg_left (hrqle i) (le_of_lt hMs0))
      have h2 : Ms * sq i * Dd (zq i) ≤ Ms * sq i * (2 * Dd w) :=
        mul_le_mul_of_nonneg_left hDw (le_of_lt (mul_pos hMs0 (hsq0 i)))
      nlinarith only [h1, h2]
    have h4b : ρ ≤ 1 / 8 * Dd w := by
      have h : 2 * Ms * sq i * Dd w ≤ 1 / 8 * Dd w :=
        mul_le_mul_of_nonneg_right ht2 hDw0
      linarith only [hρstep, h]
    -- (4c) the three-factor chain of eq:bs-thresholds / eq:bs-running / eq:bs-sandwich
    refine ⟨h4a, h4b, ?_⟩
    have hsqi0 : 0 < sq i := hsq0 i
    have hsqrp : (0 : ℝ) < sq i ^ gam i := Real.rpow_pos_of_pos hsqi0 _
    have hbigrp : (0 : ℝ) < (2 * Ms) ^ gam i :=
      Real.rpow_pos_of_pos (by linarith only [hMs0]) _
    -- `(U_i, w, ρ)` is admissible for the scale `2 M_* s_i`
    have hadm : BetaFlatness (Uq i) w ρ ≤ bd (2 * Ms * sq i) :=
      hbetale (2 * Ms * sq i) (Uq i) w ρ (hUq i) h4a hρ0 hρstep
    -- eq:bs-running at `s = 2 M_* s_i`
    have hsle : sq i ≤ 2 * Ms * sq i := by nlinarith only [hMs, hsqi0]
    have hrun := hrunning i (2 * Ms * sq i) hsle ht2
    have hsplit : (2 * Ms * sq i) ^ gam i = (2 * Ms) ^ gam i * sq i ^ gam i :=
      Real.mul_rpow (by linarith only [hMs0]) (le_of_lt hsqi0)
    have hsqne : sq i ^ gam i ≠ 0 := ne_of_gt hsqrp
    have hbd2 : bd (2 * Ms * sq i) ≤ 2 * bd (sq i) * (2 * Ms) ^ gam i := by
      have hA : (0 : ℝ) < (2 * Ms * sq i) ^ gam i :=
        Real.rpow_pos_of_pos (mul_pos (by linarith only [hMs0]) hsqi0) _
      rw [div_le_iff₀ hA, hsplit] at hrun
      have hid : 2 * (bd (sq i) / sq i ^ gam i) * ((2 * Ms) ^ gam i * sq i ^ gam i)
          = 2 * bd (sq i) * (2 * Ms) ^ gam i := by
        field_simp
      rw [hid] at hrun
      exact hrun
    -- `b_d(s_i) < 4 λ_i` and `(2 M_*)^{γ_i} < 4`
    have hbdlt : bd (sq i) < 4 * lamq i := by linarith only [hsand1 i]
    have hbd0' : 0 < bd (sq i) := hbdsq i
    have hbetalt : BetaFlatness (Uq i) w ρ < 32 * lamq i := by
      have hp1 : bd (sq i) * (2 * Ms) ^ gam i < 4 * lamq i * (2 * Ms) ^ gam i :=
        mul_lt_mul_of_pos_right hbdlt hbigrp
      have hp2 : 4 * lamq i * (2 * Ms) ^ gam i < 4 * lamq i * 4 :=
        mul_lt_mul_of_pos_left ht3 (by linarith only [hlam0 i])
      linarith only [hadm, hbd2, hp1, hp2]
    exact hgood (Uq i) w ρ (32 * lamq i) (by linarith only [hlam0 i]) ht4 hbetalt
  -- ===================== CONCLUSION =====================
  -- the twelve clauses of `IsBadScaleData`, in the order the .tex's Conclusion lists them
  refine ⟨gam, sq, rq, lamq, Uq, zq, ?_⟩
  rw [IsBadScaleData]
  refine ⟨hgam0, hgamlim, hsq0, hsqlim, hlam0, hlamlim, hUq, hzq, hrq0, ?_, hlambad, ?_⟩
  · intro i
    have h := hrqle i
    simp only [hDddef] at h
    exact h
  · intro Ms hMs
    obtain ⟨i₀, hi₀⟩ := step4 Ms hMs
    refine ⟨i₀, fun i hi w hw ρ hρ0 hρle => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hi₀ i hi w hw ρ hρ0 hρle
    refine ⟨h1, ?_, h3⟩
    simp only [hDddef] at h2
    exact h2
