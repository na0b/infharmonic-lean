import InfHarmonic.ConeComparison
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Lemma 2.3, local Lipschitz bound: if the oscillation of an infinity-harmonic
`w` on `closedBall z₀ (ρ + σ)` is at most `Λ σ`, then `w` is
`Λ`-Lipschitz on `closedBall z₀ ρ`. -/
theorem InfHarmonicLocLipschitz (D : Set E) (w : E → ℝ) (hw : IsInfHarmonicOn D w)
    (z₀ : E) (ρ σ Λ : ℝ) (hρ : 0 ≤ ρ) (hσ : 0 < σ)
    (hsub : closedBall z₀ (ρ + σ) ⊆ D)
    (hosc : ∀ a ∈ closedBall z₀ (ρ + σ), ∀ b ∈ closedBall z₀ (ρ + σ),
      |w a - w b| ≤ Λ * σ) :
    ∀ a ∈ closedBall z₀ ρ, ∀ b ∈ closedBall z₀ ρ, |w a - w b| ≤ Λ * ‖a - b‖ := by
  -- Step 0: the oscillation hypothesis at `a = b = z₀` forces `0 ≤ Λ`.
  have hρσ : 0 < ρ + σ := by linarith
  have hz₀ : z₀ ∈ closedBall z₀ (ρ + σ) := mem_closedBall_self hρσ.le
  have hΛ : 0 ≤ Λ := by
    have h0 : |w z₀ - w z₀| ≤ Λ * σ := hosc z₀ hz₀ z₀ hz₀
    simp only [sub_self, abs_zero] at h0
    exact le_of_mul_le_mul_right (by linarith) hσ
  -- Step 1: a Lipschitz estimate for nearby pairs.  `ConeComparison` is a closed
  -- theorem, so its three conclusions are used here as a black box.
  have near : ∀ a ∈ closedBall z₀ ρ, ∀ Z ∈ closedBall a σ,
      |w Z - w a| ≤ Λ * ‖Z - a‖ := by
    intro a ha Z hZ
    rw [mem_closedBall] at ha
    have hain : a ∈ closedBall z₀ (ρ + σ) := by
      rw [mem_closedBall]; linarith
    have hinc : closedBall a σ ⊆ closedBall z₀ (ρ + σ) := by
      intro Y hY
      rw [mem_closedBall] at hY ⊢
      calc dist Y z₀ ≤ dist Y a + dist a z₀ := dist_triangle _ _ _
        _ ≤ σ + ρ := add_le_add hY ha
        _ = ρ + σ := by ring
    have hcomp : ∀ h ∈ closedBall (0 : E) σ, a + h ∈ closedBall z₀ (ρ + σ) := by
      intro h hh
      refine hinc ?_
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      rw [mem_closedBall, dist_eq_norm, sub_zero] at hh
      exact hh
    -- both slopes at the centre `a` and radius `σ` are at most `Λ`
    have hupb : ConeSlopeUpper w a σ ≤ Λ := by
      simp only [ConeSlopeUpper]
      refine csSup_le ⟨(w (a + 0) - w a) / σ, ⟨0, mem_closedBall_self hσ.le, rfl⟩⟩ ?_
      rintro x ⟨h, hh, rfl⟩
      show (w (a + h) - w a) / σ ≤ Λ
      rw [div_le_iff₀ hσ]
      have hb := abs_le.mp (hosc (a + h) (hcomp h hh) a hain)
      linarith [hb.2]
    have hlob : ConeSlopeLower w a σ ≤ Λ := by
      simp only [ConeSlopeLower]
      refine csSup_le ⟨(-(w (a + 0) - w a)) / σ, ⟨0, mem_closedBall_self hσ.le, rfl⟩⟩ ?_
      rintro x ⟨h, hh, rfl⟩
      show (-(w (a + h) - w a)) / σ ≤ Λ
      rw [div_le_iff₀ hσ]
      have hb := abs_le.mp (hosc (a + h) (hcomp h hh) a hain)
      linarith [hb.1]
    obtain ⟨hup, hlo, -⟩ := ConeComparison D w hw a σ hσ (hinc.trans hsub)
    have hZn : (0 : ℝ) ≤ ‖Z - a‖ := norm_nonneg _
    have h1 := hup Z hZ
    have h2 := hlo Z hZ
    have h3 : ConeSlopeUpper w a σ * ‖Z - a‖ ≤ Λ * ‖Z - a‖ :=
      mul_le_mul_of_nonneg_right hupb hZn
    have h4 : ConeSlopeLower w a σ * ‖Z - a‖ ≤ Λ * ‖Z - a‖ :=
      mul_le_mul_of_nonneg_right hlob hZn
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- Step 2: subdivision of the segment from `a` to `b`.
  intro a ha b hb
  set d : ℝ := ‖a - b‖ with hddef
  have hd0 : 0 ≤ d := norm_nonneg _
  set N : ℕ := ⌈d / σ⌉₊ + 1 with hNdef
  have hNpos : 0 < (N : ℝ) := by
    have hN1 : 1 ≤ N := by simp only [hNdef]; omega
    exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hdN : d / (N : ℝ) ≤ σ := by
    have hce : d / σ ≤ (N : ℝ) := by
      have h1 := Nat.le_ceil (d / σ)
      have h2 : (⌈d / σ⌉₊ : ℝ) ≤ (N : ℝ) := by
        simp only [hNdef]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hσ] at hce
    rw [div_le_iff₀ hNpos]
    linarith
  set p : ℕ → E := fun k => a + ((k : ℝ) / (N : ℝ)) • (b - a) with hpdef
  have hp0 : p 0 = a := by simp [hpdef]
  have hpN : p N = b := by
    simp only [hpdef]
    rw [div_self hNne, one_smul]
    abel
  have hpmem : ∀ k : ℕ, k ≤ N → p k ∈ closedBall z₀ ρ := by
    intro k hk
    have ht0 : (0 : ℝ) ≤ (k : ℝ) / (N : ℝ) := by positivity
    have ht1 : (k : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]; exact_mod_cast hk
    have hcv := (convex_closedBall z₀ ρ) ha hb
      (by linarith : (0 : ℝ) ≤ 1 - (k : ℝ) / (N : ℝ)) ht0 (by ring)
    have he : (1 - (k : ℝ) / (N : ℝ)) • a + ((k : ℝ) / (N : ℝ)) • b
        = a + ((k : ℝ) / (N : ℝ)) • (b - a) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [he] at hcv
    simpa only [hpdef] using hcv
  have hpstep : ∀ k : ℕ, ‖p (k + 1) - p k‖ = d / (N : ℝ) := by
    intro k
    have he : p (k + 1) - p k = ((1 : ℝ) / (N : ℝ)) • (b - a) := by
      simp only [hpdef]
      push_cast
      match_scalars <;> ring
    rw [he, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)),
      ← norm_neg (b - a), neg_sub, ← hddef]
    ring
  -- the chain estimate along the subdivision points
  have key : ∀ k : ℕ, k ≤ N → |w (p k) - w a| ≤ (k : ℝ) * (Λ * (d / (N : ℝ))) := by
    intro k
    induction k with
    | zero => intro _; simp [hp0]
    | succ n ih =>
      intro hn
      have hnN : n ≤ N := Nat.le_of_succ_le hn
      have h1 := ih hnN
      have h2 : |w (p (n + 1)) - w (p n)| ≤ Λ * (d / (N : ℝ)) := by
        have hmem : p (n + 1) ∈ closedBall (p n) σ := by
          rw [mem_closedBall, dist_eq_norm, hpstep n]
          exact hdN
        have hn2 := near (p n) (hpmem n hnN) (p (n + 1)) hmem
        rwa [hpstep n] at hn2
      have h3 : |w (p (n + 1)) - w a| ≤ |w (p (n + 1)) - w (p n)| + |w (p n) - w a| :=
        abs_sub_le _ _ _
      push_cast
      linarith
  have hfin := key N le_rfl
  rw [hpN] at hfin
  have hNd : (N : ℝ) * (Λ * (d / (N : ℝ))) = Λ * d := by field_simp
  rw [hNd] at hfin
  rw [abs_sub_comm]
  exact hfin
