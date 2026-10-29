module

public import InfHarmonic.CylinderComparisonSameCenter

@[expose] public section
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The doubling chain of (3.5): for a slope window `[c₁, C₁]` there is one constant `C`
such that, whenever fits of parameter `θ²` exist at every radius up to `R r` at a common
centre with slopes in that window, the fit at the outer radius `R r` and the fit at the
base radius `r` have comparable directions and norms, with the LOGARITHMIC factor
`1 + log R` coming from the number of doublings in the chain `r, 2r, …, 2^n r, R r`. -/
theorem CylinderFitDoublingChain (c₁ C₁ : ℝ) (hc : 0 < c₁) (hcC : c₁ ≤ C₁) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : E → ℝ) (zc : E) (rb th R : ℝ) (P : E),
        0 < rb → 0 < th → th < 1 → 2 ≤ R →
        c₁ ≤ ‖P‖ → ‖P‖ ≤ C₁ → IsCylinderFit u zc rb (th ^ 2) P →
        (∀ rho : ℝ, 0 < rho → rho ≤ R * rb →
          ∃ Q : E, IsCylinderFit u zc rho (th ^ 2) Q ∧ c₁ ≤ ‖Q‖ ∧ ‖Q‖ ≤ C₁) →
        ∃ PR : E, IsCylinderFit u zc (R * rb) (th ^ 2) PR ∧
          c₁ ≤ ‖PR‖ ∧ ‖PR‖ ≤ C₁ ∧
          ‖‖PR‖⁻¹ • PR - ‖P‖⁻¹ • P‖ ≤ C * (1 + Real.log R) * th ∧
          |‖PR‖ - ‖P‖| ≤ C * (1 + Real.log R) * th ^ 2 := by
  classical
  obtain ⟨Ca, hCa0, hcmp⟩ := CylinderComparisonSameCenter (E := E) c₁ C₁ hc hcC
  refine ⟨2 * Ca, by linarith only [hCa0], ?_⟩
  intro u zc rb th R P hrb hth0 hth1 hR2 hPl hPu hPfit hfits
  -- `n` is the least index with `R ≤ 2^(n+1)`, so `2^n < R ≤ 2^(n+1)`: the chain
  -- `rb, 2rb, …, 2^n rb, R rb` has `n+1` links, each of ratio in `[1,2]`
  obtain ⟨n, hnR, hnlow⟩ : ∃ n : ℕ, R ≤ (2 : ℝ) ^ (n + 1) ∧ (2 : ℝ) ^ n < R := by
    have hex : ∃ k : ℕ, R ≤ (2 : ℝ) ^ (k + 1) := by
      obtain ⟨k, hk⟩ := exists_nat_gt R
      refine ⟨k, ?_⟩
      have h1 : (k : ℝ) ≤ (2 : ℝ) ^ k := by
        have := Nat.lt_two_pow_self (n := k)
        have h2 : ((k : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast le_of_lt this
        rwa [Nat.cast_pow, Nat.cast_ofNat] at h2
      have h3 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
        apply pow_le_pow_right₀ (by norm_num) (by omega)
      linarith only [hk, h1, h3]
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; norm_num; linarith only [hR2]
    · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      have hnn : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rw [hnn] at hmin
      exact not_le.mp hmin
  -- the radii of the chain, as a total function
  obtain ⟨rho, hrhodef⟩ : ∃ rho : ℕ → ℝ,
      rho = fun k => if k ≤ n then (2 : ℝ) ^ k * rb else R * rb := ⟨_, rfl⟩
  have hpow0 : ∀ k : ℕ, (0 : ℝ) < (2 : ℝ) ^ k := fun k => by positivity
  have hrho0 : ∀ k, 0 < rho k := by
    intro k
    rw [hrhodef]
    by_cases hk : k ≤ n
    · simp only [if_pos hk]; exact mul_pos (hpow0 k) hrb
    · simp only [if_neg hk]; exact mul_pos (by linarith only [hR2]) hrb
  have hpowmono : ∀ k : ℕ, k ≤ n → (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n :=
    fun k hk => pow_le_pow_right₀ (by norm_num) hk
  have hrhoR : ∀ k, rho k ≤ R * rb := by
    intro k
    rw [hrhodef]
    by_cases hk : k ≤ n
    · simp only [if_pos hk]
      have h1 : (2 : ℝ) ^ k ≤ R := by linarith only [hpowmono k hk, hnlow]
      exact mul_le_mul_of_nonneg_right h1 (le_of_lt hrb)
    · simp only [if_neg hk]
      exact le_refl _
  have hrho00 : rho 0 = rb := by rw [hrhodef]; simp
  have hrhoLast : rho (n + 1) = R * rb := by rw [hrhodef]; simp
  have hstep : ∀ k : ℕ, k ≤ n → rho k ≤ rho (k + 1) ∧ rho (k + 1) ≤ 2 * rho k := by
    intro k hk
    rcases lt_or_eq_of_le hk with hlt | heq
    · have h1 : k + 1 ≤ n := by omega
      rw [hrhodef]
      simp only [if_pos hk, if_pos h1]
      have h2 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
      rw [h2]
      constructor
      · nlinarith only [hpow0 k, hrb]
      · nlinarith only [hpow0 k, hrb]
    · subst heq
      have h1 : ¬ (k + 1 ≤ k) := by omega
      rw [hrhodef]
      simp only [if_pos (le_refl k), if_neg h1]
      have h2 : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
      rw [h2] at hnR
      constructor
      · nlinarith only [hnlow, hrb]
      · nlinarith only [hnR, hrb]
  -- a fit at every radius of the chain, from the hypothesis
  have hfitex : ∀ k : ℕ, ∃ Q : E,
      IsCylinderFit u zc (rho k) (th ^ 2) Q ∧ c₁ ≤ ‖Q‖ ∧ ‖Q‖ ≤ C₁ :=
    fun k => hfits (rho k) (hrho0 k) (hrhoR k)
  choose Qc hQcfit hQc1 hQc2 using hfitex
  -- the chain itself, anchored at `Q₀ = P` (legitimate because `ρ₀ = rb`)
  obtain ⟨Qf, hQfdef⟩ : ∃ Qf : ℕ → E, Qf = fun k => if k = 0 then P else Qc k := ⟨_, rfl⟩
  have hQf0 : Qf 0 = P := by rw [hQfdef]; simp
  have hQffit : ∀ k, IsCylinderFit u zc (rho k) (th ^ 2) (Qf k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      rw [hQf0, hrho00]
      exact hPfit
    · have hk : ¬ (k = 0) := by omega
      rw [hQfdef]
      simp only [if_neg hk]
      exact hQcfit k
  have hQfl : ∀ k, c₁ ≤ ‖Qf k‖ := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; rw [hQf0]; exact hPl
    · have hk : ¬ (k = 0) := by omega
      rw [hQfdef]; simp only [if_neg hk]; exact hQc1 k
  have hQfu : ∀ k, ‖Qf k‖ ≤ C₁ := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; rw [hQf0]; exact hPu
    · have hk : ¬ (k = 0) := by omega
      rw [hQfdef]; simp only [if_neg hk]; exact hQc2 k
  -- summing the `n+1` inequalities of the same-centre comparison along the chain
  have hCath : 0 ≤ Ca * th := mul_nonneg (le_of_lt hCa0) (le_of_lt hth0)
  have hCath2 : 0 ≤ Ca * th ^ 2 := by positivity
  have hind : ∀ k : ℕ, k ≤ n + 1 →
      ‖‖Qf k‖⁻¹ • Qf k - ‖P‖⁻¹ • P‖ ≤ (k : ℝ) * (Ca * th) ∧
      |‖Qf k‖ - ‖P‖| ≤ (k : ℝ) * (Ca * th ^ 2) := by
    intro k
    induction k with
    | zero =>
        intro _
        rw [hQf0]
        simp
    | succ k ih =>
        intro hk
        obtain ⟨g1, g2⟩ := ih (by omega)
        obtain ⟨hs1, hs2⟩ := hstep k (by omega)
        obtain ⟨c1, c2⟩ := hcmp u zc th (rho k) (rho (k + 1)) (Qf k) (Qf (k + 1))
          hth0 hth1 (hrho0 k) hs1 hs2 (hQfl k) (hQfu k) (hQfl (k + 1)) (hQfu (k + 1))
          (hQffit k) (hQffit (k + 1))
        have hsplit : ‖‖Qf k‖⁻¹ • Qf k - ‖Qf (k + 1)‖⁻¹ • Qf (k + 1)‖ ≤ Ca * th := by
          linarith only [c1, norm_nonneg (Qf k - Qf (k + 1))]
        refine ⟨?_, ?_⟩
        · have htri : ‖‖Qf (k + 1)‖⁻¹ • Qf (k + 1) - ‖P‖⁻¹ • P‖
              ≤ ‖‖Qf (k + 1)‖⁻¹ • Qf (k + 1) - ‖Qf k‖⁻¹ • Qf k‖
                + ‖‖Qf k‖⁻¹ • Qf k - ‖P‖⁻¹ • P‖ := by
            have hd := dist_triangle (‖Qf (k + 1)‖⁻¹ • Qf (k + 1)) (‖Qf k‖⁻¹ • Qf k)
              (‖P‖⁻¹ • P)
            rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hd
          have hrev : ‖‖Qf (k + 1)‖⁻¹ • Qf (k + 1) - ‖Qf k‖⁻¹ • Qf k‖
              = ‖‖Qf k‖⁻¹ • Qf k - ‖Qf (k + 1)‖⁻¹ • Qf (k + 1)‖ := norm_sub_rev _ _
          rw [hrev] at htri
          push_cast
          linarith only [htri, hsplit, g1]
        · have habs : |‖Qf (k + 1)‖ - ‖P‖|
              ≤ |‖Qf (k + 1)‖ - ‖Qf k‖| + |‖Qf k‖ - ‖P‖| :=
            abs_sub_le (‖Qf (k + 1)‖) (‖Qf k‖) (‖P‖)
          have hrev2 : |‖Qf (k + 1)‖ - ‖Qf k‖| = |‖Qf k‖ - ‖Qf (k + 1)‖| :=
            abs_sub_comm _ _
          rw [hrev2] at habs
          push_cast
          linarith only [habs, c2, g2]
  -- `n + 1 ≤ 2 (1 + log R)`: this is where the DOUBLING COUNT becomes `1 + log R`
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith only [hR2])
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have h1 : (1 : ℝ) / 2 < Real.exp (-(1 / 2)) := by
      have h := Real.add_one_lt_exp (x := -(1 / 2 : ℝ)) (by norm_num)
      linarith only [h]
    have h2 : Real.log (1 / 2 : ℝ) < Real.log (Real.exp (-(1 / 2))) :=
      Real.log_lt_log (by norm_num) h1
    rw [Real.log_exp] at h2
    have h3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [h3] at h2
    linarith only [h2]
  have hnlog : (n : ℝ) * Real.log 2 ≤ Real.log R := by
    have h := Real.log_le_log (hpow0 n) (le_of_lt hnlow)
    rwa [Real.log_pow] at h
  have hn2 : ((n : ℝ) + 1) ≤ 2 * (1 + Real.log R) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith only [hnlog, hlog2, hn0, hlogR]
  obtain ⟨g1, g2⟩ := hind (n + 1) le_rfl
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at g1 g2
  refine ⟨Qf (n + 1), ?_, hQfl (n + 1), hQfu (n + 1), ?_, ?_⟩
  · rw [← hrhoLast]; exact hQffit (n + 1)
  · calc ‖‖Qf (n + 1)‖⁻¹ • Qf (n + 1) - ‖P‖⁻¹ • P‖
        ≤ ((n : ℝ) + 1) * (Ca * th) := g1
      _ ≤ 2 * (1 + Real.log R) * (Ca * th) := mul_le_mul_of_nonneg_right hn2 hCath
      _ = 2 * Ca * (1 + Real.log R) * th := by ring
  · calc |‖Qf (n + 1)‖ - ‖P‖|
        ≤ ((n : ℝ) + 1) * (Ca * th ^ 2) := g2
      _ ≤ 2 * (1 + Real.log R) * (Ca * th ^ 2) := mul_le_mul_of_nonneg_right hn2 hCath2
      _ = 2 * Ca * (1 + Real.log R) * th ^ 2 := by ring
