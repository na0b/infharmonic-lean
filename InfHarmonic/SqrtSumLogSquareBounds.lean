import InfHarmonic.Preamble

/-- Two elementary real-analytic bounds used by the logarithmic grid sums of
Section 6.2. First, a telescoping comparison bounds the harmonic-type sum of
inverse square roots over the arithmetic grid `a, 2a, ..., M a` by
`2 * sqrt (a * M) / a`. Second, on `(0, 8]` the square of the logarithm is
dominated by `16 / sqrt s` plus the constant `(log 8) ^ 2`: for `s <= 1` the
inequality `-log u <= 1 / u` applied to `u = s ^ (1/4)` gives
`(log s) ^ 2 <= 16 / sqrt s`, and for `1 < s <= 8` monotonicity of the
logarithm gives `(log s) ^ 2 <= (log 8) ^ 2`. -/
theorem SqrtSumLogSquareBounds :
    (∀ a : ℝ, 0 < a → ∀ Mn : ℕ,
        ∑ m ∈ Finset.range Mn, 1 / Real.sqrt (a * ((m : ℝ) + 1))
          ≤ 2 * Real.sqrt (a * (Mn : ℝ)) / a)
      ∧ (∀ s : ℝ, 0 < s → s ≤ 8 →
        |Real.log s| ^ 2 ≤ 16 / Real.sqrt s + Real.log 8 ^ 2) := by
  constructor
  · intro a ha Mn
    have hterm : ∀ m : ℕ, 1 / Real.sqrt (a * ((m : ℝ) + 1))
        ≤ 2 * (Real.sqrt (a * ((m : ℝ) + 1)) - Real.sqrt (a * (m : ℝ))) / a := by
      intro m
      have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h1 : (0:ℝ) < a * ((m : ℝ) + 1) := by positivity
      have h2 : (0:ℝ) ≤ a * (m : ℝ) := by positivity
      have hs1 : 0 < Real.sqrt (a * ((m : ℝ) + 1)) := Real.sqrt_pos.mpr h1
      have hs2 : (0:ℝ) ≤ Real.sqrt (a * (m : ℝ)) := Real.sqrt_nonneg _
      have hq1 : Real.sqrt (a * ((m : ℝ) + 1)) * Real.sqrt (a * ((m : ℝ) + 1))
          = a * ((m : ℝ) + 1) := Real.mul_self_sqrt h1.le
      have hq2 : Real.sqrt (a * (m : ℝ)) * Real.sqrt (a * (m : ℝ)) = a * (m : ℝ) :=
        Real.mul_self_sqrt h2
      have hle : Real.sqrt (a * (m : ℝ)) ≤ Real.sqrt (a * ((m : ℝ) + 1)) :=
        Real.sqrt_le_sqrt (by nlinarith only [ha])
      rw [div_le_div_iff₀ hs1 ha]
      nlinarith only [hq1, hq2, hle, hs1, hs2, ha,
        sq_nonneg (Real.sqrt (a * ((m : ℝ) + 1)) - Real.sqrt (a * (m : ℝ)))]
    have hsumeq : ∑ m ∈ Finset.range Mn,
        2 * (Real.sqrt (a * ((m : ℝ) + 1)) - Real.sqrt (a * (m : ℝ))) / a
        = 2 * Real.sqrt (a * (Mn : ℝ)) / a := by
      have he : ∀ m ∈ Finset.range Mn,
          2 * (Real.sqrt (a * ((m : ℝ) + 1)) - Real.sqrt (a * (m : ℝ))) / a
          = (2 / a) * ((fun k : ℕ => Real.sqrt (a * (k : ℝ))) (m + 1)
              - (fun k : ℕ => Real.sqrt (a * (k : ℝ))) m) := by
        intro m _
        simp only
        push_cast
        ring
      rw [Finset.sum_congr rfl he, ← Finset.mul_sum,
        Finset.sum_range_sub (fun k : ℕ => Real.sqrt (a * (k : ℝ)))]
      simp only [Nat.cast_zero, mul_zero, Real.sqrt_zero, sub_zero]
      ring
    calc ∑ m ∈ Finset.range Mn, 1 / Real.sqrt (a * ((m : ℝ) + 1))
        ≤ ∑ m ∈ Finset.range Mn,
            2 * (Real.sqrt (a * ((m : ℝ) + 1)) - Real.sqrt (a * (m : ℝ))) / a :=
          Finset.sum_le_sum (fun m _ => hterm m)
      _ = 2 * Real.sqrt (a * (Mn : ℝ)) / a := hsumeq
  · intro s hs0 hs8
    have hl8 : (0:ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    rcases le_or_gt s 1 with hc | hc
    · have hu0 : 0 < Real.sqrt (Real.sqrt s) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hs0)
      have hu2 : Real.sqrt (Real.sqrt s) ^ 2 = Real.sqrt s :=
        Real.sq_sqrt (Real.sqrt_nonneg s)
      have hlogu : Real.log (Real.sqrt (Real.sqrt s)) = Real.log s / 4 := by
        rw [Real.log_sqrt (Real.sqrt_nonneg s), Real.log_sqrt hs0.le]
        ring
      have hinv : -Real.log (Real.sqrt (Real.sqrt s)) ≤ 1 / Real.sqrt (Real.sqrt s) := by
        have h1 := Real.log_le_sub_one_of_pos
          (show (0:ℝ) < (Real.sqrt (Real.sqrt s))⁻¹ by positivity)
        rw [Real.log_inv, inv_eq_one_div] at h1
        linarith only [h1]
      have hlogs : -Real.log s ≤ 4 / Real.sqrt (Real.sqrt s) := by
        rw [hlogu] at hinv
        have hconv : 4 / Real.sqrt (Real.sqrt s) = 4 * (1 / Real.sqrt (Real.sqrt s)) := by
          ring
        rw [hconv]
        linarith only [hinv]
      have hlognp : Real.log s ≤ 0 := Real.log_nonpos hs0.le hc
      have habs : |Real.log s| = -Real.log s := abs_of_nonpos hlognp
      have hsq : (0:ℝ) ≤ 16 / Real.sqrt s := by positivity
      have hkey : (-Real.log s) ^ 2 ≤ 16 / Real.sqrt s := by
        have h2 : (0:ℝ) ≤ -Real.log s := by linarith only [hlognp]
        have h3 := mul_self_le_mul_self h2 hlogs
        have h4 : (4 / Real.sqrt (Real.sqrt s)) * (4 / Real.sqrt (Real.sqrt s))
            = 16 / Real.sqrt s := by
          rw [div_mul_div_comm, ← hu2]
          norm_num
        rw [h4] at h3
        nlinarith only [h3]
      rw [habs]
      have h5 : (0:ℝ) ≤ Real.log 8 ^ 2 := sq_nonneg _
      linarith only [hkey, h5]
    · have hlogs : Real.log s ≤ Real.log 8 := Real.log_le_log hs0 hs8
      have h0 : (0:ℝ) ≤ Real.log s := Real.log_nonneg (le_of_lt hc)
      have habs : |Real.log s| = Real.log s := abs_of_nonneg h0
      rw [habs]
      have h3 := mul_self_le_mul_self h0 hlogs
      have h4 : (0:ℝ) ≤ 16 / Real.sqrt s := by positivity
      nlinarith only [h3, h4]
