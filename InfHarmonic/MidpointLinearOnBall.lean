module

public import InfHarmonic.Preamble
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section
open Metric Set

/-- Step 9 of the family-flatness argument: a function on a closed ball of a
finite-dimensional inner-product space that vanishes at the centre, is continuous
there, and satisfies the EXACT midpoint identity is the restriction of a linear
functional, hence of an inner product with a fixed vector.  The identities on a
ball support subdivision only, never doubling, so the usual Cauchy-equation
argument is run by halving: the extension `A ↦ 2^n W(2^{-n} A)` is additive and
continuous on the whole space, and an additive continuous map between real normed
spaces is automatically `ℝ`-linear. -/
theorem MidpointLinearOnBall {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (W : H → ℝ) (R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn W (closedBall (0 : H) R)) (h0 : W 0 = 0)
    (hmid : ∀ A ∈ closedBall (0 : H) R, ∀ B ∈ closedBall (0 : H) R,
      W A + W B = 2 * W ((2 : ℝ)⁻¹ • (A + B))) :
    ∃ P : H, ∀ A ∈ closedBall (0 : H) R, W A = (inner ℝ P A : ℝ) := by
  classical
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = R / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hcR : c ≤ R := by rw [hcdef]; linarith
  have hmem : ∀ A : H, ‖A‖ ≤ R → A ∈ closedBall (0 : H) R := by
    intro A h; rw [mem_closedBall, dist_zero_right]; exact h
  have h0mem : (0 : H) ∈ closedBall (0 : H) R := hmem 0 (by simp [hR.le])
  -- halving
  have hhalf : ∀ A : H, ‖A‖ ≤ R → W A = 2 * W ((2 : ℝ)⁻¹ • A) := by
    intro A hA
    have h := hmid A (hmem A hA) 0 h0mem
    rw [h0, add_zero, add_zero] at h
    linarith [h]
  -- additivity on the half-ball
  have hadd : ∀ A B : H, ‖A‖ ≤ c → ‖B‖ ≤ c → W (A + B) = W A + W B := by
    intro A B hA hB
    have hAB : ‖A + B‖ ≤ R := by
      have := norm_add_le A B
      rw [hcdef] at hA hB
      linarith
    have h := hmid A (hmem A (le_trans hA hcR)) B (hmem B (le_trans hB hcR))
    have h2 := hhalf (A + B) hAB
    linarith [h, h2]
  -- powers of two
  have hpow : ∀ (n : ℕ) (A : H), ‖A‖ ≤ R →
      W (((2 : ℝ) ^ n)⁻¹ • A) = ((2 : ℝ) ^ n)⁻¹ * W A := by
    intro n
    induction n with
    | zero => intro A _; simp
    | succ k ih =>
      intro A hA
      have hstep : (((2 : ℝ) ^ (k + 1))⁻¹ • A) = ((2 : ℝ) ^ k)⁻¹ • ((2 : ℝ)⁻¹ • A) := by
        rw [smul_smul]
        congr 1
        rw [pow_succ]
        field_simp
      have hhalfA : ‖(2 : ℝ)⁻¹ • A‖ ≤ R := by
        rw [norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
        have := norm_nonneg A
        linarith
      rw [hstep, ih _ hhalfA, hhalf A hA]
      rw [pow_succ]
      field_simp
  -- ===== admissible exponents =====
  have hadm2 : ∀ (t : ℝ), 0 < t → ∀ A : H, ‖A‖ ≤ (2 : ℝ) ^ (⌈‖A‖ / t⌉₊) * t := by
    intro t ht A
    have h1 : ‖A‖ / t ≤ ((⌈‖A‖ / t⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ ht] at h1
    have h2 : ((⌈‖A‖ / t⌉₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (⌈‖A‖ / t⌉₊) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := ⌈‖A‖ / t⌉₊)).le
    have h3 := mul_le_mul_of_nonneg_right h2 ht.le
    linarith only [h1, h3]
  have hmono2 : ∀ (t : ℝ), 0 ≤ t → ∀ (n m : ℕ), n ≤ m → ∀ A : H,
      ‖A‖ ≤ (2 : ℝ) ^ n * t → ‖A‖ ≤ (2 : ℝ) ^ m * t := by
    intro t ht n m hnm A hA
    have h : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hnm
    have := mul_le_mul_of_nonneg_right h ht
    linarith only [hA, this]
  -- the rescaled point lands in the small ball
  have hshrink : ∀ (n : ℕ) (t : ℝ) (A : H), 0 < t → ‖A‖ ≤ (2 : ℝ) ^ n * t →
      ‖((2 : ℝ) ^ n)⁻¹ • A‖ ≤ t := by
    intro n t A ht hA
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith only [hA]
  -- ===== independence of the exponent =====
  have key : ∀ (n k : ℕ) (A : H), ‖A‖ ≤ (2 : ℝ) ^ n * c →
      ((2 : ℝ) ^ (n + k)) * W (((2 : ℝ) ^ (n + k))⁻¹ • A)
        = ((2 : ℝ) ^ n) * W (((2 : ℝ) ^ n)⁻¹ • A) := by
    intro n k A hA
    have hA' : ‖((2 : ℝ) ^ n)⁻¹ • A‖ ≤ R :=
      le_trans (hshrink n c A hc0 hA) hcR
    have hsplit : ((2 : ℝ) ^ (n + k))⁻¹ • A
        = ((2 : ℝ) ^ k)⁻¹ • (((2 : ℝ) ^ n)⁻¹ • A) := by
      rw [smul_smul, pow_add]
      congr 1
      field_simp
    rw [hsplit, hpow k _ hA', pow_add]
    field_simp
  have hwd : ∀ (n m : ℕ) (A : H), ‖A‖ ≤ (2 : ℝ) ^ n * c → ‖A‖ ≤ (2 : ℝ) ^ m * c →
      ((2 : ℝ) ^ n) * W (((2 : ℝ) ^ n)⁻¹ • A)
        = ((2 : ℝ) ^ m) * W (((2 : ℝ) ^ m)⁻¹ • A) := by
    intro n m A hn hm
    rcases le_total n m with h | h
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      rw [hk]; exact (key n k A hn).symm
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      rw [hk]; exact key m k A hm
  -- ===== the homogeneous extension =====
  obtain ⟨Lf, hLfdef⟩ : ∃ Lf : H → ℝ,
      Lf = fun A => ((2 : ℝ) ^ (⌈‖A‖ / c⌉₊)) * W (((2 : ℝ) ^ (⌈‖A‖ / c⌉₊))⁻¹ • A) :=
    ⟨_, rfl⟩
  have hLfval : ∀ (n : ℕ) (A : H), ‖A‖ ≤ (2 : ℝ) ^ n * c →
      Lf A = ((2 : ℝ) ^ n) * W (((2 : ℝ) ^ n)⁻¹ • A) := by
    intro n A hA
    rw [hLfdef]
    exact hwd _ n A (hadm2 c hc0 A) hA
  have hLfW : ∀ A : H, ‖A‖ ≤ c → Lf A = W A := by
    intro A hA
    have h := hLfval 0 A (by simpa using hA)
    simpa using h
  -- ===== additivity of the extension =====
  have hhalfc : (0:ℝ) < c / 2 := by linarith
  have hLfadd : ∀ A B : H, Lf (A + B) = Lf A + Lf B := by
    intro A B
    obtain ⟨n, hnA, hnB⟩ : ∃ n : ℕ,
        ‖A‖ ≤ (2 : ℝ) ^ n * (c / 2) ∧ ‖B‖ ≤ (2 : ℝ) ^ n * (c / 2) := by
      refine ⟨max ⌈‖A‖ / (c / 2)⌉₊ ⌈‖B‖ / (c / 2)⌉₊, ?_, ?_⟩
      · exact hmono2 (c / 2) hhalfc.le _ _ (le_max_left _ _) A (hadm2 (c / 2) hhalfc A)
      · exact hmono2 (c / 2) hhalfc.le _ _ (le_max_right _ _) B (hadm2 (c / 2) hhalfc B)
    have h2n : (0:ℝ) < (2 : ℝ) ^ n := by positivity
    have hAc : ‖A‖ ≤ (2 : ℝ) ^ n * c := by nlinarith only [hnA, h2n, hc0]
    have hBc : ‖B‖ ≤ (2 : ℝ) ^ n * c := by nlinarith only [hnB, h2n, hc0]
    have hABn : ‖A + B‖ ≤ (2 : ℝ) ^ n * c := by
      have h := norm_add_le A B
      nlinarith only [h, hnA, hnB]
    have hAs : ‖((2 : ℝ) ^ n)⁻¹ • A‖ ≤ c / 2 := hshrink n (c / 2) A hhalfc hnA
    have hBs : ‖((2 : ℝ) ^ n)⁻¹ • B‖ ≤ c / 2 := hshrink n (c / 2) B hhalfc hnB
    have hsum : ((2 : ℝ) ^ n)⁻¹ • (A + B)
        = ((2 : ℝ) ^ n)⁻¹ • A + ((2 : ℝ) ^ n)⁻¹ • B := smul_add _ _ _
    rw [hLfval n (A + B) hABn, hLfval n A hAc, hLfval n B hBc, hsum,
      hadd _ _ (by linarith only [hAs, hc0]) (by linarith only [hBs, hc0])]
    ring
  have hLf0 : Lf 0 = 0 := by
    rw [hLfW 0 (by simpa using hc0.le)]; exact h0
  -- ===== continuity of the extension =====
  have hLfcont : Continuous Lf := by
    rw [continuous_iff_continuousAt]
    intro A
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖A‖ < (2 : ℝ) ^ n * c := by
      refine ⟨⌈‖A‖ / c⌉₊ + 1, ?_⟩
      have h1 := hadm2 c hc0 A
      have h2 : (2 : ℝ) ^ (⌈‖A‖ / c⌉₊) * c < (2 : ℝ) ^ (⌈‖A‖ / c⌉₊ + 1) * c := by
        have hp : (0:ℝ) < (2 : ℝ) ^ (⌈‖A‖ / c⌉₊) := by positivity
        rw [pow_succ]
        nlinarith only [hp, hc0]
      linarith only [h1, h2]
    obtain ⟨S, hSdef⟩ : ∃ S : Set H, S = {x : H | ‖x‖ < (2 : ℝ) ^ n * c} := ⟨_, rfl⟩
    have hopen : IsOpen S := by
      rw [hSdef]; exact isOpen_lt continuous_norm continuous_const
    have hSnhds : S ∈ nhds A := by
      refine hopen.mem_nhds ?_
      rw [hSdef]; exact hn
    have hcont2 : ContinuousOn (fun x : H => ((2 : ℝ) ^ n) * W (((2 : ℝ) ^ n)⁻¹ • x)) S := by
      refine continuousOn_const.mul ?_
      refine hcont.comp (by fun_prop) ?_
      intro x hx
      rw [hSdef] at hx
      refine hmem _ (le_trans (hshrink n c x hc0 (le_of_lt hx)) hcR)
    have heqon : Set.EqOn Lf (fun x : H => ((2 : ℝ) ^ n) * W (((2 : ℝ) ^ n)⁻¹ • x)) S := by
      intro x hx
      rw [hSdef] at hx
      exact hLfval n x (le_of_lt hx)
    exact (hcont2.congr heqon).continuousAt hSnhds
  -- ===== Riesz representation =====
  obtain ⟨Lhom, hLhom⟩ : ∃ Lhom : H →+ ℝ, ∀ A, Lhom A = Lf A :=
    ⟨{ toFun := Lf, map_zero' := hLf0, map_add' := hLfadd }, fun _ => rfl⟩
  have hLhomcont : Continuous Lhom := by
    have he : (Lhom : H → ℝ) = Lf := funext hLhom
    rw [he]; exact hLfcont
  obtain ⟨Lclm, hLclm⟩ : ∃ Lclm : H →L[ℝ] ℝ, ∀ A, Lclm A = Lf A :=
    ⟨Lhom.toRealLinearMap hLhomcont, by
      intro A
      rw [AddMonoidHom.coe_toRealLinearMap]
      exact hLhom A⟩
  refine ⟨(InnerProductSpace.toDual ℝ H).symm Lclm, ?_⟩
  intro A hA
  rw [mem_closedBall, dist_zero_right] at hA
  have hhalfA : ‖(2 : ℝ)⁻¹ • A‖ ≤ c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹), hcdef]
    linarith only [hA]
  have hrep : ∀ x : H, (inner ℝ ((InnerProductSpace.toDual ℝ H).symm Lclm) x : ℝ) = Lf x := by
    intro x
    rw [InnerProductSpace.toDual_symm_apply]
    exact hLclm x
  have h1 : W ((2 : ℝ)⁻¹ • A) = Lf ((2 : ℝ)⁻¹ • A) := (hLfW _ hhalfA).symm
  have h2 : Lf ((2 : ℝ)⁻¹ • A) = (2 : ℝ)⁻¹ * Lf A := by
    have := hLclm ((2 : ℝ)⁻¹ • A)
    have h3 := Lclm.map_smul ((2:ℝ)⁻¹) A
    rw [hLclm ((2 : ℝ)⁻¹ • A)] at h3
    rw [hLclm A] at h3
    simpa using h3
  rw [hhalf A hA, h1, h2, hrep A]
  ring
