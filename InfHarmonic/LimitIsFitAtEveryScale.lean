import InfHarmonic.IsFit
import InfHarmonic.IsFitClass
import InfHarmonic.AnisotropicBoxOffsets
set_option maxHeartbeats 400000
open Metric Set Filter Topology WithLp

/-- Step 11 of Proposition 3.6: the limit function is a fit of class `256` at
every centre and every scale.  Given the Step 7 uniform bound on each box ---
the normalized coefficients of the family are bounded by `Cthree K S` and the
sheared increments of `v i` deviate from the affine model by at most `64 S` ---
a Bolzano-Weierstrass extraction along a further subsequence of `psi` produces
a limiting pair `(p, a)`, and the bound passes to `vlim` on the compact sheared
box because `lam i` tends to `0` and `v (psi j)` tends to `vlim` uniformly
there. -/
theorem LimitIsFitAtEveryScale (d : ℕ) (lam : ℕ → ℝ)
    (v : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (Box : ℝ → Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))) (Cthree : ℝ → ℝ → ℝ) (ifive : ℝ → ℝ → ℕ)
    (psi : ℕ → ℕ) (vlim : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (hlam0 : ∀ i, 0 < lam i) (hlamlim : Tendsto lam atTop (𝓝 0))
    (hBoxdef : Box = fun K => {w | ‖(ofLp w).1‖ ≤ K ∧ |(ofLp w).2| ≤ K})
    (hCthree0 : ∀ K S : ℝ, 0 ≤ Cthree K S)
    (hpsimono : StrictMono psi)
    (hvconv : ∀ K : Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), IsCompact K →
      TendstoUniformlyOn (fun j => v (psi j)) vlim atTop K)
    (hfit :
      (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ ifive K S, ∀ w ∈ Box K,
        ∃ (p' : EuclideanSpace ℝ (Fin d)) (q' : ℝ),
          ‖p'‖ + |q'| ≤ Cthree K S ∧ 1 / 2 ≤ 1 + lam i * q' ∧
          ∀ (h : EuclideanSpace ℝ (Fin d)) (l : ℝ), |l| ≤ S / 2 →
            ‖h - (l / (1 + lam i * q')) • p'‖ ≤ S →
            |v i (w + toLp 2 (h, l)) - v i w - (inner ℝ p' h : ℝ) - q' * l|
              ≤ 64 * S)) :
    ∀ (zhat : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (R' : ℝ), 0 < R' →
      ∃ (p : EuclideanSpace ℝ (Fin d)) (a : ℝ), IsFit 256 vlim zhat R' p a := by
    intro zhat R' hR'
    -- the box comes from the CENTRE; the increments are unconstrained by it
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max 1 (max ‖(ofLp zhat).1‖ |(ofLp zhat).2|) := ⟨_, rfl⟩
    have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; exact le_max_left _ _
    have hzB : zhat ∈ Box K := by
      rw [hBoxdef, hKdef]
      exact ⟨le_trans (le_max_left _ _) (le_max_right _ _),
        le_trans (le_max_right _ _) (le_max_right _ _)⟩
    -- eq:nl-fit at `S = 4R'`: the coefficient of `S` is `2Λ = 64`, so `64 S = 256 R'`
    obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 4 * R' := ⟨_, rfl⟩
    have hS0 : (0 : ℝ) < S := by rw [hSdef]; linarith only [hR']
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Cthree K S := ⟨_, rfl⟩
    have hC0 : (0 : ℝ) ≤ C := by rw [hCdef]; exact hCthree0 K S
    obtain ⟨j0, hj0def⟩ : ∃ j0 : ℕ, j0 = ifive K S := ⟨_, rfl⟩
    -- the coefficient sequence along `psi`, shifted past the Step-8 threshold
    have hcoef : ∀ n : ℕ, ∃ (ppn : EuclideanSpace ℝ (Fin d)) (qnn : ℝ),
        ‖ppn‖ + |qnn| ≤ C ∧ 1 / 2 ≤ 1 + lam (psi (j0 + n)) * qnn ∧
        ∀ (h : EuclideanSpace ℝ (Fin d)) (l : ℝ), |l| ≤ S / 2 →
          ‖h - (l / (1 + lam (psi (j0 + n)) * qnn)) • ppn‖ ≤ S →
          |v (psi (j0 + n)) (zhat + toLp 2 (h, l)) - v (psi (j0 + n)) zhat
            - (inner ℝ ppn h : ℝ) - qnn * l| ≤ 64 * S := by
      intro n
      have hidx : ifive K S ≤ psi (j0 + n) := by
        rw [← hj0def]
        exact le_trans (Nat.le_add_right j0 n) (hpsimono.le_apply (x := j0 + n))
      obtain ⟨ppn, qnn, hb, hA, hinc⟩ := hfit K hK1 S hS0 (psi (j0 + n)) hidx zhat hzB
      exact ⟨ppn, qnn, by rw [hCdef]; exact hb, hA, hinc⟩
    choose pp qn hppb hppA hppinc using hcoef
    -- A FURTHER SUBSEQUENCE: the coefficients are bounded, so they converge along one
    have hPmem : ∀ n : ℕ, (toLp 2 (pp n, qn n) : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
        ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) C := by
      intro n
      rw [mem_closedBall, dist_zero_right]
      have hsq := WithLp.prod_norm_sq_eq_of_L2
        (toLp 2 (pp n, qn n) : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
      have he1 : ‖(toLp 2 (pp n, qn n)
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).fst‖ = ‖pp n‖ := rfl
      have he2 : ‖(toLp 2 (pp n, qn n)
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).snd‖ = |qn n| := rfl
      rw [he1, he2] at hsq
      have hub : ‖(toLp 2 (pp n, qn n) : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ ^ 2
          ≤ C ^ 2 := by
        nlinarith only [hsq, hppb n, norm_nonneg (pp n), abs_nonneg (qn n)]
      exact le_of_pow_le_pow_left₀ (by norm_num) hC0 hub
    obtain ⟨Pinf, -, φ, hφmono, hφconv⟩ :=
      (isCompact_closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) C).tendsto_subseq
        hPmem
    obtain ⟨p, hpdef⟩ : ∃ p : EuclideanSpace ℝ (Fin d), p = (ofLp Pinf).1 := ⟨_, rfl⟩
    obtain ⟨qlim, hqdef⟩ : ∃ qlim : ℝ, qlim = (ofLp Pinf).2 := ⟨_, rfl⟩
    have hc1 : Continuous
        (fun y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => (ofLp y).1) := by fun_prop
    have hc2 : Continuous
        (fun y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => (ofLp y).2) := by fun_prop
    have hppconv : Tendsto (fun n => pp (φ n)) atTop (𝓝 p) := by
      rw [hpdef]; exact (hc1.tendsto Pinf).comp hφconv
    have hqnconv : Tendsto (fun n => qn (φ n)) atTop (𝓝 qlim) := by
      rw [hqdef]; exact (hc2.tendsto Pinf).comp hφconv
    -- THE SHEARS CONVERGE TO `p`, which is what makes the domain inclusion uniform
    obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hppconv 1 (by norm_num)
    have hlamidx : Tendsto (fun n : ℕ => lam (psi (j0 + φ n))) atTop (𝓝 0) := by
      refine hlamlim.comp (tendsto_atTop_mono (fun n => ?_) tendsto_id)
      exact le_trans (le_trans (hφmono.le_apply (x := n)) (Nat.le_add_left (φ n) j0))
        (hpsimono.le_apply (x := j0 + φ n))
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
      (hlamidx.eventually_lt_const
        (show (0 : ℝ) < 1 / (2 * (C ^ 2 + 1)) by positivity))
    obtain ⟨N3, hN3def⟩ : ∃ N3 : ℕ, N3 = max N1 N2 := ⟨_, rfl⟩
    have hshear : ∀ n ≥ N3,
        ‖p - (1 + lam (psi (j0 + φ n)) * qn (φ n))⁻¹ • pp (φ n)‖ ≤ 2 := by
      intro n hn
      have hn1 : N1 ≤ n := le_trans (by rw [hN3def]; exact le_max_left _ _) hn
      have hn2 : N2 ≤ n := le_trans (by rw [hN3def]; exact le_max_right _ _) hn
      obtain ⟨An, hAndef⟩ : ∃ An : ℝ, An = 1 + lam (psi (j0 + φ n)) * qn (φ n) := ⟨_, rfl⟩
      rw [← hAndef]
      have hA2 : (1 : ℝ) / 2 ≤ An := by rw [hAndef]; exact hppA (φ n)
      have hA0 : (0 : ℝ) < An := by linarith only [hA2]
      have hppC : ‖pp (φ n)‖ ≤ C := by
        linarith only [hppb (φ n), abs_nonneg (qn (φ n))]
      have hqnC : |qn (φ n)| ≤ C := by
        linarith only [hppb (φ n), norm_nonneg (pp (φ n))]
      -- first leg: the coefficients themselves
      have hleg1 : ‖p - pp (φ n)‖ ≤ 1 := by
        have h := hN1 n hn1
        rw [dist_eq_norm] at h
        rw [show ‖p - pp (φ n)‖ = ‖pp (φ n) - p‖ from (norm_sub_rev _ _).symm]
        exact le_of_lt h
      -- second leg: the shear correction
      have hsplit : p - An⁻¹ • pp (φ n) = (p - pp (φ n)) + (1 - An⁻¹) • pp (φ n) := by
        rw [sub_smul, one_smul]; abel
      have htri : ‖p - An⁻¹ • pp (φ n)‖
          ≤ ‖p - pp (φ n)‖ + |1 - An⁻¹| * ‖pp (φ n)‖ := by
        rw [hsplit]
        have h := norm_add_le (p - pp (φ n)) ((1 - An⁻¹) • pp (φ n))
        rw [norm_smul, Real.norm_eq_abs] at h
        exact h
      have hinvb : |1 - An⁻¹| ≤ 2 * |An - 1| := by
        have h1 : 1 - An⁻¹ = (An - 1) / An := by field_simp
        rw [h1, abs_div, abs_of_pos hA0, div_le_iff₀ hA0]
        nlinarith only [hA2, abs_nonneg (An - 1)]
      have hAm1 : |An - 1| = lam (psi (j0 + φ n)) * |qn (φ n)| := by
        rw [hAndef, show (1 : ℝ) + lam (psi (j0 + φ n)) * qn (φ n) - 1
          = lam (psi (j0 + φ n)) * qn (φ n) from by ring, abs_mul,
          abs_of_pos (hlam0 (psi (j0 + φ n)))]
      have hlamn : lam (psi (j0 + φ n)) < 1 / (2 * (C ^ 2 + 1)) := hN2 n hn2
      have hlampos : (0 : ℝ) < lam (psi (j0 + φ n)) := hlam0 (psi (j0 + φ n))
      have hlamC : lam (psi (j0 + φ n)) * (2 * (C ^ 2 + 1)) < 1 := by
        rw [← lt_div_iff₀ (show (0 : ℝ) < 2 * (C ^ 2 + 1) by positivity)]
        exact hlamn
      have hleg2 : |1 - An⁻¹| * ‖pp (φ n)‖ ≤ 1 := by
        have h1 : |1 - An⁻¹| ≤ 2 * (lam (psi (j0 + φ n)) * C) := by
          rw [hAm1] at hinvb
          nlinarith only [hinvb, hqnC, hlampos]
        have h2 : |1 - An⁻¹| * ‖pp (φ n)‖
            ≤ (2 * (lam (psi (j0 + φ n)) * C)) * C :=
          mul_le_mul h1 hppC (norm_nonneg _)
            (by positivity)
        nlinarith only [h2, hlamC, hlampos, hC0]
      linarith only [htri, hleg1, hleg2]
    -- pointwise convergence of the shifted tail at any single point
    have hptwise : ∀ y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        Tendsto (fun n => v (psi (j0 + φ n)) y) atTop (𝓝 (vlim y)) := by
      intro y
      have h1 : TendstoUniformlyOn (fun j => v (psi j)) vlim atTop ({y} : Set _) :=
        hvconv _ isCompact_singleton
      refine (h1.tendsto_at (Set.mem_singleton y)).comp
        (tendsto_atTop_mono (fun n => ?_) tendsto_id)
      exact le_trans (hφmono.le_apply (x := n)) (Nat.le_add_left (φ n) j0)
    -- `a = q + ‖p‖²/2`, so that `a - ‖p‖²/2 = q`, matching the paper
    refine ⟨p, qlim + ‖p‖ ^ 2 / 2, ?_⟩
    intro h l hl hhp
    have hcoeffa : qlim + ‖p‖ ^ 2 / 2 - ‖p‖ ^ 2 / 2 = qlim := by ring
    rw [hcoeffa]
    -- the three convergences, and the limit of the whole quantity
    have hcC : Continuous (fun x : EuclideanSpace ℝ (Fin d) => (inner ℝ x h : ℝ)) := by
      fun_prop
    have hconvC : Tendsto (fun n => (inner ℝ (pp (φ n)) h : ℝ)) atTop
        (𝓝 (inner ℝ p h : ℝ)) := (hcC.tendsto p).comp hppconv
    have hQ : Tendsto (fun n => |v (psi (j0 + φ n)) (zhat + toLp 2 (h, l))
        - v (psi (j0 + φ n)) zhat - (inner ℝ (pp (φ n)) h : ℝ) - qn (φ n) * l|) atTop
        (𝓝 |vlim (zhat + toLp 2 (h, l)) - vlim zhat - (inner ℝ p h : ℝ) - qlim * l|) :=
      ((((hptwise (zhat + toLp 2 (h, l))).sub (hptwise zhat)).sub hconvC).sub
        (hqnconv.mul_const l)).abs
    refine le_of_tendsto hQ ?_
    filter_upwards [eventually_ge_atTop N3] with n hn
    -- the DOMAIN conditions, with the factor-2 margin on `|l|` and the shear margin
    have hdom1 : |l| ≤ S / 2 := by rw [hSdef]; linarith only [hl, hR']
    have hdom2 : ‖h - (l / (1 + lam (psi (j0 + φ n)) * qn (φ n))) • pp (φ n)‖ ≤ S := by
      obtain ⟨An, hAndef⟩ : ∃ An : ℝ, An = 1 + lam (psi (j0 + φ n)) * qn (φ n) := ⟨_, rfl⟩
      rw [← hAndef]
      have hA2 : (1 : ℝ) / 2 ≤ An := by rw [hAndef]; exact hppA (φ n)
      have hA0 : (0 : ℝ) < An := by linarith only [hA2]
      have hid : h - (l / An) • pp (φ n)
          = (h - l • p) + l • (p - An⁻¹ • pp (φ n)) := by
        rw [smul_sub, smul_smul, div_eq_mul_inv]
        abel
      have htri : ‖h - (l / An) • pp (φ n)‖
          ≤ ‖h - l • p‖ + |l| * ‖p - An⁻¹ • pp (φ n)‖ := by
        rw [hid]
        have hh := norm_add_le (h - l • p) (l • (p - An⁻¹ • pp (φ n)))
        rw [norm_smul, Real.norm_eq_abs] at hh
        exact hh
      have hsh : ‖p - An⁻¹ • pp (φ n)‖ ≤ 2 := by rw [hAndef]; exact hshear n hn
      have hlb : |l| * ‖p - An⁻¹ • pp (φ n)‖ ≤ R' * 2 := by
        refine mul_le_mul hl hsh (norm_nonneg _) (le_of_lt hR')
      rw [hSdef]
      linarith only [htri, hhp, hlb, hR']
    have hb := hppinc (φ n) h l hdom1 hdom2
    rw [hSdef] at hb
    linarith only [hb]
