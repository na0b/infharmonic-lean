module

public import InfHarmonic.FrameEnvelopeCovariance
public import InfHarmonic.ContactEnv
public import InfHarmonic.BaryEnv

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 6.5, second part: the barycentric gap and the contact-envelope gap are
covariant under the contact frame, both scaling by `r`. -/
theorem FrameGapCovariance (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hJ : HasJensenBound Set.univ v κ)
    (r : ℝ) (hr : 0 < r) (x₀ p₀ : F) (a₀ : ℝ)
    (hfit : IsFit C₀ v (toLp 2 (x₀, r)) r p₀ a₀) :
    (∀ (σ : ℝ) (ζ : WithLp 2 (F × ℝ)), 0 < σ →
      BaryEnv (fun ξ => FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
            (ξ - toLp 2 ((0 : F), (1 : ℝ)))) σ ζ
        - FrameChange v (toLp 2 (x₀, r)) r p₀ a₀ (ζ - toLp 2 ((0 : F), (1 : ℝ)))
      = (BaryEnv v (r * σ)
            (toLp 2 (x₀ + r • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • p₀), r * (ofLp ζ).2))
          - v (toLp 2 (x₀ + r • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • p₀), r * (ofLp ζ).2)))
        / r) ∧
    (∀ ζ : WithLp 2 (F × ℝ), 0 < (ofLp ζ).2 →
      ContactEnv (fun ξ => FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
            (ξ - toLp 2 ((0 : F), (1 : ℝ)))) κ ζ
        - FrameChange v (toLp 2 (x₀, r)) r p₀ a₀ (ζ - toLp 2 ((0 : F), (1 : ℝ)))
      = (ContactEnv v κ
            (toLp 2 (x₀ + r • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • p₀), r * (ofLp ζ).2))
          - v (toLp 2 (x₀ + r • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • p₀), r * (ofLp ζ).2)))
        / r) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  -- The gap identity is pure frame algebra plus the Jensen bound: the fit hypotheses
  -- `hC₀`, `hv`, `hfit` and the sign `hκ` are carried by the statement because the paper's
  -- lemma carries them, but the proof below does not use them.
  have _unused := And.intro hC₀ (And.intro hκ (And.intro hv hfit))
  -- Step 0: the contact frame written out at a space-time point.
  have hvbar : ∀ ξ : WithLp 2 (F × ℝ),
      FrameChange v (toLp 2 (x₀, r)) r p₀ a₀ (ξ - toLp 2 ((0 : F), (1 : ℝ)))
        = v (toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2)) / r
          - (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * ((ofLp ξ).2 - 1)
             + inner ℝ p₀ (ofLp ξ).1) := by
    intro ξ
    have e1 : (ξ - toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))
        = toLp 2 ((ofLp ξ).1, (ofLp ξ).2 - 1) := by
      have h : ((ofLp ξ).1 - 0, (ofLp ξ).2 - 1) = ((ofLp ξ).1, (ofLp ξ).2 - 1) := by simp
      exact h ▸ rfl
    have e2 : (toLp 2 (x₀, r)
          + toLp 2 (r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * ((ofLp ξ).2 - 1))
          : WithLp 2 (F × ℝ))
        = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2) := by
      have h : r + r * ((ofLp ξ).2 - 1) = r * (ofLp ξ).2 := by ring
      exact h ▸ rfl
    simp only [FrameChange, e1, WithLp.ofLp_toLp, e2]
    field_simp
    ring
  -- Step 1: an affine function averages to its value at the barycentre.
  have hmean : ∀ (c : ℝ) (n : ℕ) (θ : Fin n → ℝ) (y' : Fin n → F) (y : F),
      IsBaryConfig n θ y' y →
      (∑ i, θ i * (c + inner ℝ p₀ (y' i))) = c + inner ℝ p₀ y := by
    intro c n θ y' y hc
    obtain ⟨-, hsum, hbary⟩ := hc
    have h1 : (∑ i, θ i * (c + inner ℝ p₀ (y' i)))
        = (∑ i, θ i) * c + ∑ i, θ i * inner ℝ p₀ (y' i) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : (∑ i, θ i * inner ℝ p₀ (y' i)) = inner ℝ p₀ y := by
      rw [← hbary, inner_sum]
      exact Finset.sum_congr rfl fun i _ => (real_inner_smul_right p₀ (y' i) (θ i)).symm
    rw [h1, h2, hsum, one_mul]
  -- Step 2: the barycentric radius scales by `r`.
  have hrad : ∀ (s : ℝ) (n : ℕ) (θ : Fin n → ℝ) (y' : Fin n → F) (y : F),
      BaryRadius n θ (fun i => x₀ + r • (y' i + (s - 1) • p₀)) (x₀ + r • (y + (s - 1) • p₀))
        = r * BaryRadius n θ y' y := by
    intro s n θ y' y
    have hdiff : ∀ i, (x₀ + r • (y' i + (s - 1) • p₀)) - (x₀ + r • (y + (s - 1) • p₀))
        = r • (y' i - y) := by
      intro i; simp only [smul_add, smul_sub]; abel
    simp only [BaryRadius, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [show (∑ i, θ i * (r * ‖y' i - y‖) ^ 2) = r ^ 2 * ∑ i, θ i * ‖y' i - y‖ ^ 2 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  -- Step 3: configurations push forward along the frame map.
  have hcfwd : ∀ (s : ℝ) (n : ℕ) (θ : Fin n → ℝ) (y' : Fin n → F) (y : F),
      IsBaryConfig n θ y' y →
      IsBaryConfig n θ (fun i => x₀ + r • (y' i + (s - 1) • p₀))
        (x₀ + r • (y + (s - 1) • p₀)) := by
    intro s n θ y' y hc
    obtain ⟨hpos, hsum, hbary⟩ := hc
    refine ⟨hpos, hsum, ?_⟩
    have h1 : ∀ i, θ i • (x₀ + r • (y' i + (s - 1) • p₀))
        = θ i • x₀ + (θ i * r) • y' i + (θ i * (r * (s - 1))) • p₀ := by
      intro i; simp only [smul_add, smul_smul]; abel
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_smul, ← Finset.sum_smul, hsum, one_smul]
    have h2 : (∑ i, (θ i * r) • y' i) = r • y := by
      rw [← hbary, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; ring_nf
    have h3 : (∑ i, θ i * (r * (s - 1))) = r * (s - 1) := by
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [h2, h3, smul_add, smul_smul]
    abel
  -- Step 4: configurations pull back along the frame map; it is a bijection.
  have hcbwd : ∀ (s : ℝ) (y : F) (n : ℕ) (θ : Fin n → ℝ) (x' : Fin n → F),
      IsBaryConfig n θ x' (x₀ + r • (y + (s - 1) • p₀)) →
      IsBaryConfig n θ (fun i => r⁻¹ • (x' i - x₀) - (s - 1) • p₀) y ∧
      ∀ i, x₀ + r • ((r⁻¹ • (x' i - x₀) - (s - 1) • p₀) + (s - 1) • p₀) = x' i := by
    intro s y n θ x' hc
    obtain ⟨hpos, hsum, hbary⟩ := hc
    constructor
    · refine ⟨hpos, hsum, ?_⟩
      have h1 : ∀ i, θ i • (r⁻¹ • (x' i - x₀) - (s - 1) • p₀)
          = (θ i * r⁻¹) • x' i - (θ i * r⁻¹) • x₀ - (θ i * (s - 1)) • p₀ := by
        intro i; simp only [smul_sub, smul_smul]
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_smul, ← Finset.sum_smul]
      have h2 : (∑ i, (θ i * r⁻¹) • x' i) = r⁻¹ • (x₀ + r • (y + (s - 1) • p₀)) := by
        rw [← hbary, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; ring_nf
      have h3 : (∑ i, θ i * r⁻¹) = r⁻¹ := by rw [← Finset.sum_mul, hsum, one_mul]
      have h4 : (∑ i, θ i * (s - 1)) = s - 1 := by rw [← Finset.sum_mul, hsum, one_mul]
      rw [h2, h3, h4, smul_add, smul_smul, inv_mul_cancel₀ hr', one_smul]
      abel
    · intro i
      rw [sub_add_cancel, smul_smul, mul_inv_cancel₀ hr', one_smul]
      abel
  -- Step 5: the Jensen bound bounds the `v`-side barycentric set from ABOVE.
  have hbdd : ∀ (m : ℝ) (X : F) (T : ℝ), 0 < m →
      BddAbove {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (x' : Fin n → F),
        IsBaryConfig n θ x' X ∧
        w = (∑ i, θ i * v (toLp 2 (x' i, T))) - BaryRadius n θ x' X ^ 2 / (2 * m)} := by
    intro m X T hm
    refine ⟨v (toLp 2 (X, T)) + κ ^ 2 * m / 2, ?_⟩
    rintro w ⟨n, θ, x', hc, rfl⟩
    have hj := hJ T (Set.mem_univ _) n θ x' X hc
    have hρ0 : 0 ≤ BaryRadius n θ x' X := Real.sqrt_nonneg _
    have h2m : (0 : ℝ) < 2 * m := by linarith
    have hdiv : κ * BaryRadius n θ x' X - κ ^ 2 * m / 2
        ≤ BaryRadius n θ x' X ^ 2 / (2 * m) := by
      rw [le_div_iff₀ h2m]
      nlinarith [sq_nonneg (BaryRadius n θ x' X - κ * m)]
    linarith
  -- Step 6: taking suprema across a positive affine bijection of the two defining sets.
  have hsup : ∀ (Sa Sb : Set ℝ) (K : ℝ), Sa.Nonempty → Sb.Nonempty → BddAbove Sb →
      (∀ w ∈ Sa, r * (w + K) ∈ Sb) → (∀ w ∈ Sb, w / r - K ∈ Sa) →
      sSup Sa = sSup Sb / r - K := by
    intro Sa Sb K hane hbne hbdd' hf hb
    have habdd : BddAbove Sa := by
      obtain ⟨M, hM⟩ := hbdd'
      refine ⟨M / r - K, fun w hw => ?_⟩
      have h1 : r * (w + K) ≤ M := hM (hf w hw)
      rw [le_sub_iff_add_le, le_div_iff₀ hr, mul_comm]
      exact h1
    refine le_antisymm (csSup_le hane fun w hw => ?_) ?_
    · have h1 := le_csSup hbdd' (hf w hw)
      rw [le_sub_iff_add_le, le_div_iff₀ hr, mul_comm]
      exact h1
    · rw [sub_le_iff_le_add, div_le_iff₀ hr]
      refine csSup_le hbne fun w hw => ?_
      have h1 := le_csSup habdd (hb w hw)
      rw [← div_le_iff₀ hr]
      linarith
  -- Step 7: the barycentric gap identity, at explicit frame coordinates.
  have key0 : ∀ (σ : ℝ) (y : F) (s : ℝ), 0 < σ →
      BaryEnv (fun ξ => FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
            (ξ - toLp 2 ((0 : F), (1 : ℝ)))) σ (toLp 2 (y, s))
        - FrameChange v (toLp 2 (x₀, r)) r p₀ a₀ (toLp 2 (y, s) - toLp 2 ((0 : F), (1 : ℝ)))
      = (BaryEnv v (r * σ) (toLp 2 (x₀ + r • (y + (s - 1) • p₀), r * s))
          - v (toLp 2 (x₀ + r • (y + (s - 1) • p₀), r * s))) / r := by
    intro σ y s hσ
    have hσ' : σ ≠ 0 := ne_of_gt hσ
    have hrσ : 0 < r * σ := mul_pos hr hσ
    have hval : ∀ w : F, v (toLp 2 (x₀ + r • (w + (s - 1) • p₀), r * s))
        = r * (FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
              (toLp 2 (w, s) - toLp 2 ((0 : F), (1 : ℝ)))
            + (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1) + inner ℝ p₀ w)) := by
      intro w
      rw [hvbar (toLp 2 (w, s))]
      field_simp
      ring
    have hfwd : ∀ w ∈ {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y' : Fin n → F),
          IsBaryConfig n θ y' y ∧
          w = (∑ i, θ i * FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
                (toLp 2 (y' i, s) - toLp 2 ((0 : F), (1 : ℝ))))
              - BaryRadius n θ y' y ^ 2 / (2 * σ)},
        r * (w + (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1) + inner ℝ p₀ y))
          ∈ {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (x' : Fin n → F),
            IsBaryConfig n θ x' (x₀ + r • (y + (s - 1) • p₀)) ∧
            w = (∑ i, θ i * v (toLp 2 (x' i, r * s)))
                - BaryRadius n θ x' (x₀ + r • (y + (s - 1) • p₀)) ^ 2 / (2 * (r * σ))} := by
      rintro w ⟨n, θ, y', hc, rfl⟩
      refine ⟨n, θ, fun i => x₀ + r • (y' i + (s - 1) • p₀), hcfwd s n θ y' y hc, ?_⟩
      rw [hrad s n θ y' y]
      have hterm : ∀ i, θ i * v (toLp 2 (x₀ + r • (y' i + (s - 1) • p₀), r * s))
          = r * (θ i * FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
              (toLp 2 (y' i, s) - toLp 2 ((0 : F), (1 : ℝ))))
            + r * (θ i * (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1)
              + inner ℝ p₀ (y' i))) := by
        intro i; rw [hval (y' i)]; ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum,
        hmean (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1)) n θ y' y hc]
      field_simp
      ring
    have hbwd : ∀ w ∈ {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (x' : Fin n → F),
          IsBaryConfig n θ x' (x₀ + r • (y + (s - 1) • p₀)) ∧
          w = (∑ i, θ i * v (toLp 2 (x' i, r * s)))
              - BaryRadius n θ x' (x₀ + r • (y + (s - 1) • p₀)) ^ 2 / (2 * (r * σ))},
        w / r - (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1) + inner ℝ p₀ y)
          ∈ {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y' : Fin n → F),
            IsBaryConfig n θ y' y ∧
            w = (∑ i, θ i * FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
                  (toLp 2 (y' i, s) - toLp 2 ((0 : F), (1 : ℝ))))
                - BaryRadius n θ y' y ^ 2 / (2 * σ)} := by
      rintro w ⟨n, θ, x', hc, rfl⟩
      obtain ⟨hcy, hxi⟩ := hcbwd s y n θ x' hc
      refine ⟨n, θ, fun i => r⁻¹ • (x' i - x₀) - (s - 1) • p₀, hcy, ?_⟩
      have hfun : (fun i => x₀ + r • ((r⁻¹ • (x' i - x₀) - (s - 1) • p₀) + (s - 1) • p₀)) = x' :=
        funext hxi
      have hrx : BaryRadius n θ x' (x₀ + r • (y + (s - 1) • p₀))
          = r * BaryRadius n θ (fun i => r⁻¹ • (x' i - x₀) - (s - 1) • p₀) y := by
        rw [← hrad s n θ (fun i => r⁻¹ • (x' i - x₀) - (s - 1) • p₀) y, hfun]
      have hterm : ∀ i, v (toLp 2 (x' i, r * s))
          = r * (FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
                (toLp 2 (r⁻¹ • (x' i - x₀) - (s - 1) • p₀, s) - toLp 2 ((0 : F), (1 : ℝ)))
              + (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1)
                + inner ℝ p₀ (r⁻¹ • (x' i - x₀) - (s - 1) • p₀))) := by
        intro i
        have h := hval (r⁻¹ • (x' i - x₀) - (s - 1) • p₀)
        rw [hxi i] at h
        exact h
      have hsum2 : (∑ i, θ i * v (toLp 2 (x' i, r * s)))
          = r * ((∑ i, θ i * FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
                (toLp 2 (r⁻¹ • (x' i - x₀) - (s - 1) • p₀, s) - toLp 2 ((0 : F), (1 : ℝ))))
              + (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1) + inner ℝ p₀ y)) := by
        have hh : ∀ i, θ i * v (toLp 2 (x' i, r * s))
            = r * (θ i * FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
                (toLp 2 (r⁻¹ • (x' i - x₀) - (s - 1) • p₀, s) - toLp 2 ((0 : F), (1 : ℝ))))
              + r * (θ i * (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1)
                + inner ℝ p₀ (r⁻¹ • (x' i - x₀) - (s - 1) • p₀))) := by
          intro i; rw [hterm i]; ring
        rw [Finset.sum_congr rfl fun i _ => hh i, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum,
          hmean (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1)) n θ
            (fun i => r⁻¹ • (x' i - x₀) - (s - 1) • p₀) y hcy]
        ring
      rw [hrx, hsum2]
      field_simp
      ring
    have hSbne : ({w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y' : Fin n → F),
        IsBaryConfig n θ y' y ∧
        w = (∑ i, θ i * FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
              (toLp 2 (y' i, s) - toLp 2 ((0 : F), (1 : ℝ))))
            - BaryRadius n θ y' y ^ 2 / (2 * σ)}).Nonempty := by
      refine ⟨_, 1, fun _ => 1, fun _ => y, ⟨fun i => one_pos, by simp, by simp⟩, rfl⟩
    have hSne : ({w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (x' : Fin n → F),
        IsBaryConfig n θ x' (x₀ + r • (y + (s - 1) • p₀)) ∧
        w = (∑ i, θ i * v (toLp 2 (x' i, r * s)))
            - BaryRadius n θ x' (x₀ + r • (y + (s - 1) • p₀)) ^ 2 / (2 * (r * σ))}).Nonempty := by
      refine ⟨_, 1, fun _ => 1, fun _ => x₀ + r • (y + (s - 1) • p₀),
        ⟨fun i => one_pos, by simp, by simp⟩, rfl⟩
    have hmain := hsup _ _
      (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (s - 1) + inner ℝ p₀ y)
      hSbne hSne (hbdd (r * σ) (x₀ + r • (y + (s - 1) • p₀)) (r * s) hrσ) hfwd hbwd
    simp only [BaryEnv]
    rw [hmain, hvbar (toLp 2 (y, s))]
    rw [sub_div]
    ring
  refine ⟨fun σ ζ hσ => key0 σ (ofLp ζ).1 (ofLp ζ).2 hσ, ?_⟩
  intro ζ hs
  have h1 := key0 (ofLp ζ).2 (ofLp ζ).1 (ofLp ζ).2 hs
  simp only [ContactEnv]
  rw [eq_div_iff hr'] at h1 ⊢
  have h2 : κ ^ 2 * (ofLp ζ).2 / 2 * r = κ ^ 2 * (r * (ofLp ζ).2) / 2 := by ring
  linarith [h1, h2]
