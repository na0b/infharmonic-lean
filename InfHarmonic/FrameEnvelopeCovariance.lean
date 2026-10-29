module

public import InfHarmonic.FrameInvariance
public import InfHarmonic.EnvSlopeP
public import InfHarmonic.EnvSlopeM
public import InfHarmonic.HasJensenBound
public import InfHarmonic.IsCenteredAt
public import InfHarmonic.UniformSubquadratic
public import InfHarmonic.EnvelopeCompetitorBounds

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 6.5, first part: the contact frame based at a fit at `(x₀, r)` of
radius `r` carries `v` to a member of `A_{m,C₀}` centered at `(0,1)` with
the same Jensen constant, and the envelope slopes transform by
`S_ℓ^± v̄ (y,s) = S_{rℓ}^± v (x,t) - a₀`. -/
theorem FrameEnvelopeCovariance (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hJ : HasJensenBound Set.univ v κ)
    (r : ℝ) (hr : 0 < r) (x₀ p₀ : F) (a₀ : ℝ)
    (hfit : IsFit C₀ v (toLp 2 (x₀, r)) r p₀ a₀) :
    IsFitClass C₀
        (fun ζ => FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
          (ζ - toLp 2 ((0 : F), (1 : ℝ)))) ∧
    IsCenteredAt C₀
        (fun ζ => FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
          (ζ - toLp 2 ((0 : F), (1 : ℝ)))) (toLp 2 ((0 : F), (1 : ℝ))) ∧
    HasJensenBound Set.univ
        (fun ζ => FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
          (ζ - toLp 2 ((0 : F), (1 : ℝ)))) κ ∧
    (∀ (l : ℝ) (ζ : WithLp 2 (F × ℝ)), 0 < l →
      EnvSlopeP (fun ξ => FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
            (ξ - toLp 2 ((0 : F), (1 : ℝ)))) l ζ
        = EnvSlopeP v (r * l)
            (toLp 2 (x₀ + r • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • p₀), r * (ofLp ζ).2))
          - a₀ ∧
      EnvSlopeM (fun ξ => FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
            (ξ - toLp 2 ((0 : F), (1 : ℝ)))) l ζ
        = EnvSlopeM v (r * l)
            (toLp 2 (x₀ + r • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • p₀), r * (ofLp ζ).2))
          - a₀) := by
  classical
  -- `κ` enters only through the hypothesis transported in Step 2, whose statement
  -- carries it; the frozen signature still binds it, so name it once.
  have _unused_hκ : 0 ≤ κ := hκ
  have hrne : r ≠ 0 := ne_of_gt hr
  -- ===== the framed function, the frame map and the affine correction, bound once =====
  obtain ⟨g, hg⟩ : ∃ w : WithLp 2 (F × ℝ) → ℝ, w = fun ζ =>
      FrameChange v (toLp 2 (x₀, r)) r p₀ a₀ (ζ - toLp 2 ((0 : F), (1 : ℝ))) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ S : WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ), S = fun ξ =>
      toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ a : WithLp 2 (F × ℝ) → ℝ, a = fun ξ =>
      v (toLp 2 (x₀, r)) / r + inner ℝ p₀ (ofLp ξ).1
        + (a₀ + ‖p₀‖ ^ 2 / 2) * ((ofLp ξ).2 - 1) := ⟨_, rfl⟩
  have hgval : ∀ ξ : WithLp 2 (F × ℝ),
      g ξ = FrameChange v (toLp 2 (x₀, r)) r p₀ a₀ (ξ - toLp 2 ((0 : F), (1 : ℝ))) := by
    intro ξ; rw [hg]
  rw [← hg]
  have hrcan : ∀ S : ℝ, r * (S / r) = S := by intro S; field_simp
  have hTval : ∀ ξ : WithLp 2 (F × ℝ),
      T ξ = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2) := by
    intro ξ; rw [hT]
  have hTfst : ∀ ξ : WithLp 2 (F × ℝ),
      (ofLp (T ξ)).1 = x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀) := by
    intro ξ; rw [hTval]
  have hTsnd : ∀ ξ : WithLp 2 (F × ℝ), (ofLp (T ξ)).2 = r * (ofLp ξ).2 := by
    intro ξ; rw [hTval]
  have hAlp : ∀ (u : F) (σ : ℝ), A (toLp 2 (u, σ))
      = v (toLp 2 (x₀, r)) / r + inner ℝ p₀ u + (a₀ + ‖p₀‖ ^ 2 / 2) * (σ - 1) := by
    intro u σ; rw [hA]
  have hAval : ∀ ξ : WithLp 2 (F × ℝ), A ξ
      = v (toLp 2 (x₀, r)) / r + inner ℝ p₀ (ofLp ξ).1
        + (a₀ + ‖p₀‖ ^ 2 / 2) * ((ofLp ξ).2 - 1) := by
    intro ξ; rw [hA]
  -- the shift coordinates of the frame-changed argument
  have hofs1 : ∀ ξ : WithLp 2 (F × ℝ),
      (ofLp (ξ - toLp 2 ((0 : F), (1 : ℝ)))).1 = (ofLp ξ).1 := by intro ξ; simp
  have hofs2 : ∀ ξ : WithLp 2 (F × ℝ),
      (ofLp (ξ - toLp 2 ((0 : F), (1 : ℝ)))).2 = (ofLp ξ).2 - 1 := by intro ξ; simp
  -- ===== eq:fec-split : `v` at the corresponding point splits as `r (v̄ + A)` =====
  have hsplit : ∀ ξ : WithLp 2 (F × ℝ), v (T ξ) = r * (g ξ + A ξ) := by
    intro ξ
    have hpt : (toLp 2 (x₀, r) : WithLp 2 (F × ℝ))
        + toLp 2 (r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * ((ofLp ξ).2 - 1))
        = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2) := by
      have h1 : (toLp 2 (x₀, r) : WithLp 2 (F × ℝ))
          + toLp 2 (r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * ((ofLp ξ).2 - 1))
          = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀),
              r + r * ((ofLp ξ).2 - 1)) := rfl
      rw [h1, show r + r * ((ofLp ξ).2 - 1) = r * (ofLp ξ).2 from by ring]
    rw [hTval, hgval, hAval]
    simp only [FrameChange]
    rw [hofs1, hofs2, hpt]
    field_simp
    ring
  -- ===== Step 1 : the framed function is a constant shift of a change of frame =====
  obtain ⟨K, hK⟩ : ∃ c : ℝ, c
      = (v (toLp 2 (x₀, r)) - v (toLp 2 (x₀ - r • p₀, (0 : ℝ)))) / r
        - (a₀ + ‖p₀‖ ^ 2 / 2) := ⟨_, rfl⟩
  have hgfun : g = fun ξ => FrameChange v (toLp 2 (x₀ - r • p₀, (0 : ℝ))) r p₀ a₀ ξ - K := by
    funext ξ
    have hpt1 : (toLp 2 (x₀, r) : WithLp 2 (F × ℝ))
        + toLp 2 (r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * ((ofLp ξ).2 - 1))
        = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2) := by
      have h1 : (toLp 2 (x₀, r) : WithLp 2 (F × ℝ))
          + toLp 2 (r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * ((ofLp ξ).2 - 1))
          = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀),
              r + r * ((ofLp ξ).2 - 1)) := rfl
      rw [h1, show r + r * ((ofLp ξ).2 - 1) = r * (ofLp ξ).2 from by ring]
    have hpt2 : (toLp 2 (x₀ - r • p₀, (0 : ℝ)) : WithLp 2 (F × ℝ))
        + toLp 2 (r • ((ofLp ξ).1 + (ofLp ξ).2 • p₀), r * (ofLp ξ).2)
        = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2) := by
      have h1 : (toLp 2 (x₀ - r • p₀, (0 : ℝ)) : WithLp 2 (F × ℝ))
          + toLp 2 (r • ((ofLp ξ).1 + (ofLp ξ).2 • p₀), r * (ofLp ξ).2)
          = toLp 2 (x₀ - r • p₀ + r • ((ofLp ξ).1 + (ofLp ξ).2 • p₀),
              0 + r * (ofLp ξ).2) := rfl
      rw [h1, show x₀ - r • p₀ + r • ((ofLp ξ).1 + (ofLp ξ).2 • p₀)
            = x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀) from by module, zero_add]
    rw [hgval, hK]
    simp only [FrameChange]
    rw [hofs1, hofs2, hpt1, hpt2]
    field_simp
    ring
  -- ===== the constant-shift invariance of the whole fit package =====
  have hfitshift : ∀ (w : WithLp 2 (F × ℝ) → ℝ) (Kc : ℝ) (z : WithLp 2 (F × ℝ)) (R : ℝ)
      (p : F) (a : ℝ), IsFit C₀ w z R p a → IsFit C₀ (fun ν => w ν - Kc) z R p a := by
    intro w Kc z R p a hf h l hl hhl
    have hb := hf h l hl hhl
    show |w (z + toLp 2 (h, l)) - Kc - (w z - Kc) - inner ℝ p h
        - (a - ‖p‖ ^ 2 / 2) * l| ≤ C₀ * R
    rw [show w (z + toLp 2 (h, l)) - Kc - (w z - Kc) - inner ℝ p h
          - (a - ‖p‖ ^ 2 / 2) * l
        = w (z + toLp 2 (h, l)) - w z - inner ℝ p h - (a - ‖p‖ ^ 2 / 2) * l from by ring]
    exact hb
  have hLimitOpSub : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (ζ : WithLp 2 (F × ℝ)) (Kc : ℝ),
      ContDiffAt ℝ 2 φ ζ → LimitOp (fun ν => φ ν - Kc) ζ = LimitOp φ ζ := by
    intro φ ζ Kc hφ
    have hgr : gradient (fun ν : WithLp 2 (F × ℝ) => φ ν - Kc) ζ = gradient φ ζ := by
      simp only [gradient, fderiv_sub_const]
    have hjet : iteratedFDeriv ℝ 2 (fun ν : WithLp 2 (F × ℝ) => φ ν - Kc) ζ
        = iteratedFDeriv ℝ 2 φ ζ := by
      have heq : (fun ν : WithLp 2 (F × ℝ) => φ ν - Kc)
          = (fun ν : WithLp 2 (F × ℝ) => φ ν + (-Kc)) := by funext ν; ring
      rw [heq, fun_iteratedFDeriv_add_apply hφ contDiffAt_const,
        iteratedFDeriv_const_of_ne (n := 2) (by norm_num)]
      simp
    rw [LimitOp, LimitOp, hgr, hjet]
  have hclassshift : ∀ (w : WithLp 2 (F × ℝ) → ℝ) (Kc : ℝ),
      IsFitClass C₀ w → IsFitClass C₀ (fun ν => w ν - Kc) := by
    intro w Kc hw
    refine ⟨⟨⟨isOpen_univ, hw.1.1.2.1.sub continuousOn_const, ?_⟩,
      ⟨isOpen_univ, hw.1.2.2.1.sub continuousOn_const, ?_⟩⟩, ?_⟩
    · intro ζ _ φ hφ hmax
      have hφ' : ContDiffAt ℝ 2 (fun ν : WithLp 2 (F × ℝ) => φ ν - Kc) ζ :=
        hφ.sub contDiffAt_const
      have hmax' : IsLocalMaxOn (fun ν => w ν - (fun ν => φ ν - Kc) ν)
          (Set.univ : Set (WithLp 2 (F × ℝ))) ζ := by
        show ∀ᶠ ν in nhdsWithin ζ (Set.univ : Set (WithLp 2 (F × ℝ))),
          w ν - (φ ν - Kc) ≤ w ζ - (φ ζ - Kc)
        have h0 : ∀ᶠ ν in nhdsWithin ζ (Set.univ : Set (WithLp 2 (F × ℝ))),
            w ν - Kc - φ ν ≤ w ζ - Kc - φ ζ := hmax
        filter_upwards [h0] with ν hν
        linarith
      have hres := hw.1.1.2.2 ζ (Set.mem_univ _) (fun ν => φ ν - Kc) hφ' hmax'
      rwa [hLimitOpSub φ ζ Kc hφ] at hres
    · intro ζ _ φ hφ hmin
      have hφ' : ContDiffAt ℝ 2 (fun ν : WithLp 2 (F × ℝ) => φ ν - Kc) ζ :=
        hφ.sub contDiffAt_const
      have hmin' : IsLocalMinOn (fun ν => w ν - (fun ν => φ ν - Kc) ν)
          (Set.univ : Set (WithLp 2 (F × ℝ))) ζ := by
        show ∀ᶠ ν in nhdsWithin ζ (Set.univ : Set (WithLp 2 (F × ℝ))),
          w ζ - (φ ζ - Kc) ≤ w ν - (φ ν - Kc)
        have h0 : ∀ᶠ ν in nhdsWithin ζ (Set.univ : Set (WithLp 2 (F × ℝ))),
            w ζ - Kc - φ ζ ≤ w ν - Kc - φ ν := hmin
        filter_upwards [h0] with ν hν
        linarith
      have hres := hw.1.2.2.2 ζ (Set.mem_univ _) (fun ν => φ ν - Kc) hφ' hmin'
      rwa [hLimitOpSub φ ζ Kc hφ] at hres
    · intro ζ ρ hρ
      obtain ⟨p, a, hf⟩ := hw.2 ζ ρ hρ
      exact ⟨p, a, hfitshift w Kc ζ ρ p a hf⟩
  -- ===== Step 2 : class and centering =====
  obtain ⟨hFIclass, hFIfit⟩ :=
    FrameInvariance C₀ v hv (toLp 2 (x₀ - r • p₀, (0 : ℝ))) r hr p₀ a₀
  have hc1 : IsFitClass C₀ g := by rw [hgfun]; exact hclassshift _ K hFIclass
  have hzero : g (toLp 2 ((0 : F), (1 : ℝ))) = 0 := by
    have hpt : (toLp 2 (x₀, r) : WithLp 2 (F × ℝ))
        + toLp 2 (r • ((0 : F) + ((1 : ℝ) - 1) • p₀), r * ((1 : ℝ) - 1))
        = toLp 2 (x₀, r) := by
      have h1 : (toLp 2 (x₀, r) : WithLp 2 (F × ℝ))
          + toLp 2 (r • ((0 : F) + ((1 : ℝ) - 1) • p₀), r * ((1 : ℝ) - 1))
          = toLp 2 (x₀ + r • ((0 : F) + ((1 : ℝ) - 1) • p₀),
              r + r * ((1 : ℝ) - 1)) := rfl
      rw [h1, show x₀ + r • ((0 : F) + ((1 : ℝ) - 1) • p₀) = x₀ from by module,
        show r + r * ((1 : ℝ) - 1) = r from by ring]
    rw [hgval]
    simp only [FrameChange]
    rw [hofs1, hofs2]
    show (v ((toLp 2 (x₀, r) : WithLp 2 (F × ℝ))
        + toLp 2 (r • ((ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).1
            + ((ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 - 1) • p₀),
          r * ((ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 - 1)))
        - v (toLp 2 (x₀, r))) / r
      - inner ℝ p₀ (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).1
      - (a₀ + ‖p₀‖ ^ 2 / 2)
          * ((ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 - 1) = 0
    rw [hpt]
    simp
  have hc2 : IsCenteredAt C₀ g (toLp 2 ((0 : F), (1 : ℝ))) := by
    refine ⟨hzero, ?_⟩
    have hbase : (toLp 2 (x₀ - r • p₀, (0 : ℝ)) : WithLp 2 (F × ℝ))
        + toLp 2 (r • ((ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).1
            + (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 • p₀),
          r * (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2)
        = toLp 2 (x₀, r) := by
      have h1 : (toLp 2 (x₀ - r • p₀, (0 : ℝ)) : WithLp 2 (F × ℝ))
          + toLp 2 (r • ((0 : F) + (1 : ℝ) • p₀), r * (1 : ℝ))
          = toLp 2 (x₀ - r • p₀ + r • ((0 : F) + (1 : ℝ) • p₀), 0 + r * (1 : ℝ)) := rfl
      rw [show (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).1 = (0 : F) from rfl,
        show (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 = (1 : ℝ) from rfl,
        h1, show x₀ - r • p₀ + r • ((0 : F) + (1 : ℝ) • p₀) = x₀ from by module,
        show (0 : ℝ) + r * (1 : ℝ) = r from by ring]
    have hin : IsFit C₀ v ((toLp 2 (x₀ - r • p₀, (0 : ℝ)) : WithLp 2 (F × ℝ))
        + toLp 2 (r • ((ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).1
            + (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 • p₀),
          r * (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2)) (r * 1) p₀ a₀ := by
      rw [hbase, mul_one]; exact hfit
    have hout := hFIfit (toLp 2 ((0 : F), (1 : ℝ))) 1 p₀ a₀ hin
    rw [sub_self, sub_self] at hout
    rw [hgfun]
    exact hfitshift _ K _ _ _ _ hout
  -- ===== Step 2 : the Jensen bound =====
  have haffsum : ∀ (n : ℕ) (θ : Fin n → ℝ) (yy : Fin n → F) (xx c : F),
      (∑ i, θ i = 1) → (∑ i, θ i • yy i = xx) →
      ∑ i, θ i • (c + r • yy i) = c + r • xx := by
    intro n θ yy xx c h1 h2
    have hstep : ∀ i, θ i • (c + r • yy i) = θ i • c + r • (θ i • yy i) := by
      intro i; module
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib,
      ← Finset.sum_smul, h1, one_smul, ← Finset.smul_sum, h2]
  have hradscale : ∀ (n : ℕ) (θ : Fin n → ℝ) (yy : Fin n → F) (xx c : F),
      BaryRadius n θ (fun i => c + r • yy i) (c + r • xx) = r * BaryRadius n θ yy xx := by
    intro n θ yy xx c
    have hd : ∀ i, ‖c + r • yy i - (c + r • xx)‖ ^ 2 = r ^ 2 * ‖yy i - xx‖ ^ 2 := by
      intro i
      rw [show c + r • yy i - (c + r • xx) = r • (yy i - xx) from by module,
        norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hsum : ∑ i, θ i * ‖c + r • yy i - (c + r • xx)‖ ^ 2
        = r ^ 2 * ∑ i, θ i * ‖yy i - xx‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hd i]; ring
    rw [BaryRadius, BaryRadius, hsum, Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
  have hinnersum : ∀ (n : ℕ) (θ : Fin n → ℝ) (yy : Fin n → F),
      (inner ℝ p₀ (∑ i, θ i • yy i) : ℝ) = ∑ i, θ i * inner ℝ p₀ (yy i) := by
    intro n θ yy
    rw [inner_sum]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_right _ _ _
  have hc3 : HasJensenBound Set.univ g κ := by
    intro σ _ n θ yy xx hcfg
    obtain ⟨hθpos, hθ1, hθmean⟩ := hcfg
    obtain ⟨c, hc⟩ : ∃ u : F, u = x₀ + (r * (σ - 1)) • p₀ := ⟨_, rfl⟩
    -- the mapped configuration
    have hmap : ∀ u : F, T (toLp 2 (u, σ)) = toLp 2 (c + r • u, r * σ) := by
      intro u
      rw [hTval, hc]
      show (toLp 2 (x₀ + r • ((u : F) + (σ - 1) • p₀), r * σ) : WithLp 2 (F × ℝ))
        = toLp 2 (x₀ + (r * (σ - 1)) • p₀ + r • u, r * σ)
      rw [show x₀ + r • ((u : F) + (σ - 1) • p₀)
          = x₀ + (r * (σ - 1)) • p₀ + r • u from by module]
    have hcfgnew : IsBaryConfig n θ (fun i => c + r • yy i) (c + r • xx) :=
      ⟨hθpos, hθ1, by rw [haffsum n θ yy xx c hθ1 hθmean]⟩
    have hJv := hJ (r * σ) (Set.mem_univ _) n θ (fun i => c + r • yy i) (c + r • xx) hcfgnew
    rw [hradscale n θ yy xx c] at hJv
    -- the affine terms cancel from the barycentric defect
    have hAsum : ∑ i, θ i * A (toLp 2 (yy i, σ)) = A (toLp 2 (xx, σ)) := by
      have hstep : ∀ i, θ i * A (toLp 2 (yy i, σ))
          = θ i * (v (toLp 2 (x₀, r)) / r + (a₀ + ‖p₀‖ ^ 2 / 2) * (σ - 1))
            + θ i * inner ℝ p₀ (yy i) := by
        intro i; rw [hAlp]; ring
      rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib,
        ← Finset.sum_mul, hθ1, one_mul, ← hinnersum n θ yy, hθmean, hAlp]
      ring
    -- the defect identity eq:fec-defect
    have hval : ∀ u : F, v (toLp 2 (c + r • u, r * σ)) = r * (g (toLp 2 (u, σ))
        + A (toLp 2 (u, σ))) := by
      intro u; rw [← hmap u]; exact hsplit _
    have hdef : (∑ i, θ i * v (toLp 2 (c + r • yy i, r * σ)))
        - v (toLp 2 (c + r • xx, r * σ))
        = r * ((∑ i, θ i * g (toLp 2 (yy i, σ))) - g (toLp 2 (xx, σ))) := by
      have hstep : ∀ i, θ i * v (toLp 2 (c + r • yy i, r * σ))
          = r * (θ i * g (toLp 2 (yy i, σ))) + r * (θ i * A (toLp 2 (yy i, σ))) := by
        intro i; rw [hval]; ring
      rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hAsum, hval xx]
      ring
    rw [hdef] at hJv
    -- divide the defect bound by `r`
    have hfin : r * ((∑ i, θ i * g (toLp 2 (yy i, σ))) - g (toLp 2 (xx, σ)))
        ≤ r * (κ * BaryRadius n θ yy xx) := by
      calc r * ((∑ i, θ i * g (toLp 2 (yy i, σ))) - g (toLp 2 (xx, σ)))
          ≤ κ * (r * BaryRadius n θ yy xx) := hJv
        _ = r * (κ * BaryRadius n θ yy xx) := by ring
    exact le_of_mul_le_mul_left hfin hr
  -- ===== Step 3 : the admissibility of the framed function on `I = ℝ` =====
  have hIuniv : ((fun ξ : WithLp 2 (F × ℝ) => (ofLp ξ).2) ⁻¹' (Set.univ : Set ℝ))
      = (Set.univ : Set (WithLp 2 (F × ℝ))) := Set.preimage_univ
  have hgcont : ContinuousOn g
      ((fun ξ : WithLp 2 (F × ℝ) => (ofLp ξ).2) ⁻¹' (Set.univ : Set ℝ)) := by
    rw [hIuniv]; exact hc1.1.1.2.1
  have hggrow : SubquadraticGrowth (Set.univ : Set ℝ) g := by
    intro J _ hJc η hη
    obtain ⟨M, hM0, hMb⟩ :=
      UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc η hη
    exact ⟨M, hM0, fun ξ hξ hξJ => hMb g hc1 hc2 ξ hξ hξJ⟩
  obtain ⟨hdomPg, hdomMg, -⟩ := EnvelopeCompetitorBounds (Set.univ : Set ℝ) g hgcont hggrow
  -- the two envelope defining equations at a nonzero length
  have hPdef : ∀ (f : WithLp 2 (F × ℝ) → ℝ) (L : ℝ) (z : WithLp 2 (F × ℝ)), L ≠ 0 →
      QuadEnvP f L z = sSup {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 + L)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * L)} := by
    intro f L z hL; rw [QuadEnvP, if_neg hL]
  have hMdef : ∀ (f : WithLp 2 (F × ℝ) → ℝ) (L : ℝ) (z : WithLp 2 (F × ℝ)), L ≠ 0 →
      QuadEnvM f L z = sInf {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 - L)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * L)} := by
    intro f L z hL; rw [QuadEnvM, if_neg hL]
  have hnormsmul : ∀ (cs : ℝ) (u : F), ‖cs • u‖ ^ 2 = cs ^ 2 * ‖u‖ ^ 2 := by
    intro cs u; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  -- ===== Step 4 : the slope covariance =====
  refine ⟨hc1, hc2, hc3, ?_⟩
  intro l ζ hl
  have hlne : l ≠ 0 := ne_of_gt hl
  have hrl : (0 : ℝ) < r * l := mul_pos hr hl
  have hrlne : r * l ≠ 0 := ne_of_gt hrl
  rw [← hTval ζ]
  obtain ⟨hPdom, hPleast⟩ := hdomPg l ζ hl (Set.mem_univ _) (Set.mem_univ _)
  obtain ⟨hMdom, hMleast⟩ := hdomMg l ζ hl (Set.mem_univ _) (Set.mem_univ _)
  -- the forward reparametrization of the competitor variable
  have hsurjP : ∀ x' : F, ∃ y' : F,
      x' = x₀ + r • (y' + ((ofLp ζ).2 + l - 1) • p₀) := by
    intro x'
    refine ⟨r⁻¹ • (x' - x₀) - ((ofLp ζ).2 + l - 1) • p₀, ?_⟩
    rw [show r⁻¹ • (x' - x₀) - ((ofLp ζ).2 + l - 1) • p₀
          + ((ofLp ζ).2 + l - 1) • p₀ = r⁻¹ • (x' - x₀) from by abel,
      smul_smul, mul_inv_cancel₀ hrne, one_smul]
    abel
  have hsurjM : ∀ x' : F, ∃ y' : F,
      x' = x₀ + r • (y' + ((ofLp ζ).2 - l - 1) • p₀) := by
    intro x'
    refine ⟨r⁻¹ • (x' - x₀) - ((ofLp ζ).2 - l - 1) • p₀, ?_⟩
    rw [show r⁻¹ • (x' - x₀) - ((ofLp ζ).2 - l - 1) • p₀
          + ((ofLp ζ).2 - l - 1) • p₀ = r⁻¹ • (x' - x₀) from by abel,
      smul_smul, mul_inv_cancel₀ hrne, one_smul]
    abel
  -- the forward correspondence of competitor values
  have hcorrP : ∀ y' : F,
      v (toLp 2 (x₀ + r • (y' + ((ofLp ζ).2 + l - 1) • p₀), (ofLp (T ζ)).2 + r * l))
        - ‖x₀ + r • (y' + ((ofLp ζ).2 + l - 1) • p₀) - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))
      = r * (g (toLp 2 (y', (ofLp ζ).2 + l)) - ‖y' - (ofLp ζ).1‖ ^ 2 / (2 * l)
          + (A ζ + a₀ * l)) := by
    intro y'
    have hpt : (toLp 2 (x₀ + r • (y' + ((ofLp ζ).2 + l - 1) • p₀),
        (ofLp (T ζ)).2 + r * l) : WithLp 2 (F × ℝ))
        = T (toLp 2 (y', (ofLp ζ).2 + l)) := by
      rw [hTsnd ζ, hTval (toLp 2 (y', (ofLp ζ).2 + l))]
      show (toLp 2 (x₀ + r • (y' + ((ofLp ζ).2 + l - 1) • p₀),
          r * (ofLp ζ).2 + r * l) : WithLp 2 (F × ℝ))
        = toLp 2 (x₀ + r • (y' + ((ofLp ζ).2 + l - 1) • p₀), r * ((ofLp ζ).2 + l))
      rw [show r * (ofLp ζ).2 + r * l = r * ((ofLp ζ).2 + l) from by ring]
    have hdisp : x₀ + r • (y' + ((ofLp ζ).2 + l - 1) • p₀) - (ofLp (T ζ)).1
        = r • (y' - (ofLp ζ).1 + l • p₀) := by rw [hTfst]; module
    have hnorm : ‖r • (y' - (ofLp ζ).1 + l • p₀)‖ ^ 2
        = r ^ 2 * (‖y' - (ofLp ζ).1‖ ^ 2
            + 2 * (l * (inner ℝ p₀ y' - inner ℝ p₀ (ofLp ζ).1)) + l ^ 2 * ‖p₀‖ ^ 2) := by
      rw [hnormsmul]
      congr 1
      rw [norm_add_sq_real (y' - (ofLp ζ).1) (l • p₀), real_inner_smul_right,
        real_inner_comm, inner_sub_right, hnormsmul]
    rw [hpt, hsplit, hdisp, hnorm, hAlp, hAval]
    field_simp
    ring
  -- the backward correspondence of competitor values
  have hcorrM : ∀ y' : F,
      v (toLp 2 (x₀ + r • (y' + ((ofLp ζ).2 - l - 1) • p₀), (ofLp (T ζ)).2 - r * l))
        + ‖x₀ + r • (y' + ((ofLp ζ).2 - l - 1) • p₀) - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))
      = r * (g (toLp 2 (y', (ofLp ζ).2 - l)) + ‖y' - (ofLp ζ).1‖ ^ 2 / (2 * l)
          + (A ζ - a₀ * l)) := by
    intro y'
    have hpt : (toLp 2 (x₀ + r • (y' + ((ofLp ζ).2 - l - 1) • p₀),
        (ofLp (T ζ)).2 - r * l) : WithLp 2 (F × ℝ))
        = T (toLp 2 (y', (ofLp ζ).2 - l)) := by
      rw [hTsnd ζ, hTval (toLp 2 (y', (ofLp ζ).2 - l))]
      show (toLp 2 (x₀ + r • (y' + ((ofLp ζ).2 - l - 1) • p₀),
          r * (ofLp ζ).2 - r * l) : WithLp 2 (F × ℝ))
        = toLp 2 (x₀ + r • (y' + ((ofLp ζ).2 - l - 1) • p₀), r * ((ofLp ζ).2 - l))
      rw [show r * (ofLp ζ).2 - r * l = r * ((ofLp ζ).2 - l) from by ring]
    have hdisp : x₀ + r • (y' + ((ofLp ζ).2 - l - 1) • p₀) - (ofLp (T ζ)).1
        = r • (y' - (ofLp ζ).1 - l • p₀) := by rw [hTfst]; module
    have hnorm : ‖r • (y' - (ofLp ζ).1 - l • p₀)‖ ^ 2
        = r ^ 2 * (‖y' - (ofLp ζ).1‖ ^ 2
            - 2 * (l * (inner ℝ p₀ y' - inner ℝ p₀ (ofLp ζ).1)) + l ^ 2 * ‖p₀‖ ^ 2) := by
      rw [hnormsmul]
      congr 1
      rw [norm_sub_sq_real (y' - (ofLp ζ).1) (l • p₀), real_inner_smul_right,
        real_inner_comm, inner_sub_right, hnormsmul]
    rw [hpt, hsplit, hdisp, hnorm, hAlp, hAval]
    field_simp
    ring
  -- the forward envelope identity
  have hVbP : ∀ x' : F,
      v (toLp 2 (x', (ofLp (T ζ)).2 + r * l))
          - ‖x' - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))
        ≤ r * (QuadEnvP g l ζ + A ζ + a₀ * l) := by
    intro x'
    obtain ⟨y', rfl⟩ := hsurjP x'
    rw [hcorrP y']
    have hmul : r * (g (toLp 2 (y', (ofLp ζ).2 + l)) - ‖y' - (ofLp ζ).1‖ ^ 2 / (2 * l)
          + (A ζ + a₀ * l))
        ≤ r * (QuadEnvP g l ζ + (A ζ + a₀ * l)) :=
      mul_le_mul_of_nonneg_left (by linarith [hPdom y']) hr.le
    linarith [hmul]
  have hVneP : ({w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 + r * l))
      - ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))}).Nonempty := ⟨_, ⟨(ofLp (T ζ)).1, rfl⟩⟩
  have hVbddP : BddAbove {w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 + r * l))
      - ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))} :=
    ⟨r * (QuadEnvP g l ζ + A ζ + a₀ * l), by rintro w ⟨y, rfl⟩; exact hVbP y⟩
  have hQP : QuadEnvP v (r * l) (T ζ) = r * (QuadEnvP g l ζ + A ζ + a₀ * l) := by
    rw [hPdef v (r * l) (T ζ) hrlne]
    refine le_antisymm (csSup_le hVneP ?_) ?_
    · rintro w ⟨y, rfl⟩; exact hVbP y
    · have hb : QuadEnvP g l ζ
          ≤ sSup {w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 + r * l))
              - ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))} / r - (A ζ + a₀ * l) := by
        refine hPleast _ fun y' => ?_
        have hmem := le_csSup hVbddP
          (⟨x₀ + r • (y' + ((ofLp ζ).2 + l - 1) • p₀), rfl⟩ :
            _ ∈ {w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 + r * l))
              - ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))})
        rw [hcorrP y'] at hmem
        rw [le_sub_iff_add_le, le_div_iff₀ hr]
        linarith [hmem]
      have hmul := mul_le_mul_of_nonneg_left
        (by linarith [hb] :
          QuadEnvP g l ζ + (A ζ + a₀ * l)
            ≤ sSup {w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 + r * l))
              - ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))} / r) hr.le
      rw [hrcan] at hmul
      linarith [hmul]
  -- the backward envelope identity
  have hVbM : ∀ x' : F,
      r * (QuadEnvM g l ζ + A ζ - a₀ * l)
        ≤ v (toLp 2 (x', (ofLp (T ζ)).2 - r * l))
          + ‖x' - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l)) := by
    intro x'
    obtain ⟨y', rfl⟩ := hsurjM x'
    rw [hcorrM y']
    have hmul : r * (QuadEnvM g l ζ + (A ζ - a₀ * l))
        ≤ r * (g (toLp 2 (y', (ofLp ζ).2 - l)) + ‖y' - (ofLp ζ).1‖ ^ 2 / (2 * l)
            + (A ζ - a₀ * l)) :=
      mul_le_mul_of_nonneg_left (by linarith [hMdom y']) hr.le
    linarith [hmul]
  have hVneM : ({w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 - r * l))
      + ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))}).Nonempty := ⟨_, ⟨(ofLp (T ζ)).1, rfl⟩⟩
  have hVbddM : BddBelow {w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 - r * l))
      + ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))} :=
    ⟨r * (QuadEnvM g l ζ + A ζ - a₀ * l), by rintro w ⟨y, rfl⟩; exact hVbM y⟩
  have hQM : QuadEnvM v (r * l) (T ζ) = r * (QuadEnvM g l ζ + A ζ - a₀ * l) := by
    rw [hMdef v (r * l) (T ζ) hrlne]
    refine le_antisymm ?_ (le_csInf hVneM ?_)
    · have hb : sInf {w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 - r * l))
            + ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))} / r - (A ζ - a₀ * l)
          ≤ QuadEnvM g l ζ := by
        refine hMleast _ fun y' => ?_
        have hmem := csInf_le hVbddM
          (⟨x₀ + r • (y' + ((ofLp ζ).2 - l - 1) • p₀), rfl⟩ :
            _ ∈ {w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 - r * l))
              + ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))})
        rw [hcorrM y'] at hmem
        rw [sub_le_iff_le_add, div_le_iff₀ hr]
        linarith [hmem]
      have hmul := mul_le_mul_of_nonneg_left
        (by linarith [hb] :
          sInf {w : ℝ | ∃ y : F, w = v (toLp 2 (y, (ofLp (T ζ)).2 - r * l))
              + ‖y - (ofLp (T ζ)).1‖ ^ 2 / (2 * (r * l))} / r
            ≤ QuadEnvM g l ζ + (A ζ - a₀ * l)) hr.le
      rw [hrcan] at hmul
      linarith [hmul]
    · rintro w ⟨y, rfl⟩; exact hVbM y
  -- the two slope identities
  refine ⟨?_, ?_⟩
  · rw [EnvSlopeP, EnvSlopeP, hQP, hsplit ζ]
    field_simp
    ring
  · rw [EnvSlopeM, EnvSlopeM, hQM, hsplit ζ]
    field_simp
    ring
