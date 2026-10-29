import InfHarmonic.SupConvolutionSeparable
import InfHarmonic.SupConvolutionSemiconvex
open Set
open WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Part III of the theorem of sums, the sup-convolution duality: the
sup-convolution of a separated sum splits into the sum of the sup-convolutions,
and the function `Υ = 𝒢^ε - ⟪Aeps ·, ·⟫ / 2` built from a quadratic test with a
strict maximum at `0` again has a strict global maximum at `0`, is
`(ε⁻¹ + ‖Aeps‖)`-semiconvex, and is continuous. -/
theorem SumRuleDualityTest (N : ℕ) (G : Fin N → E → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hGc : ∀ j, Continuous (G j)) (hGb : ∀ j, ∀ w : E, G j w ≤ C)
    (hG0 : ∀ j, G j 0 = 0)
    (B Aeps : PiLp 2 (fun _ : Fin N => E) →L[ℝ] PiLp 2 (fun _ : Fin N => E))
    (hB : ∀ ξ ζ : PiLp 2 (fun _ : Fin N => E), inner ℝ (B ξ) ζ = inner ℝ ξ (B ζ))
    (hAs : ∀ ξ ζ : PiLp 2 (fun _ : Fin N => E), inner ℝ (Aeps ξ) ζ = inner ℝ ξ (Aeps ζ))
    (ε : ℝ) (hε : 0 < ε)
    (hres : ∀ ξ : PiLp 2 (fun _ : Fin N => E), Aeps ξ = B (ξ + ε • Aeps ξ))
    (hinv : ∀ ξ : PiLp 2 (fun _ : Fin N => E),
      (ξ + ε • Aeps ξ) - ε • B (ξ + ε • Aeps ξ) = ξ)
    (hpos : ∀ ξ : PiLp 2 (fun _ : Fin N => E), ξ ≠ 0 →
      0 < (inner ℝ ξ ξ : ℝ) / ε + inner ℝ (Aeps ξ) ξ)
    (hG3 : ∀ W : PiLp 2 (fun _ : Fin N => E), W ≠ 0 →
      (∑ j, G j (ofLp W j)) - (inner ℝ (B W) W : ℝ) / 2 ≤ -∑ j, ‖ofLp W j‖ ^ 4) :
    (∀ Z : PiLp 2 (fun _ : Fin N => E),
        SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
          = ∑ j, SupConvolution ε (G j) (ofLp Z j)) ∧
      ∃ Υ : PiLp 2 (fun _ : Fin N => E) → ℝ,
        (∀ Z : PiLp 2 (fun _ : Fin N => E), Υ Z =
          SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
            - (inner ℝ (Aeps Z) Z : ℝ) / 2) ∧
        Υ 0 = 0 ∧ (∀ Z : PiLp 2 (fun _ : Fin N => E), Z ≠ 0 → Υ Z < 0) ∧
        SemiconvexOn (1 / ε + ‖Aeps‖) Set.univ Υ ∧ Continuous Υ := by
  classical
  -- Body-only acknowledgement: `hC : 0 ≤ C` is part of this node's (coarse, protected)
  -- signature but the proof never consumes it -- the only use of `C` is the uniform upper
  -- bound `hGb`, which feeds `SupConvolutionSeparable` and the growth bound `(N : ℝ) * C + ‖W‖`
  -- and needs no sign.  Acknowledged here rather than above `-- BODY`, where a linter
  -- suggestion would move the statement region.
  have _hC : (0:ℝ) ≤ C := hC
  -- DURABLE ROUTE NOTE (burst 401, closure burst).  Two places where the Lean takes a
  -- shorter road than the .tex; the .tex route is correct and is kept as written.
  --   * Step 3's last paragraph argues by contradiction ("suppose Υ(Z) = 0 ...").  The Lean
  --     instead CASE-SPLITS ON THE MAXIMIZER: once `hattain` produces a `W` with
  --     Υ Z = Φ W - defect(Z - T W), either `W ≠ 0` and `Φ W < 0` already finishes it, or
  --     `W = 0`, in which case `T 0 = 0`, `Φ 0 = 0` and the defect is the form at `Z` itself,
  --     strictly positive by `hpos`.  No contradiction and no reuse of (eq:srdt-expand).
  --   * (2b)+(2c) are ONE identity in Lean (`hkey` below), not two steps: the exact expansion
  --     and the value at the maximizer are the same algebraic computation, so proving
  --     `F(Z,W) - F(Z_W,W) = -defect(Z - T W)` with `F(Z_W,W) = Φ W` already built in is
  --     cheaper than deriving the vanishing linear term separately.
  -- The three cosmetic .tex items parked here by burst 389 are DISCHARGED in this burst:
  -- (a) the (eq:srdt-TS) instantiation now reads `ξ = y`, (b) the Step-3 ball radius is now
  -- `R`, and (c) the \noderef hygiene needed nothing.
  have h2e : (0:ℝ) < 2 * ε := by linarith
  -- ============ Step 1: separability, one application of the separability node ============
  refine ⟨fun Z => SupConvolutionSeparable N ε C hε G hGb Z, ?_⟩
  -- ============ Step 2a: the two operators S ξ = ξ + ε Aeps ξ, T ξ = ξ - ε B ξ ============
  -- `hinv` says T (S ξ) = ξ; self-adjointness upgrades this to S (T x) = x.
  have hST : ∀ x : PiLp 2 (fun _ : Fin N => E),
      (x - ε • B x) + ε • Aeps (x - ε • B x) = x := by
    intro x
    have hzero : ∀ y : PiLp 2 (fun _ : Fin N => E),
        (inner ℝ (((x - ε • B x) + ε • Aeps (x - ε • B x)) - x) y : ℝ) = 0 := by
      intro y
      have e1 : (inner ℝ ((x - ε • B x) + ε • Aeps (x - ε • B x)) y : ℝ)
          = inner ℝ (x - ε • B x) (y + ε • Aeps y) := by
        rw [inner_add_left, real_inner_smul_left, hAs (x - ε • B x) y,
          inner_add_right, real_inner_smul_right]
      have e2 : (inner ℝ (x - ε • B x) (y + ε • Aeps y) : ℝ)
          = inner ℝ x ((y + ε • Aeps y) - ε • B (y + ε • Aeps y)) := by
        rw [inner_sub_left, real_inner_smul_left, hB x (y + ε • Aeps y),
          inner_sub_right, real_inner_smul_right]
      rw [inner_sub_left, e1, e2, hinv y]
      ring
    have hz := hzero (((x - ε • B x) + ε • Aeps (x - ε • B x)) - x)
    rw [real_inner_self_eq_norm_sq] at hz
    have hn : ‖((x - ε • B x) + ε • Aeps (x - ε • B x)) - x‖ = 0 := by
      nlinarith [norm_nonneg (((x - ε • B x) + ε • Aeps (x - ε • B x)) - x)]
    have hn0 := norm_eq_zero.mp hn
    linear_combination (norm := module) hn0
  -- the consequence used twice: Aeps (T x) = B x
  have hAT : ∀ x : PiLp 2 (fun _ : Fin N => E), Aeps (x - ε • B x) = B x := by
    intro x
    rw [hres (x - ε • B x), hST x]
  -- ============ Step 2b/2c: the exact expansion of F(·, W) about Z_W = T W ============
  -- F(Z,W) - F(Z_W,W) is exactly minus the positive quadratic form at h = Z - T W, and
  -- F(Z_W,W) = Φ(W) = 𝒢(W) - ⟪B W, W⟫/2.  One identity carries all of Step 2.
  have hkey : ∀ Z W : PiLp 2 (fun _ : Fin N => E),
      ((∑ j, G j (ofLp W j)) - ‖Z - W‖ ^ 2 / (2 * ε)) - (inner ℝ (Aeps Z) Z : ℝ) / 2
        = ((∑ j, G j (ofLp W j)) - (inner ℝ (B W) W : ℝ) / 2)
          - ((inner ℝ (Z - (W - ε • B W)) (Z - (W - ε • B W)) : ℝ) / ε
             + (inner ℝ (Aeps (Z - (W - ε • B W))) (Z - (W - ε • B W)) : ℝ)) / 2 := by
    intro Z W
    obtain ⟨h, hhd⟩ : ∃ h : PiLp 2 (fun _ : Fin N => E), h = Z - (W - ε • B W) := ⟨_, rfl⟩
    have hZW : Z - W = h - ε • B W := by rw [hhd]; abel
    have hZ : Z = (W - ε • B W) + h := by rw [hhd]; abel
    have hn : ‖Z - W‖ ^ 2
        = (inner ℝ h h : ℝ) - 2 * ε * (inner ℝ (B W) h : ℝ)
          + ε ^ 2 * (inner ℝ (B W) (B W) : ℝ) := by
      rw [← real_inner_self_eq_norm_sq, hZW]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm h (B W)]
      ring
    have hcross : (inner ℝ (Aeps h) (W - ε • B W) : ℝ) = inner ℝ (B W) h := by
      rw [hAs h (W - ε • B W), hAT W, real_inner_comm]
    have hAexp : (inner ℝ (Aeps Z) Z : ℝ)
        = (inner ℝ (B W) W : ℝ) - ε * (inner ℝ (B W) (B W) : ℝ)
          + 2 * (inner ℝ (B W) h : ℝ) + (inner ℝ (Aeps h) h : ℝ) := by
      rw [hZ, map_add]
      simp only [inner_add_left, inner_add_right]
      rw [hAT W, hcross]
      simp only [inner_sub_right, real_inner_smul_right]
      ring
    rw [hn, hAexp, ← hhd]
    field_simp
    ring
  -- the quadratic form is nonnegative, and strictly positive off `0` by `hpos`
  have hQnn : ∀ h : PiLp 2 (fun _ : Fin N => E),
      0 ≤ ((inner ℝ h h : ℝ) / ε + (inner ℝ (Aeps h) h : ℝ)) / 2 := by
    intro h
    rcases eq_or_ne h 0 with h0 | h0
    · rw [h0]; simp
    · linarith [hpos h h0]
  -- ============ Step 3, first half: Φ ≤ 0 everywhere, Φ 0 = 0, Φ < 0 off 0 ============
  have hPhi0 : (∑ j, G j (ofLp (0 : PiLp 2 (fun _ : Fin N => E)) j))
      - (inner ℝ (B 0) (0 : PiLp 2 (fun _ : Fin N => E)) : ℝ) / 2 = 0 := by
    simp [hG0]
  have hPhineg : ∀ W : PiLp 2 (fun _ : Fin N => E), W ≠ 0 →
      (∑ j, G j (ofLp W j)) - (inner ℝ (B W) W : ℝ) / 2 < 0 := by
    intro W hW
    have hex : ∃ j, ofLp W j ≠ 0 := by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hW (by ext j; simpa using hc j)
    obtain ⟨j₀, hj₀⟩ := hex
    -- name the summand: `Finset.single_le_sum` leaves `?f j₀ ≤ ∑ ?f` otherwise
    have hsingle : ‖ofLp W j₀‖ ^ 4 ≤ ∑ j, ‖ofLp W j‖ ^ 4 :=
      Finset.single_le_sum (f := fun j : Fin N => ‖ofLp W j‖ ^ 4)
        (fun j _ => by positivity) (Finset.mem_univ j₀)
    have hjpos : 0 < ‖ofLp W j₀‖ ^ 4 := by
      have h1 : 0 < ‖ofLp W j₀‖ := norm_pos_iff.mpr hj₀
      positivity
    linarith [hG3 W hW]
  have hPhile : ∀ W : PiLp 2 (fun _ : Fin N => E),
      (∑ j, G j (ofLp W j)) - (inner ℝ (B W) W : ℝ) / 2 ≤ 0 := by
    intro W
    rcases eq_or_ne W 0 with h0 | h0
    · rw [h0]; exact le_of_eq hPhi0
    · exact (hPhineg W h0).le
  -- ============ the growth bound and the three parts of SupConvolutionSemiconvex ========
  have hbdN : ∀ W : PiLp 2 (fun _ : Fin N => E), (∑ j, G j (ofLp W j)) ≤ (N : ℝ) * C := by
    intro W
    have h1 : (∑ j, G j (ofLp W j)) ≤ ∑ _j : Fin N, C :=
      Finset.sum_le_sum (fun j _ => hGb j (ofLp W j))
    have h2 : (∑ _j : Fin N, C) = (N : ℝ) * C := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hgrow : ∀ W : PiLp 2 (fun _ : Fin N => E),
      (∑ j, G j (ofLp W j)) ≤ (N : ℝ) * C + ‖W‖ := by
    intro W; linarith [hbdN W, norm_nonneg W]
  have hSC := SupConvolutionSemiconvex ε ((N : ℝ) * C) hε
    (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) hgrow
  -- ============ Step 3, second half: the supremum in W is attained ============
  have hattain : ∀ Z : PiLp 2 (fun _ : Fin N => E),
      ∃ W : PiLp 2 (fun _ : Fin N => E),
        SupConvolution ε (fun W' : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W' j)) Z
          = (∑ j, G j (ofLp W j)) - ‖Z - W‖ ^ 2 / (2 * ε) := by
    intro Z
    obtain ⟨obj, hobjd⟩ : ∃ f : PiLp 2 (fun _ : Fin N => E) → ℝ,
        f = fun W : PiLp 2 (fun _ : Fin N => E) =>
          (∑ j, G j (ofLp W j)) - ‖Z - W‖ ^ 2 / (2 * ε) := ⟨_, rfl⟩
    have hobjc : Continuous obj := by
      rw [hobjd]
      refine Continuous.sub ?_ ?_
      · refine continuous_finsetSum _ (fun j _ => ?_)
        exact (hGc j).comp (PiLp.continuous_apply (p := 2) (fun _ : Fin N => E) j)
      · exact (((continuous_const.sub continuous_id).norm).pow 2).div_const _
    have hobjZ : obj Z = (∑ j, G j (ofLp Z j)) := by rw [hobjd]; simp
    have hApos : (0:ℝ) ≤ (N : ℝ) * C - (∑ j, G j (ofLp Z j)) := by linarith [hbdN Z]
    obtain ⟨R, hR0, hRsq⟩ : ∃ R : ℝ, 0 < R ∧
        2 * ε * ((N : ℝ) * C - (∑ j, G j (ofLp Z j))) + 1 ≤ R ^ 2 := by
      refine ⟨Real.sqrt (2 * ε * ((N : ℝ) * C - (∑ j, G j (ofLp Z j))) + 1), ?_, ?_⟩
      · exact Real.sqrt_pos.mpr (by nlinarith)
      · rw [Real.sq_sqrt (by nlinarith)]
    have hfar : ∀ W : PiLp 2 (fun _ : Fin N => E), R < ‖Z - W‖ → obj W < obj Z := by
      intro W hWfar
      have hsq : R ^ 2 < ‖Z - W‖ ^ 2 := by nlinarith [hR0, norm_nonneg (Z - W)]
      have hxA : (N : ℝ) * C - (∑ j, G j (ofLp Z j)) < ‖Z - W‖ ^ 2 / (2 * ε) := by
        have hx : 2 * ε * (‖Z - W‖ ^ 2 / (2 * ε)) = ‖Z - W‖ ^ 2 := by field_simp
        by_contra hcon
        rw [not_lt] at hcon
        have := mul_le_mul_of_nonneg_left hcon h2e.le
        linarith
      rw [hobjZ]
      simp only [hobjd]
      linarith [hbdN W]
    obtain ⟨W, hWmem, hWmax⟩ := (isCompact_closedBall Z R).exists_isMaxOn
      ⟨Z, Metric.mem_closedBall_self hR0.le⟩ hobjc.continuousOn
    have hall : ∀ W' : PiLp 2 (fun _ : Fin N => E), obj W' ≤ obj W := by
      intro W'
      rcases le_or_gt ‖Z - W'‖ R with hle | hlt
      · refine hWmax ?_
        simp only [Metric.mem_closedBall, dist_eq_norm]
        rw [← norm_neg, neg_sub]
        exact hle
      · have h1 := hfar W' hlt
        have h2 : obj Z ≤ obj W := hWmax (Metric.mem_closedBall_self hR0.le)
        linarith
    refine ⟨W, ?_⟩
    have hgreat : IsGreatest (Set.range obj) (obj W) :=
      ⟨⟨W, rfl⟩, fun y hy => by obtain ⟨W', rfl⟩ := hy; exact hall W'⟩
    have hsup : SupConvolution ε
        (fun W' : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W' j)) Z
        = sSup (Set.range obj) := by rw [hobjd]; rfl
    rw [hsup, hgreat.csSup_eq, hobjd]
  -- ============ Step 3, conclusion: Υ ≤ 0 everywhere, with equality only at 0 ============
  have hUneg : ∀ Z : PiLp 2 (fun _ : Fin N => E), Z ≠ 0 →
      SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
        - (inner ℝ (Aeps Z) Z : ℝ) / 2 < 0 := by
    intro Z hZ
    obtain ⟨W, hW⟩ := hattain Z
    rw [hW, hkey Z W]
    rcases eq_or_ne W 0 with hW0 | hW0
    · -- the maximizer is the origin: the defect is the form at `Z` itself, strictly positive
      subst hW0
      have hT0 : (0 : PiLp 2 (fun _ : Fin N => E)) - ε • B 0 = 0 := by simp
      rw [hT0, sub_zero, hPhi0]
      linarith [hpos Z hZ]
    · -- the maximizer is off the origin: Φ is already strictly negative there
      linarith [hPhineg W hW0, hQnn (Z - (W - ε • B W))]
  have hU0 : SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j))
      (0 : PiLp 2 (fun _ : Fin N => E)) - (inner ℝ (Aeps 0) (0 : PiLp 2 (fun _ : Fin N => E)) : ℝ) / 2
      = 0 := by
    have hle : SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j))
        (0 : PiLp 2 (fun _ : Fin N => E)) ≤ 0 := by
      obtain ⟨W, hW⟩ := hattain (0 : PiLp 2 (fun _ : Fin N => E))
      have hid := hkey (0 : PiLp 2 (fun _ : Fin N => E)) W
      simp only [map_zero, inner_zero_left, zero_div] at hid
      rw [hW]
      linarith [hPhile W, hQnn ((0 : PiLp 2 (fun _ : Fin N => E)) - (W - ε • B W))]
    have hge : (0:ℝ) ≤ SupConvolution ε
        (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j))
        (0 : PiLp 2 (fun _ : Fin N => E)) := by
      have h1 := hSC.2.1 (0 : PiLp 2 (fun _ : Fin N => E))
      simpa [hG0] using h1
    simp only [map_zero, inner_zero_left, zero_div]
    linarith
  -- ============ Step 4: Υ is λ-semiconvex, hence continuous ============
  have hsym : ∀ u v : PiLp 2 (fun _ : Fin N => E),
      (inner ℝ (Aeps u) v : ℝ) = inner ℝ (Aeps v) u := by
    intro u v; rw [hAs u v, real_inner_comm]
  have hconvA : ConvexOn ℝ (Set.univ : Set (PiLp 2 (fun _ : Fin N => E)))
      (fun Z => -(inner ℝ (Aeps Z) Z : ℝ) / 2 + ‖Aeps‖ * ‖Z‖ ^ 2 / 2) := by
    have hQb : ∀ u : PiLp 2 (fun _ : Fin N => E),
        (inner ℝ (Aeps u) u : ℝ) ≤ ‖Aeps‖ * ‖u‖ ^ 2 := by
      intro u
      have h1 : (inner ℝ (Aeps u) u : ℝ) ≤ ‖Aeps u‖ * ‖u‖ := real_inner_le_norm _ _
      have h2 : ‖Aeps u‖ ≤ ‖Aeps‖ * ‖u‖ := Aeps.le_opNorm u
      nlinarith [norm_nonneg u, norm_nonneg (Aeps u)]
    have eA : ∀ (u v : PiLp 2 (fun _ : Fin N => E)) (s t : ℝ),
        (inner ℝ (Aeps (s • u + t • v)) (s • u + t • v) : ℝ)
          = s ^ 2 * (inner ℝ (Aeps u) u : ℝ) + 2 * s * t * (inner ℝ (Aeps u) v : ℝ)
            + t ^ 2 * (inner ℝ (Aeps v) v : ℝ) := by
      intro u v s t
      simp only [map_add, map_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [hsym v u]
      ring
    have eN : ∀ (u v : PiLp 2 (fun _ : Fin N => E)) (s t : ℝ),
        ‖s • u + t • v‖ ^ 2
          = s ^ 2 * ‖u‖ ^ 2 + 2 * s * t * (inner ℝ u v : ℝ) + t ^ 2 * ‖v‖ ^ 2 := by
      intro u v s t
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm v u, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hsubeq : ((1:ℝ) • x + (-1:ℝ) • y) = x - y := by module
    have eAd := eA x y 1 (-1)
    rw [hsubeq] at eAd
    have eNd := eN x y 1 (-1)
    rw [hsubeq] at eNd
    have hnn := hQb (x - y)
    rw [eAd, eNd] at hnn
    have hstuff : 0 ≤ ‖Aeps‖ * ((1:ℝ) ^ 2 * ‖x‖ ^ 2 + 2 * 1 * (-1) * (inner ℝ x y : ℝ)
          + (-1 : ℝ) ^ 2 * ‖y‖ ^ 2)
        - ((1:ℝ) ^ 2 * (inner ℝ (Aeps x) x : ℝ) + 2 * 1 * (-1) * (inner ℝ (Aeps x) y : ℝ)
          + (-1 : ℝ) ^ 2 * (inner ℝ (Aeps y) y : ℝ)) := by linarith
    have hprod := mul_nonneg (mul_nonneg ha hb) hstuff
    have ha2 : a ^ 2 = a - a * b := by nlinarith
    have hb2 : b ^ 2 = b - a * b := by nlinarith
    simp only [smul_eq_mul]
    rw [eA x y a b, eN x y a b, ha2, hb2]
    linarith [hprod]
  have hconv1 : ConvexOn ℝ (Set.univ : Set (PiLp 2 (fun _ : Fin N => E)))
      (fun z => SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) z
        + 1 / ε * ‖z‖ ^ 2 / 2) := hSC.2.2
  have hconvS : ConvexOn ℝ (Set.univ : Set (PiLp 2 (fun _ : Fin N => E)))
      (fun z => (SupConvolution ε
          (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) z
          - (inner ℝ (Aeps z) z : ℝ) / 2) + (1 / ε + ‖Aeps‖) * ‖z‖ ^ 2 / 2) := by
    have hsum := hconv1.add hconvA
    have heq : (fun z : PiLp 2 (fun _ : Fin N => E) =>
          (SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) z
            - (inner ℝ (Aeps z) z : ℝ) / 2) + (1 / ε + ‖Aeps‖) * ‖z‖ ^ 2 / 2)
        = fun z : PiLp 2 (fun _ : Fin N => E) =>
          (SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) z
            + 1 / ε * ‖z‖ ^ 2 / 2)
          + (-(inner ℝ (Aeps z) z : ℝ) / 2 + ‖Aeps‖ * ‖z‖ ^ 2 / 2) := by
      funext z; ring
    rw [heq]
    exact hsum
  refine ⟨fun Z => SupConvolution ε
      (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
      - (inner ℝ (Aeps Z) Z : ℝ) / 2, fun Z => rfl, hU0, hUneg, hconvS, ?_⟩
  -- continuity: Υ + λ‖·‖²/2 is a finite convex function on the open set V, hence continuous
  have hcont := hconvS.continuousOn isOpen_univ
  rw [continuousOn_univ] at hcont
  have hfin : (fun Z : PiLp 2 (fun _ : Fin N => E) =>
      SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
        - (inner ℝ (Aeps Z) Z : ℝ) / 2)
      = fun Z : PiLp 2 (fun _ : Fin N => E) =>
        ((SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
          - (inner ℝ (Aeps Z) Z : ℝ) / 2) + (1 / ε + ‖Aeps‖) * ‖Z‖ ^ 2 / 2)
        - (1 / ε + ‖Aeps‖) * ‖Z‖ ^ 2 / 2 := by
    funext Z; ring
  rw [hfin]
  exact hcont.sub ((continuous_norm.pow 2).const_mul _ |>.div_const _)
