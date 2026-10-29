import InfHarmonic.ClosedSuperjet
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Part I(B) of the theorem of sums: subtracting the quartic `‖·‖⁴`, whose
gradient and second derivative both vanish at `0`, does not change the closed
superjet at `0`. -/
theorem ClosedSuperjetQuartic (f : E → ℝ) :
    ClosedSuperjet (fun w : E => f w - ‖w‖ ^ 4) 0 = ClosedSuperjet f 0 := by
  -- NO TAYLOR THEOREM IS NEEDED HERE, and that is the point worth recording.  Expanding
  -- ‖z+h‖⁴ = (‖z‖² + 2⟪z,h⟫ + ‖h‖²)² is EXACT algebra, and it already separates the gradient
  -- and Hessian of `s = ‖·‖⁴` at `z` from a remainder that is visibly O(‖h‖³):
  --   ‖z+h‖⁴ - ‖z‖⁴ = ⟪q z, h⟫ + Y z h h / 2 + (4⟪z,h⟫‖h‖² + ‖h‖⁴),
  --   q z = (4‖z‖²) • z,   Y z (a,b) = 4‖z‖²⟪a,b⟫ + 8⟪z,a⟫⟪z,b⟫.
  -- So the Peano step is `hexp` below plus one triangle inequality, and the vanishing of the
  -- shift at the limit is the norm bounds ‖q z‖ ≤ 4‖z‖³ and ‖Y z‖ ≤ 12‖z‖².
  have _ : FiniteDimensional ℝ E := inferInstance
  have hiSL : ∀ u v : E, (innerSL ℝ u) v = (inner ℝ u v : ℝ) := fun _ _ => rfl
  obtain ⟨G, hGapp⟩ : ∃ G : E →L[ℝ] E →L[ℝ] ℝ, ∀ a b : E, G a b = (inner ℝ a b : ℝ) :=
    ⟨innerSL ℝ, fun _ _ => rfl⟩
  -- (1) THE HESSIAN FIELD AND ITS NORM BOUND
  obtain ⟨Y, hYapp⟩ : ∃ Y : E → (E →L[ℝ] E →L[ℝ] ℝ),
      ∀ z a b : E, Y z a b = 4 * ‖z‖ ^ 2 * inner ℝ a b + 8 * (inner ℝ z a * inner ℝ z b) := by
    refine ⟨fun z => (4 * ‖z‖ ^ 2) • G + (8 : ℝ) • ((innerSL ℝ z).smulRight (innerSL ℝ z)),
      fun z a b => ?_⟩
    simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
      hiSL, hGapp]
  have hYsym : ∀ z a b : E, Y z a b = Y z b a := by
    intro z a b
    rw [hYapp, hYapp, real_inner_comm a b]
    ring
  have hYnorm : ∀ z : E, ‖Y z‖ ≤ 12 * ‖z‖ ^ 2 := by
    intro z
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun a => ?_)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun b => ?_)
    rw [Real.norm_eq_abs, hYapp]
    have c1 : |(inner ℝ a b : ℝ)| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
    have c2 : |(inner ℝ z a : ℝ)| ≤ ‖z‖ * ‖a‖ := abs_real_inner_le_norm z a
    have c3 : |(inner ℝ z b : ℝ)| ≤ ‖z‖ * ‖b‖ := abs_real_inner_le_norm z b
    have hq : |4 * ‖z‖ ^ 2 * (inner ℝ a b : ℝ)| ≤ 4 * ‖z‖ ^ 2 * (‖a‖ * ‖b‖) := by
      rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 4 * ‖z‖ ^ 2 by positivity)]
      exact mul_le_mul_of_nonneg_left c1 (by positivity)
    have hp : |8 * ((inner ℝ z a : ℝ) * inner ℝ z b)| ≤ 8 * ((‖z‖ * ‖a‖) * (‖z‖ * ‖b‖)) := by
      rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (8:ℝ) by norm_num), abs_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul c2 c3 (abs_nonneg _) (by positivity)) (by norm_num)
    have htri := abs_add_le (4 * ‖z‖ ^ 2 * (inner ℝ a b : ℝ))
      (8 * ((inner ℝ z a : ℝ) * inner ℝ z b))
    nlinarith [htri, hq, hp]
  -- (2) THE GRADIENT FIELD AND ITS NORM BOUND
  obtain ⟨qq, hqdef⟩ : ∃ qq : E → E, qq = fun z : E => (4 * ‖z‖ ^ 2) • z := ⟨_, rfl⟩
  have hqapp : ∀ z h : E, (inner ℝ (qq z) h : ℝ) = 4 * ‖z‖ ^ 2 * inner ℝ z h := by
    intro z h
    rw [hqdef]
    exact real_inner_smul_left z h (4 * ‖z‖ ^ 2)
  have hqnorm : ∀ z : E, ‖qq z‖ = 4 * ‖z‖ ^ 3 := by
    intro z
    rw [hqdef]
    show ‖(4 * ‖z‖ ^ 2) • z‖ = 4 * ‖z‖ ^ 3
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ 4 * ‖z‖ ^ 2 by positivity)]
    ring
  -- (3) THE EXACT EXPANSION
  have hexp : ∀ z h : E, ‖z + h‖ ^ 4
      = ‖z‖ ^ 4 + inner ℝ (qq z) h + Y z h h / 2
        + (4 * inner ℝ z h * ‖h‖ ^ 2 + ‖h‖ ^ 4) := by
    intro z h
    rw [hqapp, hYapp, real_inner_self_eq_norm_sq h]
    have h1 : ‖z + h‖ ^ 2 = ‖z‖ ^ 2 + 2 * inner ℝ z h + ‖h‖ ^ 2 := by
      rw [norm_add_sq_real]
    have h2 : ‖z + h‖ ^ 4 = (‖z + h‖ ^ 2) ^ 2 := by ring
    rw [h2, h1]
    ring
  -- (4) THE REMAINDER IS o(‖h‖²), UNIFORMLY FOR EACH FIXED z
  have hrem : ∀ (z : E) (ε : ℝ), 0 < ε → ∃ δ > 0, ∀ h : E, ‖h‖ < δ →
      |4 * (inner ℝ z h : ℝ) * ‖h‖ ^ 2 + ‖h‖ ^ 4| ≤ ε * ‖h‖ ^ 2 := by
    intro z ε hε
    refine ⟨min 1 (ε / (4 * ‖z‖ + 1)), lt_min one_pos (by positivity), fun h hh => ?_⟩
    have hh1 : ‖h‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hh (min_le_left _ _))
    have hh2 : ‖h‖ ≤ ε / (4 * ‖z‖ + 1) := le_of_lt (lt_of_lt_of_le hh (min_le_right _ _))
    have hd : (0:ℝ) < 4 * ‖z‖ + 1 := by positivity
    rw [le_div_iff₀ hd] at hh2
    have hzh : |(inner ℝ z h : ℝ)| ≤ ‖z‖ * ‖h‖ := abs_real_inner_le_norm z h
    have hn := norm_nonneg h
    have hzn := norm_nonneg z
    have hb : |4 * (inner ℝ z h : ℝ) * ‖h‖ ^ 2 + ‖h‖ ^ 4|
        ≤ 4 * |(inner ℝ z h : ℝ)| * ‖h‖ ^ 2 + ‖h‖ ^ 4 := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (4:ℝ) by norm_num),
        abs_of_nonneg (show (0:ℝ) ≤ ‖h‖ ^ 2 by positivity),
        abs_of_nonneg (show (0:ℝ) ≤ ‖h‖ ^ 4 by positivity)]
    have hsq : ‖h‖ ^ 2 ≤ ‖h‖ := by nlinarith [hn, hh1]
    have hfac : 4 * ‖z‖ * ‖h‖ + ‖h‖ ^ 2 ≤ ε := by linarith [hsq, hh2]
    have hstep : 4 * |(inner ℝ z h : ℝ)| * ‖h‖ ^ 2 + ‖h‖ ^ 4
        ≤ (4 * ‖z‖ * ‖h‖ + ‖h‖ ^ 2) * ‖h‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hzh (show (0:ℝ) ≤ ‖h‖ ^ 2 by positivity)]
    have hfin : (4 * ‖z‖ * ‖h‖ + ‖h‖ ^ 2) * ‖h‖ ^ 2 ≤ ε * ‖h‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hfac (by positivity)
    linarith [hb, hstep, hfin]
  -- (5) THE SUPERJET SHIFT, at an arbitrary base point
  have key : ∀ (z p : E) (X : E →L[ℝ] E →L[ℝ] ℝ),
      (p, X) ∈ Superjet (fun w : E => f w - ‖w‖ ^ 4) z ↔
        (p + qq z, X + Y z) ∈ Superjet f z := by
    intro z p X
    have hXY : ∀ a b : E, (X + Y z) a b = X a b + Y z a b := by
      intro a b
      simp only [add_apply]
    constructor
    · rintro ⟨hsym, hineq⟩
      refine ⟨fun a b => by rw [hXY, hXY, hsym a b, hYsym z a b], fun ε hε => ?_⟩
      obtain ⟨δ₁, hδ₁, hball⟩ := hineq (ε / 2) (by positivity)
      obtain ⟨δ₂, hδ₂, hr⟩ := hrem z (ε / 2) (by positivity)
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun h hh => ?_⟩
      have hb : f (z + h) - ‖z + h‖ ^ 4
          ≤ (f z - ‖z‖ ^ 4) + inner ℝ p h + X h h / 2 + ε / 2 * ‖h‖ ^ 2 :=
        hball h (lt_of_lt_of_le hh (min_le_left _ _))
      have hrb := hr h (lt_of_lt_of_le hh (min_le_right _ _))
      have habs := abs_le.mp hrb
      show f (z + h) ≤ f z + inner ℝ (p + qq z) h + (X + Y z) h h / 2 + ε * ‖h‖ ^ 2
      rw [hXY, inner_add_left]
      have he := hexp z h
      linarith [habs.1, habs.2]
    · rintro ⟨hsym, hineq⟩
      refine ⟨fun a b => by
        have h1 := hsym a b
        rw [hXY, hXY] at h1
        have h2 := hYsym z a b
        linarith, fun ε hε => ?_⟩
      obtain ⟨δ₁, hδ₁, hball⟩ := hineq (ε / 2) (by positivity)
      obtain ⟨δ₂, hδ₂, hr⟩ := hrem z (ε / 2) (by positivity)
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun h hh => ?_⟩
      have hb : f (z + h) ≤ f z + inner ℝ (p + qq z) h + (X + Y z) h h / 2 + ε / 2 * ‖h‖ ^ 2 :=
        hball h (lt_of_lt_of_le hh (min_le_left _ _))
      rw [hXY, inner_add_left] at hb
      have hrb := hr h (lt_of_lt_of_le hh (min_le_right _ _))
      have habs := abs_le.mp hrb
      show f (z + h) - ‖z + h‖ ^ 4
          ≤ (f z - ‖z‖ ^ 4) + inner ℝ p h + X h h / 2 + ε * ‖h‖ ^ 2
      have he := hexp z h
      linarith [habs.1, habs.2]
  -- (6) PASSING TO CLOSED SUPERJETS
  have hq0 : qq 0 = (0 : E) := by rw [hqdef]; simp
  have hY0 : Y (0 : E) = 0 := by
    refine ContinuousLinearMap.ext (fun a => ContinuousLinearMap.ext (fun b => ?_))
    rw [hYapp]
    simp
  have hqlim : ∀ zs : ℕ → E, Filter.Tendsto zs Filter.atTop (nhds 0) →
      Filter.Tendsto (fun k => qq (zs k)) Filter.atTop (nhds 0) := by
    intro zs hzs
    refine squeeze_zero_norm (f := fun k => qq (zs k))
      (a := fun k => 4 * ‖zs k‖ ^ 3) (fun k => ?_) ?_
    · exact le_of_eq (hqnorm (zs k))
    · have hc : Filter.Tendsto (fun k => 4 * ‖zs k‖ ^ 3) Filter.atTop (nhds (4 * ‖(0:E)‖ ^ 3)) :=
        ((continuous_const.mul (continuous_norm.pow 3)).tendsto (0:E)).comp hzs
      rw [norm_zero] at hc
      simpa using hc
  have hYlim : ∀ zs : ℕ → E, Filter.Tendsto zs Filter.atTop (nhds 0) →
      Filter.Tendsto (fun k => Y (zs k)) Filter.atTop (nhds 0) := by
    intro zs hzs
    refine squeeze_zero_norm (f := fun k => Y (zs k))
      (a := fun k => 12 * ‖zs k‖ ^ 2) (fun k => hYnorm (zs k)) ?_
    have hc : Filter.Tendsto (fun k => 12 * ‖zs k‖ ^ 2) Filter.atTop (nhds (12 * ‖(0:E)‖ ^ 2)) :=
      ((continuous_const.mul (continuous_norm.pow 2)).tendsto (0:E)).comp hzs
    rw [norm_zero] at hc
    simpa using hc
  -- `ContinuousAdd`/`ContinuousSub` on the space of bilinear forms do not resolve directly from
  -- this node's imports, but `IsTopologicalAddGroup` does, and its projections supply them.  With
  -- these two in the local context `Tendsto.add` and `Tendsto.sub` work on the CLM space.
  have htag : IsTopologicalAddGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  have hca : ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ) := htag.toContinuousAdd
  have hcn : ContinuousNeg (E →L[ℝ] E →L[ℝ] ℝ) := htag.toContinuousNeg
  have hs0 : ((fun w : E => f w - ‖w‖ ^ 4) 0) = f 0 := by simp
  apply Set.eq_of_subset_of_subset
  · rintro ⟨p, X⟩ ⟨zs, ps, Xs, hjet, hz, hg, hp, hX⟩
    refine ⟨zs, fun k => ps k + qq (zs k), fun k => Xs k + Y (zs k), fun k => ?_, hz, ?_, ?_, ?_⟩
    · exact (key (zs k) (ps k) (Xs k)).mp (hjet k)
    · rw [hs0] at hg
      have heq : (fun k => f (zs k)) = fun k => (f (zs k) - ‖zs k‖ ^ 4) + ‖zs k‖ ^ 4 := by
        funext k; ring
      rw [heq]
      have hn : Filter.Tendsto (fun k => ‖zs k‖ ^ 4) Filter.atTop (nhds 0) := by
        have hc : Filter.Tendsto (fun k => ‖zs k‖ ^ 4) Filter.atTop (nhds (‖(0:E)‖ ^ 4)) :=
          ((continuous_norm.pow 4).tendsto (0:E)).comp hz
        rw [norm_zero] at hc
        simpa using hc
      have hfin := hg.add hn
      rw [add_zero] at hfin
      exact hfin
    · have hfin := hp.add (hqlim zs hz)
      rw [add_zero] at hfin
      exact hfin
    · have hfin := Filter.Tendsto.add (f := Xs) (g := fun k => Y (zs k)) hX (hYlim zs hz)
      rw [add_zero X] at hfin
      exact hfin
  · rintro ⟨p, X⟩ ⟨zs, ps, Xs, hjet, hz, hg, hp, hX⟩
    refine ⟨zs, fun k => ps k - qq (zs k), fun k => Xs k - Y (zs k), fun k => ?_, hz, ?_, ?_, ?_⟩
    · have h1 : ps k - qq (zs k) + qq (zs k) = ps k := by abel
      have h2 : Xs k - Y (zs k) + Y (zs k) = Xs k := by abel
      have h3 := key (zs k) (ps k - qq (zs k)) (Xs k - Y (zs k))
      rw [h1, h2] at h3
      exact h3.mpr (hjet k)
    · rw [hs0]
      have hn : Filter.Tendsto (fun k => ‖zs k‖ ^ 4) Filter.atTop (nhds 0) := by
        have hc : Filter.Tendsto (fun k => ‖zs k‖ ^ 4) Filter.atTop (nhds (‖(0:E)‖ ^ 4)) :=
          ((continuous_norm.pow 4).tendsto (0:E)).comp hz
        rw [norm_zero] at hc
        simpa using hc
      have hfin := hg.sub hn
      rw [sub_zero] at hfin
      exact hfin
    · have hfin := hp.sub (hqlim zs hz)
      rw [sub_zero] at hfin
      exact hfin
    · -- `ContinuousSub` is not derivable here either, so subtract by adding the negation
      have hneg : Filter.Tendsto (fun k => -(Y (zs k))) Filter.atTop (nhds 0) := by
        have h1 := Filter.Tendsto.neg (f := fun k => Y (zs k)) (hYlim zs hz)
        rw [show -(0 : E →L[ℝ] E →L[ℝ] ℝ) = 0 from by abel] at h1
        exact h1
      have hfin := Filter.Tendsto.add (f := Xs) (g := fun k => -(Y (zs k))) hX hneg
      rw [add_zero X] at hfin
      rw [show (fun k => Xs k + -(Y (zs k))) = fun k => Xs k - Y (zs k) from by
        funext k; abel] at hfin
      exact hfin
