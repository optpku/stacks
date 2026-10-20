module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.BrillNoether
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Gonality
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Hyperelliptic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Trigonal

/-!
# Linear series on genus-seven curves

Partial existence, base-point-freeness, and closed-embedding criteria for
genus-seven curves and selected curve strata.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.LinearSeries
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve.GenusSeven

/-- A degree-`d`, dimension-`r` linear series exists on some smooth projective
geometrically irreducible genus-seven curve over an algebraically closed field. -/
def existsLinearSeries (k : Type u) [Field k] [IsAlgClosed k] (d r : ℕ) : Prop :=
  ∃ (X : SchemeOverField k) (hCurve : Curve X) (hProj : Projective X.hom)
    (hSmooth : Smooth X.hom) (hGI : GeometricallyIrreducible X.hom),
    @genus k _ X hCurve hProj hSmooth hGI = 7 ∧
      Nonempty
        (@LinearSeries k _ X (Projective.isProper hProj)
          hCurve.topologicalKrullDim_eq_one.le d r)

/-- A base-point-free degree-`d`, dimension-`r` linear series exists on some
smooth projective geometrically irreducible genus-seven curve. -/
def existsBasePointFreeLinearSeries
    (k : Type u) [Field k] [IsAlgClosed k] (d r : ℕ) : Prop :=
  ∃ (X : SchemeOverField k) (hCurve : Curve X) (hProj : Projective X.hom)
    (hSmooth : Smooth X.hom) (hGI : GeometricallyIrreducible X.hom)
    (g : @LinearSeries k _ X (Projective.isProper hProj)
      hCurve.topologicalKrullDim_eq_one.le d r),
    @genus k _ X hCurve hProj hSmooth hGI = 7 ∧
      @IsBasePointFree k _ X (Projective.isProper hProj)
        hCurve.topologicalKrullDim_eq_one.le d r g

/-- A degree-`d`, dimension-`r` linear series inducing a closed embedding exists
on some smooth projective geometrically irreducible genus-seven curve. -/
def existsClosedEmbeddingLinearSeries
    (k : Type u) [Field k] [IsAlgClosed k] (d r : ℕ) : Prop :=
  ∃ (X : SchemeOverField k) (hCurve : Curve X) (hProj : Projective X.hom)
    (hSmooth : Smooth X.hom) (hGI : GeometricallyIrreducible X.hom)
    (g : @LinearSeries k _ X (Projective.isProper hProj)
      hCurve.topologicalKrullDim_eq_one.le d r),
    @genus k _ X hCurve hProj hSmooth hGI = 7 ∧
      @InducesClosedEmbedding k _ X (Projective.isProper hProj)
        hCurve.topologicalKrullDim_eq_one.le d r g

/-- Existence on some genus-seven curve is characterized by the Clifford or
Riemann–Roch numerical bound. -/
theorem existsLinearSeries_iff {k : Type u} [Field k] [IsAlgClosed k]
    (d r : ℕ) :
    existsLinearSeries k d r ↔ 2 * r ≤ d ∨ r + 7 ≤ d := sorry

/-- A genus-seven base-point-free series is trivial or has positive dimension and
satisfies the Clifford–Riemann–Roch bound. -/
theorem existsBasePointFreeLinearSeries_bound
    {k : Type u} [Field k] [IsAlgClosed k] (d r : ℕ) :
    existsBasePointFreeLinearSeries k d r →
      (r = 0 ∧ d = 0) ∨ (1 ≤ r ∧ (2 * r ≤ d ∨ r + 7 ≤ d)) := sorry

/-- The degree-zero, dimension-zero base-point-free series exists on a genus-seven curve. -/
theorem existsBasePointFreeLinearSeries_trivial
    {k : Type u} [Field k] [IsAlgClosed k] :
    existsBasePointFreeLinearSeries k 0 0 := sorry

/-- A pure hyperelliptic multiple gives a base-point-free genus-seven series for
`1 ≤ r ≤ 6` and degree `2 * r`. -/
theorem existsBasePointFreeLinearSeries_hyperelliptic
    {k : Type u} [Field k] [IsAlgClosed k] {d r : ℕ} (hr : 1 ≤ r) (hr' : r ≤ 6)
    (hd : d = 2 * r) :
    existsBasePointFreeLinearSeries k d r := sorry

/-- A nonspecial series of degree at least `14` gives a base-point-free genus-seven series. -/
theorem existsBasePointFreeLinearSeries_nonspecial
    {k : Type u} [Field k] [IsAlgClosed k] {d r : ℕ} (hd : 14 ≤ d)
    (hr : r + 7 = d) :
    existsBasePointFreeLinearSeries k d r := sorry

/-- A canonical or sufficiently large-degree nonspecial series gives a closed-embedding
genus-seven series. -/
theorem existsClosedEmbeddingLinearSeries_of
    {k : Type u} [Field k] [IsAlgClosed k] (d r : ℕ)
    (h : (r = 6 ∧ d = 12) ∨ (r + 7 = d ∧ 15 ≤ d)) :
    existsClosedEmbeddingLinearSeries k d r := sorry

/-- On a Brill–Noether-general genus-seven curve, linear-series existence is
equivalent to nonnegativity of `ρ(7, r, d)`. -/
theorem linearSeries_iff_of_isBrillNoetherGeneral
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hG : IsBrillNoetherGeneral X) (hgenus : genus X = 7) (d r : ℕ) :
    Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r) ↔
      0 ≤ brillNoetherNumber 7 r d := sorry

/-- A complete Brill–Noether-general genus-seven series is base-point-free under
the degree-zero or negative predecessor Brill–Noether condition. -/
theorem isBasePointFree_of_isBrillNoetherGeneral
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hG : IsBrillNoetherGeneral X) (hgenus : genus X = 7)
    {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r)
    (hC : IsComplete g)
    (h : d = 0 ∨ (0 < d ∧ brillNoetherNumber 7 r (d - 1) < 0)) :
    IsBasePointFree g := sorry

/-- A complete canonical or sufficiently large-degree Brill–Noether-general
genus-seven series induces a closed embedding. -/
theorem inducesClosedEmbedding_of_isBrillNoetherGeneral
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hG : IsBrillNoetherGeneral X) (hgenus : genus X = 7)
    {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r)
    (hC : IsComplete g) (h : (r = 6 ∧ d = 12) ∨ 15 ≤ d) :
    InducesClosedEmbedding g := sorry

/-- On a hyperelliptic genus-seven curve, linear-series existence satisfies the
Clifford or Riemann–Roch numerical bound. -/
theorem linearSeries_iff_of_isHyperelliptic
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hH : IsHyperelliptic X) (hgenus : genus X = 7) (d r : ℕ) :
    Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r) ↔
      2 * r ≤ d ∨ r + 7 ≤ d := sorry

/-- A complete hyperelliptic genus-seven series is base-point-free in the stated
pure-hyperelliptic and high-degree ranges. -/
theorem isBasePointFree_of_isHyperelliptic
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hH : IsHyperelliptic X) (hgenus : genus X = 7)
    {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r)
    (hC : IsComplete g) (h : (1 ≤ r ∧ r ≤ 6 ∧ 2 * r = d) ∨ 14 ≤ d) :
    IsBasePointFree g := sorry

/-- A complete hyperelliptic genus-seven series of degree at least `15` induces
a closed embedding. -/
theorem inducesClosedEmbedding_of_isHyperelliptic
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hH : IsHyperelliptic X) (hgenus : genus X = 7)
    {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r)
    (hC : IsComplete g) (hd : 15 ≤ d) :
    InducesClosedEmbedding g := sorry

/-- A trigonal non-hyperelliptic genus-seven curve has a trigonal pencil and all
its series satisfy the Clifford–Riemann–Roch necessary bound. -/
theorem linearSeries_of_isTrigonal
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hT : IsTrigonal X) (hH : ¬IsHyperelliptic X) (hgenus : genus X = 7) :
    Nonempty (LinearSeries X topologicalKrullDim_eq_one.le 3 1) ∧
      ∀ d r : ℕ, Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r) →
        2 * r ≤ d ∨ r + 7 ≤ d := sorry

/-- The stated numerical bound is sufficient for a linear series on a trigonal
non-hyperelliptic genus-seven curve. -/
theorem nonempty_linearSeries_of_isTrigonal
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hT : IsTrigonal X) (hH : ¬IsHyperelliptic X) (hgenus : genus X = 7)
    (d r : ℕ) (h : 3 * r ≤ d ∨ r + 7 ≤ d) :
    Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r) := sorry

/-- A complete trigonal non-hyperelliptic genus-seven series is base-point-free
in the trigonal-pencil and high-degree ranges. -/
theorem isBasePointFree_of_isTrigonal
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hT : IsTrigonal X) (hH : ¬IsHyperelliptic X) (hgenus : genus X = 7)
    {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r)
    (hC : IsComplete g) (h : (d = 3 ∧ r = 1) ∨ 14 ≤ d) :
    IsBasePointFree g := sorry

/-- A complete canonical or sufficiently large-degree series on a trigonal
non-hyperelliptic genus-seven curve induces a closed embedding. -/
theorem inducesClosedEmbedding_of_isTrigonal
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (hT : IsTrigonal X) (hH : ¬IsHyperelliptic X) (hgenus : genus X = 7)
    {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r)
    (hC : IsComplete g) (h : (r = 6 ∧ d = 12) ∨ 15 ≤ d) :
    InducesClosedEmbedding g := sorry

end AlgebraicGeometry.Curve.GenusSeven
