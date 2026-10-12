/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.GenusSeven
import StacksCheckRecall

/-!
# Exercise 111.46.7

Partial criteria for linear series of degree `d` and dimension `r` on smooth
projective curves of genus `7`, including base-point-freeness and closed
embeddings on selected curve strata.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Curve
open AlgebraicGeometry.LinearSeries
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Exercise 111.46.7 (1): a linear series of degree `d` and dimension `r` exists
on some smooth projective curve of genus `7` if and only if it satisfies the
Clifford bound `2 * r ≤ d` or the Riemann–Roch bound `r + 7 ≤ d`. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.existsLinearSeries_iff :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (d r : ℕ),
      AlgebraicGeometry.Curve.GenusSeven.existsLinearSeries k d r ↔
        2 * r ≤ d ∨ r + 7 ≤ d)

/- Exercise 111.46.7 (2): a base-point-free linear series of degree `d` and
dimension `r` on some smooth projective curve of genus `7` is either the trivial
series or has positive dimension and satisfies the Clifford–Riemann–Roch
existence bound. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.existsBasePointFreeLinearSeries_bound :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (d r : ℕ),
      AlgebraicGeometry.Curve.GenusSeven.existsBasePointFreeLinearSeries k d r →
        (r = 0 ∧ d = 0) ∨ (1 ≤ r ∧ (2 * r ≤ d ∨ r + 7 ≤ d)))

/- Exercise 111.46.7 (3): a linear series of degree `d` and dimension `r`
induces a closed embedding into `ℙ^r` on some smooth projective curve of genus
`7` whenever it is a canonical series or a complete nonspecial series of degree
at least `15`. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.existsClosedEmbeddingLinearSeries_of :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (d r : ℕ),
      (r = 6 ∧ d = 12) ∨ (r + 7 = d ∧ 15 ≤ d) →
        AlgebraicGeometry.Curve.GenusSeven.existsClosedEmbeddingLinearSeries k d r)

/- Exercise 111.46.7 (4): on a Brill–Noether-general smooth projective curve of
genus `7`, a linear series of degree `d` and dimension `r` exists if and only if
the Brill–Noether number `ρ(7, r, d)` is nonnegative. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.linearSeries_iff_of_isBrillNoetherGeneral :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom],
      IsBrillNoetherGeneral X → genus X = 7 → ∀ (d r : ℕ),
        Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r) ↔
          0 ≤ brillNoetherNumber 7 r d)

/- Exercise 111.46.7 (5): a complete linear series on a Brill–Noether-general
genus-`7` curve is base-point-free if it has degree `0` or if there is no series
of the same dimension and degree `d - 1`. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.isBasePointFree_of_isBrillNoetherGeneral :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom],
      IsBrillNoetherGeneral X → genus X = 7 →
      ∀ {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r),
        IsComplete g → (d = 0 ∨ (0 < d ∧ brillNoetherNumber 7 r (d - 1) < 0)) →
          IsBasePointFree g)

/- Exercise 111.46.7 (6): a complete canonical series on a Brill–Noether-general
genus-`7` curve induces a closed embedding into `ℙ^6`, and every complete series
of degree at least `15` induces a closed embedding into `ℙ^r`. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.inducesClosedEmbedding_of_isBrillNoetherGeneral :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom],
      IsBrillNoetherGeneral X → genus X = 7 →
      ∀ {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r),
        IsComplete g → (r = 6 ∧ d = 12) ∨ 15 ≤ d → InducesClosedEmbedding g)

/- Exercise 111.46.7 (7): on a hyperelliptic smooth projective curve of genus
`7`, a linear series of degree `d` and dimension `r` exists if and only if it
satisfies the Clifford bound `2 * r ≤ d` or the Riemann–Roch bound `r + 7 ≤ d`. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.linearSeries_iff_of_isHyperelliptic :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom],
      IsHyperelliptic X → genus X = 7 → ∀ (d r : ℕ),
        Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r) ↔
          2 * r ≤ d ∨ r + 7 ≤ d)

/- Exercise 111.46.7 (8): a complete series of degree at least `14` on a
hyperelliptic genus-`7` curve is base-point-free, as is the pure hyperelliptic
series of degree `2 * r` and dimension `r` for `1 ≤ r ≤ 6`. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.isBasePointFree_of_isHyperelliptic :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom],
      IsHyperelliptic X → genus X = 7 →
      ∀ {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r),
        IsComplete g → (1 ≤ r ∧ r ≤ 6 ∧ 2 * r = d) ∨ 14 ≤ d →
          IsBasePointFree g)

/- Exercise 111.46.7 (9): a complete linear series of degree at least `15` on a
hyperelliptic genus-`7` curve induces a closed embedding into `ℙ^r`. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.inducesClosedEmbedding_of_isHyperelliptic :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom],
      IsHyperelliptic X → genus X = 7 →
      ∀ {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r),
        IsComplete g → 15 ≤ d → InducesClosedEmbedding g)

/- Exercise 111.46.7 (10): a trigonal non-hyperelliptic genus-`7` curve admits a
series of degree `3` and dimension `1`, and every series satisfies the
Clifford–Riemann–Roch necessary bound. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.linearSeries_of_isTrigonal :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom],
      IsTrigonal X → ¬IsHyperelliptic X → genus X = 7 →
      Nonempty (LinearSeries X topologicalKrullDim_eq_one.le 3 1) ∧
        ∀ (d r : ℕ), Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r) →
          2 * r ≤ d ∨ r + 7 ≤ d)

/- Exercise 111.46.7 (11): the complete trigonal series of degree `3` and
dimension `1` on a trigonal non-hyperelliptic genus-`7` curve is base-point-free,
as is every complete series of degree at least `14`. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.isBasePointFree_of_isTrigonal :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom],
      IsTrigonal X → ¬IsHyperelliptic X → genus X = 7 →
      ∀ {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r),
        IsComplete g → (d = 3 ∧ r = 1) ∨ 14 ≤ d → IsBasePointFree g)

/- Exercise 111.46.7 (12): a complete canonical series on a trigonal
non-hyperelliptic genus-`7` curve induces a closed embedding into `ℙ^6`, and
every complete series of degree at least `15` induces a closed embedding into `ℙ^r`. -/
@[stacks 0EGR] #check
  (AlgebraicGeometry.Curve.GenusSeven.inducesClosedEmbedding_of_isTrigonal :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Projective X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom],
      IsTrigonal X → ¬IsHyperelliptic X → genus X = 7 →
      ∀ {d r : ℕ} (g : LinearSeries X topologicalKrullDim_eq_one.le d r),
        IsComplete g → (r = 6 ∧ d = 12) ∨ 15 ≤ d → InducesClosedEmbedding g)

/- Supplementary genus-seven existence result. -/
#check (AlgebraicGeometry.Curve.GenusSeven.existsBasePointFreeLinearSeries_trivial :
  ∀ {k : Type u} [Field k] [IsAlgClosed k],
    AlgebraicGeometry.Curve.GenusSeven.existsBasePointFreeLinearSeries k 0 0)

/- Supplementary hyperelliptic-multiple existence result. -/
#check (AlgebraicGeometry.Curve.GenusSeven.existsBasePointFreeLinearSeries_hyperelliptic :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {d r : ℕ},
    1 ≤ r → r ≤ 6 → d = 2 * r →
      AlgebraicGeometry.Curve.GenusSeven.existsBasePointFreeLinearSeries k d r)

/- Supplementary nonspecial existence result. -/
#check (AlgebraicGeometry.Curve.GenusSeven.existsBasePointFreeLinearSeries_nonspecial :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {d r : ℕ},
    14 ≤ d → r + 7 = d →
      AlgebraicGeometry.Curve.GenusSeven.existsBasePointFreeLinearSeries k d r)

/- Supplementary trigonal sufficient existence result. -/
#check (AlgebraicGeometry.Curve.GenusSeven.nonempty_linearSeries_of_isTrigonal :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom],
    IsTrigonal X → ¬IsHyperelliptic X → genus X = 7 → ∀ (d r : ℕ),
      3 * r ≤ d ∨ r + 7 ≤ d →
        Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r))
