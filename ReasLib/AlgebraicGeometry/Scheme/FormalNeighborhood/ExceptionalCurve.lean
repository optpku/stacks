/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve
public import ReasLib.AlgebraicGeometry.Scheme.FormalNeighborhood

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FormalNeighborhood

/-- The formal-neighborhood ring of an exceptional curve of the first kind is regular local. -/
instance instIsRegularLocalRing {X : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [AlgebraicGeometry.IsExceptionalCurveFirstKind E] :
    IsRegularLocalRing (ring E) := sorry

/-- The formal-neighborhood ring of an exceptional curve of the first kind is complete local. -/
instance instIsCompleteLocalRing {X : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [AlgebraicGeometry.IsExceptionalCurveFirstKind E] :
    IsCompleteLocalRing (ring E) := sorry

/-- The formal-neighborhood ring of an exceptional curve of the first kind has Krull dimension
two. -/
theorem ringKrullDim_eq_two {X : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [AlgebraicGeometry.IsExceptionalCurveFirstKind E] :
    ringKrullDim (ring E) = 2 := sorry

/-- The kernel of the projection to positive stage `n` is the `(n + 1)`st power of the maximal
ideal. -/
theorem ker_projection {X : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [AlgebraicGeometry.IsExceptionalCurveFirstKind E] (n : ℕ) :
    RingHom.ker (projection E n).hom =
      IsLocalRing.maximalIdeal (ring E) ^ (n + 1) := sorry

end AlgebraicGeometry.Scheme.FormalNeighborhood
