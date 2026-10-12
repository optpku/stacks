/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Contraction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Contracting an exceptional curve of the first kind preserves at-worst-nodality over a
discrete valuation ring. -/
theorem atWorstNodal_of_exceptionalCurveContraction
    (R K k : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field k]
    (residueFieldEquiv : k ≃+* IsLocalRing.ResidueField R)
    {X X' : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (x : closedPoints X') (b : X ⟶ X') (h : IsContraction E b x)
    (f : X' ⟶ Spec (.of R)) [AtWorstNodal (b ≫ f)] :
    AtWorstNodal f := sorry

end AlgebraicGeometry
