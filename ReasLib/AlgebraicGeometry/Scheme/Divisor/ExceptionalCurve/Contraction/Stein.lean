module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Contraction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein.Proper

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Scheme.Hom.FiniteType (QuasiFiniteAt)
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsExceptionalCurveFirstKind

/-- A proper morphism from a Noetherian scheme that contracts an exceptional curve and is
quasi-finite away from it yields a contraction on the canonical Stein factorization. -/
theorem exists_isContraction_toNormalization
    {X Y : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (f : X ⟶ Y) [IsNoetherian Y] [IsProper f] (y : Y)
    (h_maps : Set.MapsTo f E.support ({y} : Set Y))
    (h_quasiFinite : ∀ x : X, x ∉ E.support → QuasiFiniteAt f x) :
    ∃ y' : closedPoints f.normalization,
      IsContraction E f.toNormalization y' ∧ f.fromNormalization y'.1 = y := sorry

end AlgebraicGeometry.IsExceptionalCurveFirstKind
