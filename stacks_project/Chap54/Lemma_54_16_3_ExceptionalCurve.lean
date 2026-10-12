/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/- The exceptional-curve predicate is provided by the shared mathematical owner. -/
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind :
  ∀ {X : Scheme.{u}}, X.IdealSheafData → Prop)

/- The canonical effective-Cartier instance is provided by the shared mathematical owner. -/
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.instIsEffectiveCartierDivisor :
  ∀ {X : Scheme.{u}} (E : X.IdealSheafData)
    [hE : AlgebraicGeometry.IsExceptionalCurveFirstKind E],
    IsEffectiveCartierDivisor E.subschemeι)

/- The exceptional-curve specification is provided by the shared mathematical owner. -/
#check (AlgebraicGeometry.isExceptionalCurveFirstKind_iff :
  ∀ {X : Scheme.{u}} (E : X.IdealSheafData),
    AlgebraicGeometry.IsExceptionalCurveFirstKind E ↔
      IsEffectiveCartierDivisor E.subschemeι ∧
        ∃ (k : Type u) (_ : Field k) (e : ProjectiveSpace.scheme k 1 ≅ E.subscheme),
          IsIsomorphic
            ((Scheme.Modules.pullback e.hom).obj (Scheme.Hom.normalSheaf E.subschemeι))
            (ProjectiveSpace.twistingSheaf k 1 (-1)))

end AlgebraicGeometry
