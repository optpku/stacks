/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Picard

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 54.16.5 (1): pullback and degree on the exceptional curve form the short exact
sequence `0 ⟶ PicardGroup X' ⟶ PicardGroup X ⟶ ℤ ⟶ 0` for a contraction. -/
@[stacks 0C5L] #check
  (AlgebraicGeometry.IsExceptionalCurveFirstKind.picardDegreeSequence_shortExact :
    ∀ {X X' : Scheme.{u}} [IsNoetherian X]
      (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
      (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x),
      (AlgebraicGeometry.IsExceptionalCurveFirstKind.picardDegreeSequence E b x hb).ShortExact)

/- Lemma 54.16.5 (2): the map `n ↦ 𝒪_X(-nE)` splits the degree map in the Picard-group
sequence of a contraction. -/
@[stacks 0C5L] #check
  (AlgebraicGeometry.IsExceptionalCurveFirstKind.picardDegreeSequence_splitByExceptionalTwist :
    ∀ {X X' : Scheme.{u}} [IsNoetherian X]
      (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
      (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x),
      (AlgebraicGeometry.IsExceptionalCurveFirstKind.degree E).comp
        (AlgebraicGeometry.IsExceptionalCurveFirstKind.exceptionalTwist E) = AddMonoidHom.id ℤ)

end AlgebraicGeometry
