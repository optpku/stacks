/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.ContractionPicard
public import stacks_project.Chap54.Lemma_54_16_5
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsExceptionalCurveFirstKind

variable {X X' : Scheme.{u}} [IsNoetherian X]
variable (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
variable (b : X ⟶ X') (x : closedPoints X') (hb : IsContraction E b x)
variable (a : X.PicardGroup) (a' : X'.PicardGroup) (n : ℤ)

/- Remark 54.16.6 (1): contraction of an exceptional curve identifies `PicardGroup X` with
`PicardGroup X' × ℤ`. -/
@[stacks 0C5M]
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.picardDecomposition E b x hb :
  X.PicardGroup ≃+ X'.PicardGroup × ℤ)

#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.descendedModule E b x hb a : X'.Modules)
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.descendedModule_invertible E b x hb a :
  Scheme.Modules.Invertible
    (AlgebraicGeometry.IsExceptionalCurveFirstKind.descendedModule E b x hb a))

/- Remark 54.16.6 (2): a Picard class `a` corresponds to `(a', n)` precisely when
`a = b^*a' + [𝒪_X(-nE)]`. -/
@[stacks 0C5M]
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.picardDecomposition_eq_iff E b x hb a a' n :
  AlgebraicGeometry.IsExceptionalCurveFirstKind.picardDecomposition E b x hb a = (a', n) ↔
    a = Scheme.Hom.picardPullback b a' +
      AlgebraicGeometry.IsExceptionalCurveFirstKind.exceptionalTwist E n)

/- Remark 54.16.6 (3): the first coordinate of a class `a` is represented by
`b_* (repr(a)(degree E a · E))`. In particular, the first-coordinate assignment is a group
homomorphism. -/
@[stacks 0C5M]
#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.picardDescent_reprIso E b x hb a :
  Scheme.PicardGroup.repr
      (AlgebraicGeometry.IsExceptionalCurveFirstKind.picardDescent E b x hb a) ≅
    (Scheme.Modules.pushforward b).obj
      (Scheme.Modules.twistByTensorPower E.associatedSheaf
        (Scheme.PicardGroup.repr a) (AlgebraicGeometry.IsExceptionalCurveFirstKind.degree E a)))

#check (AlgebraicGeometry.IsExceptionalCurveFirstKind.picardDescent E b x hb :
  X.PicardGroup →+ X'.PicardGroup)

end AlgebraicGeometry.IsExceptionalCurveFirstKind
