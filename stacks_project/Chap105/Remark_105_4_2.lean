/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.DiagonalBaseChange.Comparison.OverBase
public import stacks_project.Chap105.Definition_105_5_1_Moduli
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry EllipticCurve
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.ProductSlice

universe u

variable (S S' : Over Moduli.specInt.{u})
  (E : Over S.left) (zero : S.left ⟶ E.left)
  (E' : Over S'.left) (zero' : S'.left ⟶ E'.left)
  [IsEllipticCurve E zero] [IsEllipticCurve E' zero']

/-- Remark 105.4.2 (1): the fibre product of the classifying morphisms of two
elliptic curves is the base change of the diagonal of their moduli stack along
the product of their base schemes. -/
@[stacks 072N]
noncomputable def ellipticCurveDiagonalBaseChange :
    total (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
      (Moduli.classifying S' E' zero') (Moduli.classifying S E zero)) ≌
    total (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
      (PseudoPullbackCone.map (sourceSquare.coneComparison.{u, u + 1}
        (Moduli.classifying S E zero) (Moduli.classifying S' E' zero')))
      (diagonal moduli)) :=
  DiagonalBaseChange.equivalence.{u, u + 1}
    (Moduli.classifying S E zero) (Moduli.classifying S' E' zero')

/-- Remark 105.4.2 (2): representability of the fibre product of two elliptic-curve
classifying morphisms is equivalent to representability of the corresponding
base change of the diagonal of the moduli stack of elliptic curves. -/
@[stacks 072N]
theorem ellipticCurveDiagonalBaseChange_representable_iff :
    IsRepresentable (TwoFibreProduct.apex
      (Moduli.classifying S' E' zero') (Moduli.classifying S E zero)) ↔
    IsRepresentable (TwoFibreProduct.apex
      (PseudoPullbackCone.map (sourceSquare.coneComparison
        (Moduli.classifying S E zero) (Moduli.classifying S' E' zero')))
      (diagonal moduli)) := sorry
