/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Etale.Small
  CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 59.68.4: for a smooth curve over an algebraically closed field, small-étale
cohomology of the coproduct sheaf `closedPointsCoproduct` vanishes in every degree
`q ≥ 1`. -/
@[stacks 03RL] #check
  (AlgebraicGeometry.SchemeOverField.closedPointsCoproduct_etaleCohomology_isZero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ x : ClosedPoint X, HasSheafify (Spec (X.left.residueField x.1)).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasCoproduct fun x : ClosedPoint X ↦ closedPointConstantZPushforward X x.1 x.2]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    (q : ℕ) (hq : 0 < q),
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology q).obj
      (closedPointsCoproduct X)))

end AlgebraicGeometry.SchemeOverField
