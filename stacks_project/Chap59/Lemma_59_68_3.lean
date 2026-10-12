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

/- Lemma 59.68.3: for a smooth curve over an algebraically closed field, small-étale
cohomology of the pushforward sheaf `genericUnitsPushforward` (`j_* G_{m,η}`) vanishes
in every degree `p ≥ 1`. -/
@[stacks 03RK] #check
  (AlgebraicGeometry.SchemeOverField.genericUnitsPushforward_etaleCohomology_isZero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [Smooth X.hom]
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify
        (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology
        AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
      (p : ℕ) (hp : 0 < p),
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology p).obj
      (genericUnitsPushforward X)))

end AlgebraicGeometry.SchemeOverField
