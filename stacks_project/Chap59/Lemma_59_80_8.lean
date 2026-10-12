/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Gabber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 59.80.8: for a normal integral affine scheme with separably closed
function field, the positive-degree small-etale cohomology of every closed
subscheme with finite constant coefficients vanishes. -/
@[stacks 09ZC] #check
  (AlgebraicGeometry.Scheme.Hom.etaleHq_constantFinite_isZero :
    ∀ {X Z : Scheme.{u}} [IsAffine X] [IsIntegral X] (hX : X.isNormal)
      [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
      (M : AddCommGrpCat.{u}) [Finite M]
      [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
      (q : ℕ) (hq : 1 ≤ q),
      IsZero
        ((Sheaf.functorH Z.smallEtaleTopology q).obj
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M)))
