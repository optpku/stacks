/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.QuotientSheaf
import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory AlgebraicSpace

/- Definition 78.19.1: for a pre-relation `j : R ⟶ U ×_B U` over `B / S`, the
quotient sheaf `U/R` is the fppf sheafification of the objectwise quotient
presheaf on `(Sch / S)_fppf`. -/
@[stacks 044J] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheaf :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B},
      PreRelation U → Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))

/- The underlying presheaf of `U/R` is the sheafification of the universe-raised
quotient presheaf. -/
#check
  (PreRelation.quotientSheaf_val :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
      (P : PreRelation U),
      (P.quotientSheaf).obj =
        sheafify (Scheme.fppfTopology.over S)
          (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}))

/- If `j` comes from a `G`-action on `U` as in Lemma 78.15.1, the quotient sheaf is
denoted `U/G`. -/
#check
  (AlgebraicGeometry.GroupAlgebraicSpace.Action.quotientSheaf :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupAlgebraicSpace B},
      GroupAlgebraicSpace.Action G →
        Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
