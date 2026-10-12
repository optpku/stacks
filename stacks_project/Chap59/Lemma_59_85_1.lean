/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ProperHenselian
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 59.85.1 compares first étale cohomology with finite constant
coefficients on a proper scheme over a henselian local ring and its closed
fibre. -/
@[stacks 0A5G]
#check (AlgebraicGeometry.Scheme.Hom.etaleH1IsomorphicOfProperHenselian :
    ∀ {A : Type u} [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (M : AddCommGrpCat.{u})
    [Finite M]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify
      (f.fiber (IsLocalRing.closedPoint A)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u}
      (Sheaf (f.fiber (IsLocalRing.closedPoint A)).smallEtaleTopology
        AddCommGrpCat.{u})],
    IsIsomorphic
      ((Sheaf.functorH X.smallEtaleTopology 1).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M))
      ((Sheaf.functorH
          (f.fiber (IsLocalRing.closedPoint A)).smallEtaleTopology 1).obj
        ((constantSheaf
            (f.fiber (IsLocalRing.closedPoint A)).smallEtaleTopology
            AddCommGrpCat.{u}).obj M)))

end AlgebraicGeometry.Scheme.Hom
