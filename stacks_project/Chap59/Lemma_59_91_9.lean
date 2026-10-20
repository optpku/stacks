/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 59.91.9: torsion abelian étale cohomology commutes with arbitrary
base change in every degree for a finite morphism of schemes. -/
@[stacks 0A4E]
#check (AlgebraicGeometry.Scheme.Hom.cohomologyCommutesWithBaseChange_of_isFinite :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Z : Scheme.{u},
      HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})],
    AlgebraicGeometry.Scheme.Hom.CohomologyCommutesWithBaseChange f)

end
