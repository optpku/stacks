/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.ProjectiveLine
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.ProjectiveSpace

noncomputable section

universe u

/- Lemma 59.91.10: to prove that cohomology commutes with base change for every
proper morphism of schemes, it suffices to prove `CohomologyCommutesWithBaseChange`
for the structure morphism `ProjectiveSpace.toBase 1 S : ProjectiveSpace 1 S ⟶ S`
of the relative projective line, for every scheme `S`. -/
@[stacks 0A4F] #check
  (AlgebraicGeometry.Scheme.Hom.cohomologyCommutesWithBaseChange_of_projectiveLine.{u} :
    ∀ [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Z : Scheme.{u},
        HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
      (hP1 : ∀ S : Scheme.{u}, CohomologyCommutesWithBaseChange (toBase 1 S))
      {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
      CohomologyCommutesWithBaseChange f)

end

end
