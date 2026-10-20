/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Effacement

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

#check
  (AlgebraicGeometry.Scheme.Etale.smallEtalePullback_obj_terminal :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [HasTerminal X.Etale] [HasTerminal Z.Etale],
      (smallEtalePullback i).obj (terminal X.Etale) ≅ terminal Z.Etale)

#check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomologyRestrict :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X.Etale]
    [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal Z.Etale]
    [(siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive]
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ),
      etaleCohomology X F q ⟶
        etaleCohomology Z ((etaleAbelianRestriction i).obj F) q)

end AlgebraicGeometry.Scheme.Etale
