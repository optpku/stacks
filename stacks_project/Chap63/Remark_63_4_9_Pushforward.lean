/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PresheafPushforward

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

#check (AlgebraicGeometry.Scheme.Etale.presheafPushforwardAb :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y),
    (Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}))

#check (AlgebraicGeometry.Scheme.Etale.sheafifyPresheafPushforward :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G'),
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G ⟶
      (smallEtalePushforwardAb g).obj
        ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G'))

end
