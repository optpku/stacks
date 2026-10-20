/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open CategoryTheory.GrothendieckTopology.Point
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Postcompose a geometric point with a scheme morphism, with the morphism argument first. -/
noncomputable abbrev imageGeometricPoint {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') : GeometricPoint Y :=
  ybar'.map g

end AlgebraicGeometry.Scheme.Etale

#check (AlgebraicGeometry.Scheme.Etale.pullbackSheafFiberIso :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
    (toSmallEtalePoint (ybar'.map g)).sheafFiber.obj F ≅
      (toSmallEtalePoint ybar').sheafFiber.obj
        (((smallEtalePullback g).sheafPullback AddCommGrpCat.{u}
            Y.smallEtaleTopology Y'.smallEtaleTopology).obj F))

#check (AlgebraicGeometry.Scheme.Etale.sheafifyPresheafPushforwardAdjoint_stalk :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G')
    (V : GeometricPoint.EtaleNeighborhood (ybar'.map g)),
    (toSmallEtalePoint (ybar'.map g)).toPresheafFiber V.toEtale V.2 G ≫
        ((toSmallEtalePoint (ybar'.map g)).presheafToSheafCompSheafFiberIso
            AddCommGrpCat.{u}).inv.app G ≫
          (pullbackSheafFiberIso g ybar'
              ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G)).hom ≫
            (toSmallEtalePoint ybar').sheafFiber.map
              (sheafifyPresheafPushforwardAdjoint g α) =
      α.app (op V.toEtale) ≫
        (toSmallEtalePoint ybar').toPresheafFiber
          (pullbackNeighborhood g ybar' V).toEtale (pullbackNeighborhood g ybar' V).2 G' ≫
          ((toSmallEtalePoint ybar').presheafToSheafCompSheafFiberIso
              AddCommGrpCat.{u}).inv.app G')

end
