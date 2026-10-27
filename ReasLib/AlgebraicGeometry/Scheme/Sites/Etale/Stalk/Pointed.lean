/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber
public import ReasLib.CategoryTheory.Category.Pointed.Limits

/-!
# Pointed étale stalks on geometric fibres

Fibrewise coproducts of pointed stalks and products of pointed skyscraper sheaves are indexed by geometric lifts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}}

/-- The coproduct of pointed stalks over a geometric point. -/
def pointedStalkCoproduct (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    Sheaf X.smallEtaleTopology Pointed.{u} ⥤ Pointed.{u} where
  obj G := ∐ fun x : Fiber f ybar ↦
    (toSmallEtalePoint x.point).sheafFiber.obj G
  map {G H} φ := Limits.Sigma.map fun x : Fiber f ybar ↦
    (toSmallEtalePoint x.point).sheafFiber.map φ
  map_id := sorry
  map_comp := sorry

/-- The value of `pointedStalkCoproduct` is the coproduct of the stalks. -/
theorem pointedStalkCoproduct_obj (f : X ⟶ Y) (ybar : GeometricPoint Y)
    (G : Sheaf X.smallEtaleTopology Pointed.{u}) :
    (pointedStalkCoproduct f ybar).obj G =
      ∐ fun x : Fiber f ybar ↦ (toSmallEtalePoint x.point).sheafFiber.obj G := rfl

/-- The map of `pointedStalkCoproduct` is the coproduct of the stalk maps. -/
theorem pointedStalkCoproduct_map (f : X ⟶ Y) (ybar : GeometricPoint Y)
    {G H : Sheaf X.smallEtaleTopology Pointed.{u}} (φ : G ⟶ H) :
    (pointedStalkCoproduct f ybar).map φ =
      Limits.Sigma.map fun x : Fiber f ybar ↦ (toSmallEtalePoint x.point).sheafFiber.map φ := rfl

/-- The product of pointed skyscraper sheaves over a geometric point. -/
def pointedSkyscraperProduct (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    Pointed.{u} ⥤ Sheaf X.smallEtaleTopology Pointed.{u} where
  obj S := ∏ᶜ fun x : Fiber f ybar ↦
    (toSmallEtalePoint x.point).skyscraperSheafFunctor.obj S
  map {S T} φ := Limits.Pi.map fun x : Fiber f ybar ↦
    (toSmallEtalePoint x.point).skyscraperSheafFunctor.map φ
  map_id := sorry
  map_comp := sorry

/-- The value of `pointedSkyscraperProduct` is the product of the skyscrapers. -/
theorem pointedSkyscraperProduct_obj (f : X ⟶ Y) (ybar : GeometricPoint Y) (S : Pointed.{u}) :
    (pointedSkyscraperProduct f ybar).obj S =
      ∏ᶜ fun x : Fiber f ybar ↦ (toSmallEtalePoint x.point).skyscraperSheafFunctor.obj S := rfl

/-- The map of `pointedSkyscraperProduct` is the product of the skyscraper maps. -/
theorem pointedSkyscraperProduct_map (f : X ⟶ Y) (ybar : GeometricPoint Y)
    {S T : Pointed.{u}} (φ : S ⟶ T) :
    (pointedSkyscraperProduct f ybar).map φ =
      Limits.Pi.map fun x : Fiber f ybar ↦
        (toSmallEtalePoint x.point).skyscraperSheafFunctor.map φ := rfl

end AlgebraicGeometry.Scheme.Etale

end
