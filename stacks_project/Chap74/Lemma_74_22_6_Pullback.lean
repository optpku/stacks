/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback

open AlgebraicGeometry CategoryTheory

universe u v

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor :
  (a : Y ⟶ X) → (a' : Y' ⟶ X') → (h : X' ⟶ X) →
    (f : Y' ⟶ Y) → CommSq f a' a h →
      AlgebraicGeometry.AlgebraicSpace.DescentData (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a) ⥤
        AlgebraicGeometry.AlgebraicSpace.DescentData (fun _ : PUnit.{v + 1} ↦ Y') (fun _ ↦ a'))

#check (AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.iso :
  (a : Y ⟶ X) → (a' : Y' ⟶ X') → (h : X' ⟶ X) →
    (f₀ f₁ : Y' ⟶ Y) → (sq₀ : CommSq f₀ a' a h) → (sq₁ : CommSq f₁ a' a h) →
      AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor a a' h f₀ sq₀ ≅
        AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback.functor a a' h f₁ sq₁)
