/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction.Opens
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

universe u v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.28.1
Let f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y) be a morphism of ringed spaces. The functors
L(f)^* : D(𝒪_Y) ⥤ D(𝒪_X) and R(f)_* : D(𝒪_X) ⥤ D(𝒪_Y) are adjoint, equivalently
Hom_{D(𝒪_X)}((L(f)^*).obj 𝒢, ℱ) ≃ Hom_{D(𝒪_Y)}(𝒢, (R(f)_*).obj ℱ) bifunctorially
in ℱ ∈ D(𝒪_X) and 𝒢 ∈ D(𝒪_Y). -/
@[stacks 079W]
#check (AlgebraicGeometry.RingedSpace.moduleDerivedAdjunctionOfOpens :
  ∀ {X Y : RingedSpace.{u}} (f : X ⟶ Y), L(f)^* ⊣ R(f)_*)

#check (CategoryTheory.Adjunction.homEquiv :
  ∀ {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {F : C ⥤ D} {G : D ⥤ C} (_adj : F ⊣ G) (X : C) (Y : D),
    (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))

end AlgebraicGeometry.RingedSpace
