/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Remark_85_4_1_Fiberwise
public import stacks_project.Chap85.Remark_85_5_1_Morphism

public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialCompatibility

/-!
# Compatibility of augmented simplicial sites

The defining compatibility condition is checked against the shared mathematical API.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Grothendieck

section

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable {D' : Type u} [Category.{v} D'] (K' : Precoverage D')
variable (u0 : F.obj (op ⦋0⦌) ⥤ D) (u0' : F'.obj (op ⦋0⦌) ⥤ D')
variable (α : F ⟶ F') (v : D ⥤ D')
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
variable [hα : IsFiberwiseMorphism J J' α]
variable [h_aug : IsAugmentation F J K u0] [h_aug' : IsAugmentation F' J' K' u0']
include instF instF' hα h_aug h_aug'


#check (CategoryTheory.Grothendieck.IsCompatible.iff J J' K K' u0 u0' α v :
  CategoryTheory.Grothendieck.IsCompatible J J' K K' u0 u0' α v ↔
    Functor.Precoverage.IsCocontinuous v K K' ∧
      (α.app (op ⦋0⦌)).toFunctor ⋙ u0' = u0 ⋙ v)

end

end CategoryTheory.Grothendieck
