/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.RightExact
public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.RightExact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u w z

namespace CategoryTheory.ModuleCat

/-- Right-exact functors from right `A`-modules to `B` that preserve coproducts indexed by
types in the module universe. -/
def rightExactPreservesCoproducts (A : Type u) [Ring A] (B : Type w)
    [Category.{z} B] [HasCoproducts.{u} B] :
    ObjectProperty (ModuleCat.{u} Aᵐᵒᵖ ⥤ᵣ B) :=
  fun F ↦ ∀ (J : Type u), PreservesColimitsOfShape (Discrete J) F.obj

/-- Membership in `rightExactPreservesCoproducts` is preservation of `Discrete J`-shaped
colimits for every index type `J` in the module universe. -/
theorem rightExactPreservesCoproducts_iff {A : Type u} [Ring A] {B : Type w}
    [Category.{z} B] [HasCoproducts.{u} B] (F : ModuleCat.{u} Aᵐᵒᵖ ⥤ᵣ B) :
    rightExactPreservesCoproducts A B F ↔
      ∀ (J : Type u), PreservesColimitsOfShape (Discrete J) F.obj :=
  sorry

/-- Coproduct-preserving right-exact functors from right `A`-modules to `B`. -/
abbrev RightExactCoproductPreservingFunctor (A : Type u) [Ring A] (B : Type w)
    [Category.{z} B] [HasCoproducts.{u} B] :=
  (rightExactPreservesCoproducts A B).FullSubcategory

/-- Right-exact coproduct-preserving functors from right `A`-modules to `B` are equivalent to
additive functors from the one-object category associated to `A`, with the regular-module value
recording the induced scalar action. -/
theorem rightExactCoproductPreservingFunctorEquivalenceModuleAction
    {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B] [HasCoproducts.{u} B] :
    ∃ e : RightExactCoproductPreservingFunctor A B ≌ (SingleObj A ⥤+ B),
      ∀ (F : RightExactCoproductPreservingFunctor A B),
        let KF := (e.functor.obj F).obj
        let FA := F.obj.obj
        ∃ i : KF.obj (SingleObj.star A) ≅ FA.obj (ModuleCat.of Aᵐᵒᵖ A),
          ∀ a : A,
            KF.map a ≫ i.hom =
              i.hom ≫ FA.map (ModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a)) :=
  sorry

end CategoryTheory.ModuleCat
