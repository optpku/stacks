/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.SingleObj

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u w z

namespace CategoryTheory.ModuleCat

/-- Right-exact functors on finitely presented right modules over a ring are equivalent to
additive functors from the associated one-object category, with the regular-module value
recording the induced scalar action. -/
theorem rightExactFunctorEquivalenceModuleAction
    {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B] :
    let A₀ : (ModuleCat.isFinitePresentation.{u, u} Aᵐᵒᵖ).FullSubcategory :=
      ⟨ModuleCat.of Aᵐᵒᵖ A, Module.FinitePresentation.rightRegular A⟩
    ∃ e :
      ((ModuleCat.isFinitePresentation.{u, u} Aᵐᵒᵖ).FullSubcategory ⥤ᵣ B) ≌
        (SingleObj A ⥤+ B),
      ∀ (F : (ModuleCat.isFinitePresentation.{u, u} Aᵐᵒᵖ).FullSubcategory ⥤ᵣ B),
        ∃ i : (e.functor.obj F).obj.obj (SingleObj.star A) ≅ F.obj.obj A₀,
          ∀ a : A,
            (e.functor.obj F).obj.map a ≫ i.hom =
              i.hom ≫ F.obj.map (ObjectProperty.homMk
                (ModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a))) := sorry

end CategoryTheory.ModuleCat
