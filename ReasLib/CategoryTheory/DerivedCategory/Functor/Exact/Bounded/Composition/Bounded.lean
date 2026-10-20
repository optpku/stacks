/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Composition.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of bounded exact derived functors

The generic restricted composition comparison specializes to bounded derived
categories, with objectwise and underlying-component readouts.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ExactFunctor.Derived.Bounded

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
variable {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

/-- Passage to bounded derived categories commutes naturally with composition
of bundled exact functors. -/
@[stacks 015F "bounded exact derived functors preserve composition"]
noncomputable def compFunctorIso (F : A ⥤ₑ B) (G : B ⥤ₑ C) :
    functor (F.comp G) ≅ functor F ⋙ functor G :=
  Restriction.compFunctorIso F G
    (mapsTo F) (mapsTo G) (mapsTo (F.comp G))

/-- The objectwise composition comparison for exact functors on bounded
derived categories. -/
@[stacks 015F "bounded exact derived composition comparison"]
noncomputable abbrev compObjIso (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (X : DerivedCategory.Bounded A) :
    (functor (F.comp G)).obj X ≅ (functor F ⋙ functor G).obj X :=
  (compFunctorIso F G).app X

/-- Naturality of the objectwise composition comparison on bounded derived
categories. -/
@[reassoc]
theorem compObjIso_naturality (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    {X Y : DerivedCategory.Bounded A} (f : X ⟶ Y) :
    (functor (F.comp G)).map f ≫ (compObjIso F G Y).hom =
      (compObjIso F G X).hom ≫ (functor F ⋙ functor G).map f := sorry

namespace compFunctorIso

/-- The components of the bounded composition comparison are the objectwise
comparisons. -/
@[simp]
theorem app (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (X : DerivedCategory.Bounded A) :
    (compFunctorIso F G).app X = compObjIso F G X := sorry

/-- Forgetting the bounded structure identifies the forward component with
the ambient exact-derived composition comparison. -/
@[simp, stacks 015F "bounded composition comparison forward component"]
theorem hom_app_hom (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (X : DerivedCategory.Bounded A) :
    ((compFunctorIso F G).hom.app X).hom =
      (ExactFunctor.MapDerivedCategory.compObjIso F G X.obj).hom := sorry

/-- Forgetting the bounded structure identifies the inverse component with
the ambient exact-derived composition comparison. -/
@[simp, stacks 015F "bounded composition comparison inverse component"]
theorem inv_app_hom (F : A ⥤ₑ B) (G : B ⥤ₑ C)
    (X : DerivedCategory.Bounded A) :
    ((compFunctorIso F G).inv.app X).hom =
      (ExactFunctor.MapDerivedCategory.compObjIso F G X.obj).inv := sorry

end compFunctorIso

end CategoryTheory.ExactFunctor.Derived.Bounded
