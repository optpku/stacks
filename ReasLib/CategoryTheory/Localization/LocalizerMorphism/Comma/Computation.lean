/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Basic

/-!
# Computation for localizer-morphism comma functors

These formulas expose the object, morphism, and projection behavior of the localization comma
functors without requiring clients to unfold `StructuredArrow.map₂` or
`CostructuredArrow.map₂`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace costructuredArrow

/-- The source object of a mapped localization costructured arrow is mapped by the underlying
functor of localizers. -/
@[simp]
theorem obj_left (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : CostructuredArrow W₁.Q (W₁.Q.obj X)) :
    ((Φ.costructuredArrow X).obj U).left = Φ.functor.obj U.left := sorry

/-- The structural map of a mapped localization costructured arrow is conjugated by the
canonical localization comparison. -/
@[simp]
theorem obj_hom (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : CostructuredArrow W₁.Q (W₁.Q.obj X)) :
    ((Φ.costructuredArrow X).obj U).hom =
      (Φ.facIso W₁.Q W₂.Q).hom.app U.left ≫
        (Φ.localizedFunctor W₁.Q W₂.Q).map U.hom ≫
          (Φ.facIso W₁.Q W₂.Q).inv.app X := sorry

/-- The source component of a mapped localization costructured-arrow morphism is mapped by the
underlying functor of localizers. -/
@[simp]
theorem map_left (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {U V : CostructuredArrow W₁.Q (W₁.Q.obj X)} (f : U ⟶ V) :
    ((Φ.costructuredArrow X).map f).left = Φ.functor.map f.left := sorry

/-- Projection from mapped localization costructured arrows is the source projection followed
by the underlying functor of localizers. -/
theorem comp_proj (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    Φ.costructuredArrow X ⋙
        CostructuredArrow.proj W₂.Q (W₂.Q.obj (Φ.functor.obj X)) =
      CostructuredArrow.proj W₁.Q (W₁.Q.obj X) ⋙ Φ.functor := sorry

end costructuredArrow

namespace structuredArrow

/-- The target object of a mapped localization structured arrow is mapped by the underlying
functor of localizers. -/
@[simp]
theorem obj_right (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : StructuredArrow (W₁.Q.obj X) W₁.Q) :
    ((Φ.structuredArrow X).obj U).right = Φ.functor.obj U.right := sorry

/-- The structural map of a mapped localization structured arrow is conjugated by the
canonical localization comparison. -/
@[simp]
theorem obj_hom (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : StructuredArrow (W₁.Q.obj X) W₁.Q) :
    ((Φ.structuredArrow X).obj U).hom =
      (Φ.facIso W₁.Q W₂.Q).hom.app X ≫
        (Φ.localizedFunctor W₁.Q W₂.Q).map U.hom ≫
          (Φ.facIso W₁.Q W₂.Q).inv.app U.right := sorry

/-- The target component of a mapped localization structured-arrow morphism is mapped by the
underlying functor of localizers. -/
@[simp]
theorem map_right (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {U V : StructuredArrow (W₁.Q.obj X) W₁.Q} (f : U ⟶ V) :
    ((Φ.structuredArrow X).map f).right = Φ.functor.map f.right := sorry

/-- Projection from mapped localization structured arrows is the target projection followed by
the underlying functor of localizers. -/
theorem comp_proj (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    Φ.structuredArrow X ⋙
        StructuredArrow.proj (W₂.Q.obj (Φ.functor.obj X)) W₂.Q =
      StructuredArrow.proj (W₁.Q.obj X) W₁.Q ⋙ Φ.functor := sorry

end structuredArrow


end CategoryTheory.LocalizerMorphism
