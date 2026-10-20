/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Basic

/-!
# Functoriality on target denominators

The target-denominator action of localizer morphisms preserves identity and composition up to
canonical identity-component natural isomorphisms.  The explicit component formulas let clients
normalize iterated restrictions without unfolding `MorphismProperty.Under` objects.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.LocalizerMorphism.targetDenominators

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₃ : MorphismProperty C₃}

/-- Compatibility of the identity component for the target-denominator identity comparison. -/
theorem idComponent_comm (W : MorphismProperty C₁) (X : C₁)
    (U : MorphismProperty.Under W ⊤ X) :
    (((LocalizerMorphism.id W).targetDenominators X).obj U).hom ≫ 𝟙 U.right =
      U.hom := sorry

/-- The identity component comparing the target-denominator action of the identity localizer
morphism with the identity functor. -/
def idComponent (W : MorphismProperty C₁) (X : C₁)
    (U : MorphismProperty.Under W ⊤ X) :
    ((LocalizerMorphism.id W).targetDenominators X).obj U ≅ U :=
  MorphismProperty.Under.isoMk (Iso.refl U.right) (idComponent_comm W X U)

/-- Naturality of the target-denominator identity comparison components. -/
theorem idComponent_naturality (W : MorphismProperty C₁) (X : C₁)
    {U V : MorphismProperty.Under W ⊤ X} (f : U ⟶ V) :
    ((LocalizerMorphism.id W).targetDenominators X).map f ≫
        (idComponent W X V).hom =
      (idComponent W X U).hom ≫ f := sorry

/-- The target-denominator action of the identity localizer morphism is canonically isomorphic to
the identity functor. -/
@[stacks 05T5 "identity comparison on target denominators"]
def idIso (W : MorphismProperty C₁) (X : C₁) :
    (LocalizerMorphism.id W).targetDenominators X ≅
      𝟭 (MorphismProperty.Under W ⊤ X) :=
  NatIso.ofComponents (idComponent W X) (idComponent_naturality W X)

/-- The forward target-denominator identity comparison is the identity on target objects. -/
@[simp]
theorem idIso_hom_app_right (W : MorphismProperty C₁) (X : C₁)
    (U : MorphismProperty.Under W ⊤ X) :
    ((idIso W X).hom.app U).right = 𝟙 U.right := sorry

/-- The inverse target-denominator identity comparison is the identity on target objects. -/
@[simp]
theorem idIso_inv_app_right (W : MorphismProperty C₁) (X : C₁)
    (U : MorphismProperty.Under W ⊤ X) :
    ((idIso W X).inv.app U).right = 𝟙 U.right := sorry

/-- Compatibility of the identity component for the target-denominator composition
comparison. -/
theorem compComponent_comm (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    (U : MorphismProperty.Under W₁ ⊤ X) :
    ((Φ.targetDenominators X ⋙
          Ψ.targetDenominators (Φ.functor.obj X)).obj U).hom ≫
        𝟙 (Ψ.functor.obj (Φ.functor.obj U.right)) =
      (((Φ.comp Ψ).targetDenominators X).obj U).hom := sorry

/-- The identity component comparing successive target-denominator actions with the action of a
composite localizer morphism. -/
def compComponent (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    (U : MorphismProperty.Under W₁ ⊤ X) :
    (Φ.targetDenominators X ⋙
        Ψ.targetDenominators (Φ.functor.obj X)).obj U ≅
      ((Φ.comp Ψ).targetDenominators X).obj U :=
  MorphismProperty.Under.isoMk
    (Iso.refl (Ψ.functor.obj (Φ.functor.obj U.right)))
    (compComponent_comm Φ Ψ X U)

/-- Naturality of the target-denominator composition comparison components. -/
theorem compComponent_naturality (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    {U V : MorphismProperty.Under W₁ ⊤ X} (f : U ⟶ V) :
    (Φ.targetDenominators X ⋙
          Ψ.targetDenominators (Φ.functor.obj X)).map f ≫
        (compComponent Φ Ψ X V).hom =
      (compComponent Φ Ψ X U).hom ≫
        ((Φ.comp Ψ).targetDenominators X).map f := sorry

/-- Successive target-denominator actions agree canonically with the action of the composite
localizer morphism. -/
@[stacks 05T5 "composition comparison on target denominators"]
def compIso (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁) :
    Φ.targetDenominators X ⋙ Ψ.targetDenominators (Φ.functor.obj X) ≅
      (Φ.comp Ψ).targetDenominators X :=
  NatIso.ofComponents (compComponent Φ Ψ X)
    (compComponent_naturality Φ Ψ X)

/-- The forward target-denominator composition comparison is the identity on target objects. -/
@[simp]
theorem compIso_hom_app_right (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    (U : MorphismProperty.Under W₁ ⊤ X) :
    ((compIso Φ Ψ X).hom.app U).right =
      𝟙 (Ψ.functor.obj (Φ.functor.obj U.right)) := sorry

/-- The inverse target-denominator composition comparison is the identity on target objects. -/
@[simp]
theorem compIso_inv_app_right (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    (U : MorphismProperty.Under W₁ ⊤ X) :
    ((compIso Φ Ψ X).inv.app U).right =
      𝟙 (Ψ.functor.obj (Φ.functor.obj U.right)) := sorry

end CategoryTheory.LocalizerMorphism.targetDenominators
