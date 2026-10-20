module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Basic

/-!
# Functoriality on source denominators

The source-denominator action of localizer morphisms preserves identity and composition up to
canonical identity-component natural isomorphisms.  This is the dual normalization API for
iterated restrictions in pointwise right Kan-extension arguments.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.LocalizerMorphism.sourceDenominators

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₃ : MorphismProperty C₃}

/-- Compatibility of the identity component for the source-denominator identity comparison. -/
theorem idComponent_comm (W : MorphismProperty C₁) (X : C₁)
    (U : MorphismProperty.Over W ⊤ X) :
    𝟙 U.left ≫ U.hom =
      (((LocalizerMorphism.id W).sourceDenominators X).obj U).hom := sorry

/-- The identity component comparing the source-denominator action of the identity localizer
morphism with the identity functor. -/
def idComponent (W : MorphismProperty C₁) (X : C₁)
    (U : MorphismProperty.Over W ⊤ X) :
    ((LocalizerMorphism.id W).sourceDenominators X).obj U ≅ U :=
  MorphismProperty.Over.isoMk (Iso.refl U.left) (idComponent_comm W X U)

/-- Naturality of the source-denominator identity comparison components. -/
theorem idComponent_naturality (W : MorphismProperty C₁) (X : C₁)
    {U V : MorphismProperty.Over W ⊤ X} (f : U ⟶ V) :
    ((LocalizerMorphism.id W).sourceDenominators X).map f ≫
        (idComponent W X V).hom =
      (idComponent W X U).hom ≫ f := sorry

/-- The source-denominator action of the identity localizer morphism is canonically isomorphic to
the identity functor. -/
@[stacks 05T5 "identity comparison on source denominators"]
def idIso (W : MorphismProperty C₁) (X : C₁) :
    (LocalizerMorphism.id W).sourceDenominators X ≅
      𝟭 (MorphismProperty.Over W ⊤ X) :=
  NatIso.ofComponents (idComponent W X) (idComponent_naturality W X)

/-- The forward source-denominator identity comparison is the identity on source objects. -/
@[simp]
theorem idIso_hom_app_left (W : MorphismProperty C₁) (X : C₁)
    (U : MorphismProperty.Over W ⊤ X) :
    ((idIso W X).hom.app U).left = 𝟙 U.left := sorry

/-- The inverse source-denominator identity comparison is the identity on source objects. -/
@[simp]
theorem idIso_inv_app_left (W : MorphismProperty C₁) (X : C₁)
    (U : MorphismProperty.Over W ⊤ X) :
    ((idIso W X).inv.app U).left = 𝟙 U.left := sorry

/-- Compatibility of the identity component for the source-denominator composition
comparison. -/
theorem compComponent_comm (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    (U : MorphismProperty.Over W₁ ⊤ X) :
    𝟙 (Ψ.functor.obj (Φ.functor.obj U.left)) ≫
        (((Φ.comp Ψ).sourceDenominators X).obj U).hom =
      ((Φ.sourceDenominators X ⋙
          Ψ.sourceDenominators (Φ.functor.obj X)).obj U).hom := sorry

/-- The identity component comparing successive source-denominator actions with the action of a
composite localizer morphism. -/
def compComponent (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    (U : MorphismProperty.Over W₁ ⊤ X) :
    (Φ.sourceDenominators X ⋙
        Ψ.sourceDenominators (Φ.functor.obj X)).obj U ≅
      ((Φ.comp Ψ).sourceDenominators X).obj U :=
  MorphismProperty.Over.isoMk
    (Iso.refl (Ψ.functor.obj (Φ.functor.obj U.left)))
    (compComponent_comm Φ Ψ X U)

/-- Naturality of the source-denominator composition comparison components. -/
theorem compComponent_naturality (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    {U V : MorphismProperty.Over W₁ ⊤ X} (f : U ⟶ V) :
    (Φ.sourceDenominators X ⋙
          Ψ.sourceDenominators (Φ.functor.obj X)).map f ≫
        (compComponent Φ Ψ X V).hom =
      (compComponent Φ Ψ X U).hom ≫
        ((Φ.comp Ψ).sourceDenominators X).map f := sorry

/-- Successive source-denominator actions agree canonically with the action of the composite
localizer morphism. -/
@[stacks 05T5 "composition comparison on source denominators"]
def compIso (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁) :
    Φ.sourceDenominators X ⋙ Ψ.sourceDenominators (Φ.functor.obj X) ≅
      (Φ.comp Ψ).sourceDenominators X :=
  NatIso.ofComponents (compComponent Φ Ψ X)
    (compComponent_naturality Φ Ψ X)

/-- The forward source-denominator composition comparison is the identity on source objects. -/
@[simp]
theorem compIso_hom_app_left (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    (U : MorphismProperty.Over W₁ ⊤ X) :
    ((compIso Φ Ψ X).hom.app U).left =
      𝟙 (Ψ.functor.obj (Φ.functor.obj U.left)) := sorry

/-- The inverse source-denominator composition comparison is the identity on source objects. -/
@[simp]
theorem compIso_inv_app_left (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₃) (X : C₁)
    (U : MorphismProperty.Over W₁ ⊤ X) :
    ((compIso Φ Ψ X).inv.app U).left =
      𝟙 (Ψ.functor.obj (Φ.functor.obj U.left)) := sorry

end CategoryTheory.LocalizerMorphism.sourceDenominators
