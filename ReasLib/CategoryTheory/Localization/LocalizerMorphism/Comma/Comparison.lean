/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Computation
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Denominator.Comma

/-!
# Comparing denominator and localization comma functors

The ordinary denominator functors and the localization comma functors induced by a localizer
morphism commute up to canonical natural isomorphism.  These isomorphisms are the bridge used to
transport finality, essential constancy, and pointwise (co)limit formulas without unfolding the
localization comparison square.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace targetDenominators

/-- Compatibility needed for the identity-source comparison between the two ways of mapping a
target denominator to the target localization comma category. -/
theorem commaComponent_comm (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : MorphismProperty.Under W₁ ⊤ X) :
    W₂.Q.map (𝟙 (Φ.functor.obj U.right)) ≫
        ((MorphismProperty.Under.toCostructuredArrow W₁ X ⋙
          Φ.costructuredArrow X).obj U).hom =
      ((Φ.targetDenominators X ⋙
          MorphismProperty.Under.toCostructuredArrow W₂ (Φ.functor.obj X)).obj U).hom := sorry

/-- The component comparing the two ways of mapping a target denominator to the target
localization comma category. -/
noncomputable def commaComponent (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : MorphismProperty.Under W₁ ⊤ X) :
    (Φ.targetDenominators X ⋙
        MorphismProperty.Under.toCostructuredArrow W₂ (Φ.functor.obj X)).obj U ≅
      (MorphismProperty.Under.toCostructuredArrow W₁ X ⋙
        Φ.costructuredArrow X).obj U :=
  CostructuredArrow.isoMk (Iso.refl _) (commaComponent_comm Φ X U)

/-- Naturality of the target-denominator localization comma comparison components. -/
theorem commaComponent_naturality (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {U V : MorphismProperty.Under W₁ ⊤ X} (f : U ⟶ V) :
    (Φ.targetDenominators X ⋙
          MorphismProperty.Under.toCostructuredArrow W₂ (Φ.functor.obj X)).map f ≫
        (commaComponent Φ X V).hom =
      (commaComponent Φ X U).hom ≫
        (MorphismProperty.Under.toCostructuredArrow W₁ X ⋙
          Φ.costructuredArrow X).map f := sorry

/-- Mapping target denominators and then entering the target localization comma category agrees
with first entering the source localization comma category and applying the induced comma
functor. -/
@[stacks 05T5 "target-denominator localization comma comparison"]
noncomputable def commaIso (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    Φ.targetDenominators X ⋙
        MorphismProperty.Under.toCostructuredArrow W₂ (Φ.functor.obj X) ≅
      MorphismProperty.Under.toCostructuredArrow W₁ X ⋙
        Φ.costructuredArrow X :=
  NatIso.ofComponents (commaComponent Φ X) (commaComponent_naturality Φ X)

/-- The target-denominator comma comparison is the identity on source objects. -/
@[simp]
theorem commaIso_hom_app_left (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : MorphismProperty.Under W₁ ⊤ X) :
    ((commaIso Φ X).hom.app U).left = 𝟙 (Φ.functor.obj U.right) := sorry

/-- The inverse target-denominator comma comparison is the identity on source objects. -/
@[simp]
theorem commaIso_inv_app_left (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : MorphismProperty.Under W₁ ⊤ X) :
    ((commaIso Φ X).inv.app U).left = 𝟙 (Φ.functor.obj U.right) := sorry

end targetDenominators

namespace sourceDenominators

/-- Compatibility needed for the identity-target comparison between the two ways of mapping a
source denominator to the target localization comma category. -/
theorem commaComponent_comm (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : MorphismProperty.Over W₁ ⊤ X) :
    ((Φ.sourceDenominators X ⋙
          MorphismProperty.Over.toStructuredArrow W₂ (Φ.functor.obj X)).obj U).hom ≫
        W₂.Q.map (𝟙 (Φ.functor.obj U.left)) =
      ((MorphismProperty.Over.toStructuredArrow W₁ X ⋙
          Φ.structuredArrow X).obj U).hom := sorry

/-- The component comparing the two ways of mapping a source denominator to the target
localization comma category. -/
noncomputable def commaComponent (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : MorphismProperty.Over W₁ ⊤ X) :
    (Φ.sourceDenominators X ⋙
        MorphismProperty.Over.toStructuredArrow W₂ (Φ.functor.obj X)).obj U ≅
      (MorphismProperty.Over.toStructuredArrow W₁ X ⋙
        Φ.structuredArrow X).obj U :=
  StructuredArrow.isoMk (Iso.refl _) (commaComponent_comm Φ X U)

/-- Naturality of the source-denominator localization comma comparison components. -/
theorem commaComponent_naturality (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    {U V : MorphismProperty.Over W₁ ⊤ X} (f : U ⟶ V) :
    (Φ.sourceDenominators X ⋙
          MorphismProperty.Over.toStructuredArrow W₂ (Φ.functor.obj X)).map f ≫
        (commaComponent Φ X V).hom =
      (commaComponent Φ X U).hom ≫
        (MorphismProperty.Over.toStructuredArrow W₁ X ⋙
          Φ.structuredArrow X).map f := sorry

/-- Mapping source denominators and then entering the target localization comma category agrees
with first entering the source localization comma category and applying the induced comma
functor. -/
@[stacks 05T5 "source-denominator localization comma comparison"]
noncomputable def commaIso (Φ : LocalizerMorphism W₁ W₂) (X : C₁) :
    Φ.sourceDenominators X ⋙
        MorphismProperty.Over.toStructuredArrow W₂ (Φ.functor.obj X) ≅
      MorphismProperty.Over.toStructuredArrow W₁ X ⋙
        Φ.structuredArrow X :=
  NatIso.ofComponents (commaComponent Φ X) (commaComponent_naturality Φ X)

/-- The source-denominator comma comparison is the identity on target objects. -/
@[simp]
theorem commaIso_hom_app_right (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : MorphismProperty.Over W₁ ⊤ X) :
    ((commaIso Φ X).hom.app U).right = 𝟙 (Φ.functor.obj U.left) := sorry

/-- The inverse source-denominator comma comparison is the identity on target objects. -/
@[simp]
theorem commaIso_inv_app_right (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    (U : MorphismProperty.Over W₁ ⊤ X) :
    ((commaIso Φ X).inv.app U).right = 𝟙 (Φ.functor.obj U.left) := sorry

end sourceDenominators



end CategoryTheory.LocalizerMorphism
