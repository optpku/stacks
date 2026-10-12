/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Computation
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory

@[expose] public section

/-!
# Comparison for Localizations of Full Subcategories

This leaf specializes the generic localizer-morphism computation API to a full-subcategory
inclusion.  Its statements expose underlying ambient morphisms directly, so downstream users do
not need to unfold the inclusion or the induced localization functor.
-/

noncomputable section

universe v u

namespace CategoryTheory

open Localization ObjectProperty

variable {D : Type u} [Category.{v} D]
  (P : ObjectProperty D) (S : MorphismProperty D)

namespace fullSubcategoryLocalizationFunctor

/-- Stacks 0GSL: the canonical comparison between localizing the full-subcategory inclusion
before and after passing to the induced functor on localizations. -/
@[stacks 0GSL "comparison for a localized full-subcategory inclusion"]
noncomputable abbrev facIso :
    P.ι ⋙ S.Q ≅
      (fullSubcategoryLocalizationSystem P S).Q ⋙
        fullSubcategoryLocalizationFunctor P S :=
  (fullSubcategoryLocalizerMorphism P S).facIso
    (fullSubcategoryLocalizationSystem P S).Q S.Q

namespace facIso

/-- Naturality of the forward full-subcategory localization comparison on an underlying
subcategory morphism. -/
@[reassoc (attr := simp), stacks 0GSL]
theorem hom_naturality {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    S.Q.map f.hom ≫ (facIso P S).hom.app Y =
      (facIso P S).hom.app X ≫
        (fullSubcategoryLocalizationFunctor P S).map
          ((fullSubcategoryLocalizationSystem P S).Q.map f) := sorry

/-- Naturality of the inverse full-subcategory localization comparison on an underlying
subcategory morphism. -/
@[reassoc (attr := simp), stacks 0GSL]
theorem inv_naturality {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    (fullSubcategoryLocalizationFunctor P S).map
          ((fullSubcategoryLocalizationSystem P S).Q.map f) ≫
        (facIso P S).inv.app Y =
      (facIso P S).inv.app X ≫ S.Q.map f.hom := sorry

end facIso

/-- Stacks 0GSL: the induced localization functor maps an arrow from the restricted quotient by
conjugating the ambient localized arrow with the canonical comparison. -/
@[simp, reassoc (attr := simp), stacks 0GSL]
theorem map_Q {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    (fullSubcategoryLocalizationFunctor P S).map
        ((fullSubcategoryLocalizationSystem P S).Q.map f) =
      (facIso P S).inv.app X ≫ S.Q.map f.hom ≫ (facIso P S).hom.app Y := sorry

end fullSubcategoryLocalizationFunctor

end CategoryTheory
