/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Basic

@[expose] public section

/-!
# Localizing Full Subcategories

This leaf owns the restriction of a morphism property to the full subcategory cut out by an
object property, together with the canonical comparison functor on localizations.  It is stated
for arbitrary categories and morphism properties, so applications to derived functors and
triangulated categories need not own parallel copies of this data.
-/

universe v u

namespace CategoryTheory

open Localization MorphismProperty ObjectProperty

variable {D : Type u} [Category.{v} D]
  (P : ObjectProperty D) (S : MorphismProperty D)

/-- The morphism property on `P.FullSubcategory` obtained by restricting `S` along the
inclusion `P.ι`. -/
@[stacks 0GSL]
abbrev fullSubcategoryLocalizationSystem : MorphismProperty P.FullSubcategory :=
  S.inverseImage P.ι

namespace fullSubcategoryLocalizationSystem

/-- Membership in the localization system restricted to a full subcategory is membership of
the underlying ambient morphism. -/
@[simp, stacks 0GSL "membership in a restricted localization system"]
theorem mem_iff {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    fullSubcategoryLocalizationSystem P S f ↔ S f.hom := sorry

end fullSubcategoryLocalizationSystem

/-- The localizer morphism induced by the inclusion `P.ι : P.FullSubcategory ⥤ D`. -/
@[stacks 0GSL]
abbrev fullSubcategoryLocalizerMorphism :
    LocalizerMorphism (fullSubcategoryLocalizationSystem P S) S :=
  LocalizerMorphism.ofEq rfl

namespace fullSubcategoryLocalizerMorphism.functor

/-- The functor underlying a full-subcategory localizer morphism is full. -/
instance full : (fullSubcategoryLocalizerMorphism P S).functor.Full := sorry

/-- The functor underlying a full-subcategory localizer morphism is faithful. -/
instance faithful : (fullSubcategoryLocalizerMorphism P S).functor.Faithful := sorry

end fullSubcategoryLocalizerMorphism.functor

/-- The canonical functor from the localization of the restricted full subcategory to the
localization of the ambient category. -/
@[stacks 0GSL]
noncomputable abbrev fullSubcategoryLocalizationFunctor :
    (fullSubcategoryLocalizationSystem P S).Localization ⥤ S.Localization :=
  (fullSubcategoryLocalizerMorphism P S).localizedFunctor
    (fullSubcategoryLocalizationSystem P S).Q S.Q

end CategoryTheory
