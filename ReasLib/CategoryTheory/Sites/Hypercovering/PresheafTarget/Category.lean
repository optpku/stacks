/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.InducedCategory
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.LocalHypercover

/-!
# Morphisms of presheaf-target hypercoverings

Hypercoverings of a fixed presheaf form the induced subcategory of the costructured-arrow
category whose objects are their augmentations.  Consequently a morphism is a simplicial map of
semi-representable families whose induced presheaf map commutes with the augmentations.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

namespace HypercoveringOf

/-- Applying `Limits.FormalCoproduct.toPresheaf` degreewise to a simplicial
semi-representable family. -/
abbrev simplicialPresheafFunctor :
    SimplicialObject (SR(C)) ⥤ SimplicialObject (Cᵒᵖ ⥤ Type (max w v)) :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ (SR(C))
    (Cᵒᵖ ⥤ Type (max w v))).obj Limits.FormalCoproduct.toPresheaf

/-- The augmentation of a hypercovering, regarded as an object of the costructured-arrow
category over the constant simplicial target. -/
abbrev toCostructuredArrow (K : HypercoveringOf J 𝒢) :
    CostructuredArrow simplicialPresheafFunctor
      ((SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :=
  CostructuredArrow.mk K.augmentation

/-- Hypercoverings of a fixed presheaf inherit the category whose arrows are
augmentation-preserving simplicial maps. -/
instance instCategory : Category (HypercoveringOf J 𝒢) :=
  inferInstanceAs <| Category
    (InducedCategory
      (CostructuredArrow simplicialPresheafFunctor
        ((SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢))
      fun K : HypercoveringOf J 𝒢 ↦ K.toCostructuredArrow)

/-- The fully faithful functor sending a hypercovering to its augmentation. -/
abbrev forget : HypercoveringOf J 𝒢 ⥤
    CostructuredArrow simplicialPresheafFunctor
      ((SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj 𝒢) :=
  inducedFunctor fun K : HypercoveringOf J 𝒢 ↦ K.toCostructuredArrow

/-- Build a hypercovering morphism from a simplicial map compatible with the two
augmentations. -/
abbrev homMk {K L : HypercoveringOf J 𝒢}
    (f : K.simplicial ⟶ L.simplicial)
    (comm : simplicialPresheafFunctor.map f ≫ L.augmentation = K.augmentation) : K ⟶ L :=
  InducedCategory.homMk (CostructuredArrow.homMk f comm)

namespace Hom

/-- The simplicial map of semi-representable families underlying a hypercovering morphism. -/
abbrev toSimplicial {K L : HypercoveringOf J 𝒢} (f : K ⟶ L) :
    K.simplicial ⟶ L.simplicial :=
  (HypercoveringOf.forget.map f).left

/-- The simplicial presheaf map underlying a hypercovering morphism. -/
abbrev toSimplicialPresheaf {K L : HypercoveringOf J 𝒢} (f : K ⟶ L) :
    hypercoveringPresheaf K.simplicial ⟶ hypercoveringPresheaf L.simplicial :=
  simplicialPresheafFunctor.map (Hom.toSimplicial f)

/-- The presheaf map underlying a hypercovering morphism commutes with the augmentations. -/
@[reassoc]
theorem augmentation_naturality {K L : HypercoveringOf J 𝒢} (f : K ⟶ L) :
    Hom.toSimplicialPresheaf f ≫ L.augmentation = K.augmentation := sorry

end Hom

/-- Hypercovering morphisms are determined by their underlying simplicial maps. -/
@[ext]
theorem hom_ext {K L : HypercoveringOf J 𝒢} {f g : K ⟶ L}
    (h : Hom.toSimplicial f = Hom.toSimplicial g) : f = g := sorry

/-- The simplicial map underlying `homMk` is the supplied map. -/
@[simp]
theorem homMk_toSimplicial {K L : HypercoveringOf J 𝒢}
    (f : K.simplicial ⟶ L.simplicial)
    (comm : simplicialPresheafFunctor.map f ≫ L.augmentation = K.augmentation) :
    Hom.toSimplicial (homMk f comm) = f := sorry

end HypercoveringOf

end CategoryTheory
