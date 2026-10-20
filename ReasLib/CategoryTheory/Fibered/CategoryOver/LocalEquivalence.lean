/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Local
public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf.Extension
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.LocalEquivalence

/-!
# Local equivalences of fibered categories

This module exposes the fixed-universe view of
`CartesianBasedFunctor.IsLocalEquivalence`. Its Homwise and essential-image halves are the
fixed-universe views `Homwise.IsLocalEquivalence` and `LocallyEssentiallySurjective` of the same
cartesian-functor owners, so the defining criterion holds by definition. Stack and
stackification hypotheses remain absent from this layer.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Hom

variable {X Y Z : FiberedCategoryOver.{u, v, w, vS} C}

/-- The fixed-universe view of the heterogeneous cartesian-functor local-equivalence owner. -/
@[stacks 02ZP "fixed-universe local-equivalence predicate"]
abbrev IsLocalEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.IsLocalEquivalence J
    (FiberedCategoryOver.toCartesianBasedFunctor F)

/-- The heterogeneous owner specializes to the fixed-universe Homwise and essential-image
conditions. -/
@[stacks 02ZP "fixed-universe local-equivalence criterion"]
theorem isLocalEquivalence_iff
    (J : GrothendieckTopology C) (F : X ⟶ Y) :
    IsLocalEquivalence J F ↔
      Homwise.IsLocalEquivalence J F ∧
        LocallyEssentiallySurjective J F := Iff.rfl

/-- A local equivalence is a local equivalence on all Hom-presheaves. -/
@[stacks 02ZP "fixed-universe Homwise local-equivalence projection"]
theorem IsLocalEquivalence.isHomwise
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : IsLocalEquivalence J F) :
    Homwise.IsLocalEquivalence J F := hF.1

/-- A local equivalence is locally essentially surjective on fiber objects. -/
@[stacks 02ZP "fixed-universe essential-image projection"]
theorem IsLocalEquivalence.locallyEssentiallySurjective
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : IsLocalEquivalence J F) :
    LocallyEssentiallySurjective J F := hF.2

/-- The canonical Hom-presheaf map of a local equivalence belongs to the
localizing class of the corresponding slice site. -/
@[stacks 02ZP "fixed-universe Hom-presheaf localizing-class projection"]
theorem IsLocalEquivalence.presheafHomMap_mem
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : IsLocalEquivalence J F) {U : C} (x y : X.p.Fiber U) :
    (J.over U).W (presheafHomMap F x y) := sorry

/-- The identity morphism of a fibered category is a local equivalence. -/
@[stacks 02ZP "identity fixed-universe local equivalence"]
theorem IsLocalEquivalence.id (J : GrothendieckTopology C) :
    IsLocalEquivalence J (𝟙 X) := sorry

/-- Local equivalences of fibered categories are closed under composition. -/
@[stacks 02ZP "composition of fixed-universe local equivalences"]
theorem IsLocalEquivalence.comp
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : IsLocalEquivalence J F) (hG : IsLocalEquivalence J G) :
    IsLocalEquivalence J (F ≫ G) := sorry

/-- An equivalence over the base is a local equivalence. -/
@[stacks 02ZP "equivalence over the base gives a local equivalence"]
theorem IsLocalEquivalence.of_isEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    IsLocalEquivalence J F := sorry

/-- Precomposition by an equivalence over the base preserves local equivalence. -/
@[stacks 02ZP "left-equivalence transport of local equivalence"]
theorem IsLocalEquivalence.comp_left_of_isEquivalence
    {J : GrothendieckTopology C} (E : X ⟶ Y)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence)
    (G : Y ⟶ Z) (hG : IsLocalEquivalence J G) :
    IsLocalEquivalence J (E ≫ G) := sorry

/-- Postcomposition by an equivalence over the base preserves local equivalence. -/
@[stacks 02ZP "right-equivalence transport of local equivalence"]
theorem IsLocalEquivalence.comp_right_of_isEquivalence
    {J : GrothendieckTopology C} (F : X ⟶ Y)
    (hF : IsLocalEquivalence J F) (E : Y ⟶ Z)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence) :
    IsLocalEquivalence J (F ≫ E) := sorry

/-- Local equivalence reflects across postcomposition by an equivalence over the base. -/
@[stacks 02ZP "right-equivalence reflection of local equivalence"]
theorem IsLocalEquivalence.of_comp_right_isEquivalence
    {J : GrothendieckTopology C} (F : X ⟶ Y) (E : Y ⟶ Z)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence)
    (hFE : IsLocalEquivalence J (F ≫ E)) :
    IsLocalEquivalence J F := sorry

/-- Transport local equivalence along an isomorphism of parallel morphisms of
fibered categories. -/
@[stacks 02ZP "isomorphism transport of local equivalence"]
theorem IsLocalEquivalence.of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G)
    (hF : IsLocalEquivalence J F) :
    IsLocalEquivalence J G := sorry

/-- Isomorphic parallel morphisms of fibered categories are local equivalences
simultaneously. -/
@[stacks 02ZP "isomorphism invariance of local equivalence"]
theorem isLocalEquivalence_iff_of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G) :
    IsLocalEquivalence J F ↔ IsLocalEquivalence J G := sorry

end FiberedCategoryOver.Hom

end CategoryTheory
