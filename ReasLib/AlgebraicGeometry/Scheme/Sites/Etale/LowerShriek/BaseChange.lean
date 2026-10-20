/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.FactorThru
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Abelian

/-!
# Base change for direct image with compact support

The ordinary base-change mate restricts to a comparison on compactly supported
sections. This comparison is invertible for a cartesian square of schemes with
separated, locally finite-type vertical morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [IsSeparated f] [LocallyOfFiniteType f]

/-- The ordinary base-change mate composed with inverse image of the
compact-support inclusion. -/
def etaleLowerShriekBaseChangeToPushforward :
    etaleLowerShriek f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ abelianPushforwardAlong f' :=
  whiskerRight (etaleLowerShriekι f) (etaleAbelianSheafPullback g) ≫
    AlgebraicGeometry.Scheme.Hom.underivedBaseChange f g f' g' h_cart

section

variable [IsSeparated f'] [LocallyOfFiniteType f']

/-- The ordinary base-change image of an inverse-image compact-support section
has proper support over the new base. -/
theorem etaleLowerShriekBaseChange_mem
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y'.Etale)
    (σ : ((etaleAbelianSheafPullback g).obj ((etaleLowerShriek f).obj F)).obj.obj
      (op V)) :
    (((etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart).app F).hom.app
      (op V)) σ ∈ compactSupportSections f' ((etaleAbelianSheafPullback g').obj F) V :=
  sorry

/-- Base change on sections, with its image restricted to the subgroup of
sections with proper support over the new base. -/
def etaleLowerShriekBaseChangeSectionMap
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y'.Etale) :
    ((etaleAbelianSheafPullback g).obj ((etaleLowerShriek f).obj F)).obj.obj (op V) →+
      compactSupportSections f' ((etaleAbelianSheafPullback g').obj F) V :=
  ((((etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart).app F).hom.app
    (op V)).hom).codRestrict
      (compactSupportSections f' ((etaleAbelianSheafPullback g').obj F) V)
      (etaleLowerShriekBaseChange_mem f g f' g' h_cart F V)

/-- The compact-support base-change section maps commute with restriction on
the small étale site of the new base. -/
theorem etaleLowerShriekBaseChange_sections_naturality
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V W : Y'.Etaleᵒᵖ} (a : V ⟶ W) :
    ((etaleAbelianSheafPullback g).obj ((etaleLowerShriek f).obj F)).obj.map a ≫
        AddCommGrpCat.ofHom
          (etaleLowerShriekBaseChangeSectionMap f g f' g' h_cart F W.unop) =
      AddCommGrpCat.ofHom
          (etaleLowerShriekBaseChangeSectionMap f g f' g' h_cart F V.unop) ≫
        (etaleLowerShriekPresheaf f' ((etaleAbelianSheafPullback g').obj F)).map a :=
  sorry

/-- The compact-support base-change morphism at an abelian étale sheaf. -/
def etaleLowerShriekBaseChange_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).obj ((etaleLowerShriek f).obj F) ⟶
      (etaleLowerShriek f').obj ((etaleAbelianSheafPullback g').obj F) :=
  ObjectProperty.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom
        (etaleLowerShriekBaseChangeSectionMap f g f' g' h_cart F V.unop)
      naturality := fun _ _ a ↦
        etaleLowerShriekBaseChange_sections_naturality f g f' g' h_cart F a }

/-- Compact-support base change is natural in the abelian coefficient sheaf. -/
theorem etaleLowerShriekBaseChange_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    (etaleLowerShriek f ⋙ etaleAbelianSheafPullback g).map α ≫
        etaleLowerShriekBaseChange_app f g f' g' h_cart G =
      etaleLowerShriekBaseChange_app f g f' g' h_cart F ≫
        (etaleAbelianSheafPullback g' ⋙ etaleLowerShriek f').map α :=
  sorry

/-- The canonical comparison from inverse image of compact-support direct
image to compact-support direct image of inverse image. -/
def etaleLowerShriekBaseChange :
    etaleLowerShriek f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ etaleLowerShriek f' where
  app := etaleLowerShriekBaseChange_app f g f' g' h_cart
  naturality := fun _ _ α ↦ etaleLowerShriekBaseChange_naturality f g f' g' h_cart α

/-- Whiskering the compact-support inclusion by inverse image on its source
preserves its monicity. -/
instance etaleLowerShriekι_whiskerLeft_mono :
    Mono (whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f')) :=
  sorry

/-- The compact-support comparison followed by the compact-support inclusion
is ordinary base change restricted to inverse image of compact-support direct image. -/
theorem etaleLowerShriekBaseChange_ι :
    etaleLowerShriekBaseChange f g f' g' h_cart ≫
        whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f') =
      etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart :=
  sorry

/-- Ordinary base change on inverse image of compact-support direct image
factors through compact-support direct image on the new base. -/
theorem etaleLowerShriekBaseChange_factors :
    MonoOver.Factors
      (MonoOver.mk
        (whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f')))
      (etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart) :=
  ⟨etaleLowerShriekBaseChange f g f' g' h_cart,
    etaleLowerShriekBaseChange_ι f g f' g' h_cart⟩

/-- A morphism whose composite with the compact-support inclusion is the
restricted ordinary base-change mate equals the compact-support comparison. -/
theorem etaleLowerShriekBaseChange_lift_unique
    (α : etaleLowerShriek f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ etaleLowerShriek f')
    (hα : α ≫ whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f') =
      etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart) :
    α = etaleLowerShriekBaseChange f g f' g' h_cart :=
  sorry

/-- The compact-support base-change comparison for a cartesian square is invertible. -/
instance etaleLowerShriekBaseChange_isIso :
    IsIso (etaleLowerShriekBaseChange f g f' g' h_cart) :=
  sorry

end

/-- In a cartesian square with separated locally finite-type vertical morphism,
inverse image commutes with direct image with compact support. -/
theorem etaleLowerShriekBaseChange_isIso_of_isPullback :
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of f' from f; it is not an additional assumption.
    letI : IsSeparated f' :=
      MorphismProperty.of_isPullback (P := @IsSeparated) h_cart inferInstance
    -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of f' from f; it is not an additional assumption.
    letI : LocallyOfFiniteType f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_cart inferInstance
    IsIso (etaleLowerShriekBaseChange f g f' g' h_cart) := by
  -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of f' from f; it is not an additional assumption.
  letI : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) h_cart inferInstance
  -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of f' from f; it is not an additional assumption.
  letI : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_cart inferInstance
  exact etaleLowerShriekBaseChange_isIso f g f' g' h_cart

end AlgebraicGeometry.Scheme.Etale

end
