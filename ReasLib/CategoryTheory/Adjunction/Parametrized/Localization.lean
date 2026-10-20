/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Parametrized Adjunctions Along a Localization

A parametrized adjunction descends when both functors in its parameter are equipped with
localization liftings.  This leaf owns the representative choice, the pointwise transport,
and the computation on objects coming from the source category.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe vC vD vA vB uC uD uA uB

namespace CategoryTheory.ParametrizedAdjunction

variable {C : Type uC} {D : Type uD} {A : Type uA} {B : Type uB}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vA} A] [Category.{vB} B]
variable {L : C ⥤ D} {W : MorphismProperty C}
variable [L.IsLocalization W]
variable {F : C ⥤ A ⥤ B} {G : Cᵒᵖ ⥤ B ⥤ A}
variable {F' : D ⥤ A ⥤ B} {G' : Dᵒᵖ ⥤ B ⥤ A}
variable [Localization.Lifting L W F F']
variable [Localization.Lifting L.op W.op G G']

/-- The pointwise adjunction obtained by transporting a parametrized adjunction along chosen
localization liftings in its parameter. -/
@[stacks 05SE "pointwise parametrized adjunction along a localization"]
noncomputable def localizationAt (adj₂ : F ⊣₂ G) (K : D) :
    F'.obj K ⊣ G'.obj (op K) :=
  -- Local instance justification (proof-local temporary data): Mathlib exposes
  -- localization essential surjectivity as a theorem rather than a global
  -- instance, so only this representative choice needs the temporary pin.
  letI := Localization.essSurj L W
  let X := L.objPreimage K
  let e := L.objObjPreimageIso K
  ((adj₂.adj X).ofNatIsoLeft
      ((Localization.Lifting.iso L W F F').symm.app X ≪≫
        F'.mapIso e)).ofNatIsoRight
    ((Localization.Lifting.iso L.op W.op G G').symm.app (op X) ≪≫
      G'.mapIso e.symm.op)

/-- The transported Hom equivalences are natural in the localized parameter. -/
@[stacks 05SE "naturality of a parametrized adjunction along a localization"]
theorem localizationAt_naturality (adj₂ : F ⊣₂ G)
    {K K' : D} (f : K ⟶ K') {X : A} {Y : B}
    (g : (F'.obj K').obj X ⟶ Y) :
    (localizationAt (L := L) (W := W) (F' := F') (G' := G')
        adj₂ K).homEquiv X Y ((F'.map f).app X ≫ g) =
      (localizationAt (L := L) (W := W) (F' := F') (G' := G')
          adj₂ K').homEquiv X Y g ≫ (G'.map f.op).app Y := sorry

/-- A parametrized adjunction descends along a localization of its parameter when both
parameter functors are equipped with localization liftings. -/
@[stacks 05SE "parametrized adjunction along a localization"]
noncomputable def localization (adj₂ : F ⊣₂ G) : F' ⊣₂ G' :=
  ParametrizedAdjunction.mk'
    (localizationAt (L := L) (W := W) (F' := F') (G' := G') adj₂)
    (localizationAt_naturality
      (L := L) (W := W) (F' := F') (G' := G') adj₂)

/-- On an object in the image of the localization, the pointwise adjunction is the original
one transported by the two lifting comparisons. -/
@[stacks 05SE "parametrized adjunction on a localization image"]
noncomputable def localizationOnImage (adj₂ : F ⊣₂ G) (X : C) :
    F'.obj (L.obj X) ⊣ G'.obj (op (L.obj X)) :=
  ((adj₂.adj X).ofNatIsoLeft
      ((Localization.Lifting.iso L W F F').symm.app X)).ofNatIsoRight
    ((Localization.Lifting.iso L.op W.op G G').symm.app (op X))

/-- Currying through `localizationOnImage` is currying before localization, conjugated by
the two lifting comparisons. -/
@[simp, stacks 05SE "currying on the image of a localized parameter"]
theorem localizationOnImage_homEquiv_apply (adj₂ : F ⊣₂ G) (X : C)
    (X₂ : A) (X₃ : B) (f : (F'.obj (L.obj X)).obj X₂ ⟶ X₃) :
    (localizationOnImage
      (L := L) (W := W) (F' := F') (G' := G') adj₂ X).homEquiv X₂ X₃ f =
        (adj₂.adj X).homEquiv X₂ X₃
            (((Localization.Lifting.iso L W F F').inv.app X).app X₂ ≫ f) ≫
          ((Localization.Lifting.iso L.op W.op G G').inv.app (op X)).app X₃ := sorry

/-- Uncurrying through `localizationOnImage` is uncurrying before localization, conjugated
by the two lifting comparisons. -/
@[simp, stacks 05SE "uncurrying on the image of a localized parameter"]
theorem localizationOnImage_homEquiv_symm_apply (adj₂ : F ⊣₂ G) (X : C)
    (X₂ : A) (X₃ : B) (g : X₂ ⟶ (G'.obj (op (L.obj X))).obj X₃) :
    ((localizationOnImage
      (L := L) (W := W) (F' := F') (G' := G') adj₂ X).homEquiv X₂ X₃).symm g =
        ((Localization.Lifting.iso L W F F').hom.app X).app X₂ ≫
          ((adj₂.adj X).homEquiv X₂ X₃).symm
            (g ≫ ((Localization.Lifting.iso L.op W.op G G').hom.app (op X)).app X₃) := sorry

/-- The descended parametrized adjunction computes on objects in the image of the
localization. -/
@[stacks 05SE "computation of a localized parametrized adjunction"]
theorem localization_adj (adj₂ : F ⊣₂ G) (X : C) :
    (localization (L := L) (W := W) (F' := F') (G' := G') adj₂).adj
        (L.obj X) =
      localizationOnImage
        (L := L) (W := W) (F' := F') (G' := G') adj₂ X := sorry

end CategoryTheory.ParametrizedAdjunction
