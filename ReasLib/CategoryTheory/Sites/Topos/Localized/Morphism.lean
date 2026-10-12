/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.Representable.BaseChange
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.Localized.BaseChange

/-!
# Localized morphisms of sites

This leaf records the base-change comparisons for the localized morphism of
topoi attached to a morphism of sites.  The underlying continuous statements
live in the neighboring base-change files; the API here retains the stronger
morphism-of-sites hypothesis used by applications.
-/

@[expose] public section

open CategoryTheory Limits
open GrothendieckTopology.RepresentableLocalization

universe w u u₁ u₂ v v₁ v₂

namespace CategoryTheory.Functor.Localized

section Pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [IsMorphismOfSites JD JC u]
variable {V : D} {U : C} (c : U ⟶ u.obj V)
variable [HasWeakSheafify JD (Type w)] [HasWeakSheafify JC (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify (JD.over V) (Type w)]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.forget V).op.HasLeftKanExtension P]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type w)]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((Over.post u).sheafPullback (Type w) (JD.over V) (JC.over (u.obj V)))]
variable [HasSheafify (JC.over U) (Type w)]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension P]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.map c).op.HasPointwiseRightKanExtension P]

/-- Localizing the inverse image of a morphism of sites commutes with the two
slice lower-shriek functors. -/
@[stacks 04IN "(1)"]
theorem inverseImageOverPullback_of_morphism :
    IsIsomorphic
      (u.sheafPullback (Type w) JD JC ⋙ JC.overPullback (Type w) U)
      (JD.overPullback (Type w) V ⋙ (u.localizedMorphismOfTopoi c).inverseImage) := sorry

end Pullback

section Representable

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [IsMorphismOfSites JD JC u]
variable {V : D} {U : C} (c : U ⟶ u.obj V)
variable [HasWeakSheafify JD (Type (max u v))]
variable [HasWeakSheafify JC (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u.op.HasLeftKanExtension P]
variable [HasWeakSheafify (JD.over V) (Type (max u v))]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.forget V).op.HasLeftKanExtension P]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type (max u v))]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.post u).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((Over.post u).sheafPullback (Type (max u v)) (JD.over V) (JC.over (u.obj V)))]
variable [HasSheafify (JC.over U) (Type (max u v))]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension P]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.map c).op.HasPointwiseRightKanExtension P]

/-- Under representable localization, the inverse image of a localized morphism of sites is
pullback along the canonical representable base-change map. -/
@[stacks 04IN "(2)"]
theorem representableInverseImage_of_morphism :
    IsIsomorphic
      ((u.localizedMorphismOfTopoi c).inverseImage ⋙ comparison JC U)
      (comparison JD V ⋙ Over.post (u.sheafPullback (Type (max u v)) JD JC) ⋙
        Over.pullback
          (JC.sheafifiedRepresentableMap c ≫
            SheafifiedRepresentable.pullbackComparison u JD JC V)) := sorry

end Representable

section Naturality

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [IsMorphismOfSites JD JC u]
variable {V V' : D} {U U' : C}
variable (c : U ⟶ u.obj V) (b : V' ⟶ V) (a : U' ⟶ U)
variable (c' : U' ⟶ u.obj V') (hcomm : c' ≫ u.map b = a ≫ c)
variable [HasWeakSheafify (JC.over (u.obj V)) (Type w)]
variable [HasWeakSheafify (JC.over (u.obj V')) (Type w)]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [∀ P : (Over V')ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((Over.post u).sheafPullback (Type w) (JD.over V) (JC.over (u.obj V)))]
variable [PreservesFiniteLimits
  ((Over.post u).sheafPullback (Type w) (JD.over V') (JC.over (u.obj V')))]
variable [HasSheafify (JC.over U) (Type w)] [HasSheafify (JC.over U') (Type w)]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.map c).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over U')ᵒᵖ ⥤ Type w, (Over.map c').op.HasPointwiseRightKanExtension P]

/-- A commutative square of localization parameters induces the corresponding square of
localized inverse-image functors for a morphism of sites. -/
@[stacks 04IN "(3)"]
theorem inverseImageOverMapPullback_of_morphism :
    IsIsomorphic
      ((u.localizedMorphismOfTopoi c).inverseImage ⋙ JC.overMapPullback (Type w) a)
      (JD.overMapPullback (Type w) b ⋙ (u.localizedMorphismOfTopoi c').inverseImage) := sorry

end Naturality

end CategoryTheory.Functor.Localized
