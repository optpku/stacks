module

public import ReasLib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Topos.Localized

/-!
# Base change for localized morphisms of topoi

This leaf owns the inverse-image comparisons for the morphism of localized
topoi induced by a continuous functor and a morphism into its image.  It is
independent of representable-localization equivalences.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor.Localized

section Pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [u.IsContinuous JD JC]
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

/-- Localizing a continuous inverse image at `c : U ⟶ u.obj V` commutes with the two slice
lower-shriek functors. -/
theorem inverseImageOverPullback :
    IsIsomorphic
      (u.sheafPullback (Type w) JD JC ⋙ JC.overPullback (Type w) U)
      (JD.overPullback (Type w) V ⋙ (u.localizedMorphismOfTopoi c).inverseImage) := sorry

end Pullback

section Naturality

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C)
variable {V V' : D} {U U' : C}
variable (c : U ⟶ u.obj V) (b : V' ⟶ V) (a : U' ⟶ U)
variable (c' : U' ⟶ u.obj V') (hcomm : c' ≫ u.map b = a ≫ c)
variable [HasWeakSheafify (JC.over (u.obj V)) (Type w)]
variable [HasWeakSheafify (JC.over (u.obj V')) (Type w)]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [∀ P : (Over V')ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [(Over.post u).IsContinuous (JD.over V) (JC.over (u.obj V))]
variable [(Over.post u).IsContinuous (JD.over V') (JC.over (u.obj V'))]
variable [PreservesFiniteLimits
  ((Over.post u).sheafPullback (Type w) (JD.over V) (JC.over (u.obj V)))]
variable [PreservesFiniteLimits
  ((Over.post u).sheafPullback (Type w) (JD.over V') (JC.over (u.obj V')))]
variable [HasSheafify (JC.over U) (Type w)]
variable [HasSheafify (JC.over U') (Type w)]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.map c).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over U')ᵒᵖ ⥤ Type w, (Over.map c').op.HasPointwiseRightKanExtension P]

include hcomm

/-- A commutative square in the base sites induces the corresponding natural square between
localized inverse-image functors. -/
theorem inverseImageOverMapPullback :
    IsIsomorphic
      ((u.localizedMorphismOfTopoi c).inverseImage ⋙ JC.overMapPullback (Type w) a)
      (JD.overMapPullback (Type w) b ⋙ (u.localizedMorphismOfTopoi c').inverseImage) := sorry

end Naturality

end CategoryTheory.Functor.Localized
