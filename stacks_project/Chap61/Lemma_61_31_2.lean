module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.ChangeOfUniverse

/-!
# Lemma 61.31.2

Nested chosen small pro-étale sites induce a retraction of topoi and preserve
abelian sheaf cohomology under restriction, pushforward, and pullback.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigProetaleSite
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

/- Lemma 61.31.2 -/
@[stacks 098Y] #check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_comp_inverseImageIso :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
  ∀
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
  ,
    (MorphismOfTopoiIn.comp (smallNestedInclusion_continuousMorphism.{u, v, w} S ι e)
      (smallNestedInclusion_cocontinuousMorphism.{u, v, w} S ι e)).inverseImage ≅
      (MorphismOfTopoiIn.id (smallTopology X S)).inverseImage)

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_pushforward_iso_inverseImage :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
  ∀
    [HasSheafify (smallTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology Y (ι.obj S)) (Type w)]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ (Type w),
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
  ,
    (smallNestedInclusion_cocontinuousMorphism.{u, v, w} S ι e)⁻¹ ≅
      (smallNestedInclusion_continuousMorphism.{u, v, w} S ι e)_*)

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_cohomology_restrict :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
  ∀
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    (p : ℕ) (F' : Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})
  ,
    ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).obj
        ((smallNestedInclusion_abelianRestriction.{u, v, w} S ι e).obj F') ≅ ((Sheaf.Γ (smallTopology Y
        (ι.obj S)) AddCommGrpCat.{w}).rightDerived p).obj F')

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_cohomology_pushforward :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
  ∀
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w})
  ,
    ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).obj F ≅ ((Sheaf.Γ (smallTopology Y
        (ι.obj S)) AddCommGrpCat.{w}).rightDerived p).obj ((smallNestedInclusion_abelianPushforward.{u, v,
        w} S ι e).obj F))

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_cohomology_pullback :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
  ∀
    [HasSheafify (smallTopology X S) AddCommGrpCat.{w}]
    [HasSheafify (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology X S) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (smallTopology Y (ι.obj S)) AddCommGrpCat.{w}]
    [IsGrothendieckAbelian (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [IsGrothendieckAbelian (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology X S) AddCommGrpCat.{w})]
    [HasInjectiveResolutions (Sheaf (smallTopology Y (ι.obj S)) AddCommGrpCat.{w})]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseLeftKanExtension P]
    [∀ P : (smallSite X S)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallNestedInclusion S ι e).op.HasPointwiseRightKanExtension P]
    (p : ℕ) (F : Sheaf (smallTopology X S) AddCommGrpCat.{w})
  ,
    ((Sheaf.Γ (smallTopology X S) AddCommGrpCat.{w}).rightDerived p).obj F ≅ ((Sheaf.Γ (smallTopology Y
        (ι.obj S)) AddCommGrpCat.{w}).rightDerived p).obj ((smallNestedInclusion_abelianPullback.{u, v, w} S
        ι e).obj F))

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_full :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
    (smallNestedInclusion S ι e).Full)

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_faithful :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
    (smallNestedInclusion S ι e).Faithful)

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_isContinuous :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
    (smallNestedInclusion S ι e).IsContinuous (smallTopology X S) (smallTopology Y (ι.obj S)))

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_isCocontinuous :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
    (smallNestedInclusion S ι e).IsCocontinuous (smallTopology X S) (smallTopology Y (ι.obj S)))

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_preservesPullbacks :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
    PreservesLimitsOfShape WalkingCospan (smallNestedInclusion S ι e))

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallNestedInclusion_obj_smallTerminalObject :
  ∀ {X Y : ChosenBigProetaleSite.{u, v}} (S : X.carrier)
    (ι : X.carrier ⥤ Y.carrier) (e : ι ⋙ Y.toScheme ≅ X.toScheme),
    IsTerminal ((smallNestedInclusion S ι e).obj (smallTerminalObject X S)))

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallSiteHasPullbacks :
  ∀ (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier), HasPullbacks (smallSite X S))

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallTerminalObjectIsTerminal :
  ∀ (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier),
    IsTerminal (smallTerminalObject X S))
