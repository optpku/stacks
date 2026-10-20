/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Big
public import ReasLib.CategoryTheory.Adjunction.BaseChange

/-!
# Small étale and big ph comparison

The comparison from the big ph topos to the small étale topos, its canonical
inverse-image square, and the right mate for pushforward along scheme morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

/-- The identity on `Over S` is continuous from the big étale topology to the
big ph topology. -/
instance identity_etale_isContinuous_ph (S : Scheme.{u}) :
    Functor.IsContinuous (𝟭 (Over S))
      (S.overGrothendieckTopology @Etale) (Scheme.bigPhSite S) :=
  @Functor.isContinuous_comp' _ _ _ _ _ _ _ _ _
    (Functor.rightUnitor (𝟭 (Over S)))
    (S.overGrothendieckTopology @Etale)
    (Scheme.fppfTopology.over S)
    (Scheme.bigPhSite S)
    (StandardTopology.toFppf_isMorphismOfSites .etale S).toIsContinuous
    inferInstance

/-- Relocalization from the small étale site of `S` is continuous for the big
ph topology, as the composite of étale relocalization with the identity site
functor to ph. -/
instance relocalizationFunctor_isContinuous_ph (S : Scheme.{u}) :
    Functor.IsContinuous (relocalizationFunctor (𝟙 S))
      S.smallEtaleTopology (Scheme.bigPhSite S) :=
  Functor.isContinuous_comp' (Functor.rightUnitor (relocalizationFunctor (𝟙 S)))
    S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
    (Scheme.bigPhSite S)

/-- The morphism of topoi `a_S : Sh((Sch/S)_ph) ⟶ Sh(S_étale)` obtained by composing
the small-to-big étale morphism `π_S = siteMorphismOfTopoi S` with the ph-to-étale
comparison `ε_S = standardComparison .etale S`. -/
noncomputable abbrev toSmallEtale (X : Scheme.{u}) :
    MorphismOfTopoiIn X.smallEtaleTopology (Scheme.bigPhSite X) :=
  MorphismOfTopoiIn.comp (siteMorphismOfTopoi X) (standardComparison .etale X)

/-- Inverse image along `toSmallEtale X` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
@[simp]
theorem toSmallEtale_inverseImage (X : Scheme.{u}) :
    (toSmallEtale X)⁻¹ =
      (siteMorphismOfTopoi X)⁻¹ ⋙ (standardComparison .etale X)⁻¹ :=
  rfl

/-- Direct image along `toSmallEtale X` is the composite `ε_{X,*} ⋙ π_{X,*}`. -/
@[simp]
theorem toSmallEtale_pushforward (X : Scheme.{u}) :
    (toSmallEtale X).pushforward =
      (standardComparison .etale X).pushforward ⋙ (siteMorphismOfTopoi X).pushforward :=
  rfl

/-- Inverse image along `a_S` is sheaf pullback along étale-to-ph relocalization. -/
noncomputable def toSmallEtaleInverseImageIso (S : Scheme.{u}) :
    (toSmallEtale S)⁻¹ ≅
      (relocalizationFunctor (𝟙 S)).sheafPullback (Type (u + 1))
        S.smallEtaleTopology (Scheme.bigPhSite S) :=
  let adjπ := (siteMorphismOfTopoi S).adjunction
  let adjε := (standardComparison .etale S).adjunction
  let adjA :=
    (relocalizationFunctor (𝟙 S)).sheafAdjunctionContinuous (Type (u + 1))
      S.smallEtaleTopology (Scheme.bigPhSite S)
  Adjunction.leftAdjointCompIso adjπ adjε adjA
    (Functor.isoWhiskerRight
        (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
          (Functor.rightUnitor (𝟭 (Over S))) (Type (u + 1)) _
          (S.overGrothendieckTopology @Etale)
          (Scheme.fppfTopology.over S)
          (Scheme.bigPhSite S)
          (StandardTopology.toFppf_isMorphismOfSites .etale S).toIsContinuous
          inferInstance inferInstance)
        (siteMorphismOfTopoi S).pushforward ≪≫
      Functor.sheafPushforwardContinuousComp'
        (Functor.rightUnitor (relocalizationFunctor (𝟙 S))) (Type (u + 1))
        S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
        (Scheme.bigPhSite S))


variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Continuous sheaf pushforward along `Over.pullback f` on big ph sites is a
right adjoint, via the postcomposition-pullback adjunction. -/
instance isRightAdjoint_overPullback_sheafPushforwardContinuous_ph :
    ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
      (Scheme.bigPhSite Y) (Scheme.bigPhSite X)).IsRightAdjoint :=
  (Adjunction.sheafPushforwardContinuous (Over.mapPullbackAdj f)
    (Scheme.bigPhSite X) (Scheme.bigPhSite Y)).isRightAdjoint

/-- The composite `smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)` is continuous from the
small étale topology of `Y` to the big ph topology of `X`. -/
instance isContinuous_smallEtalePullback_comp_relocalization_ph :
    Functor.IsContinuous (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X))
      Y.smallEtaleTopology (Scheme.bigPhSite X) :=
  Functor.isContinuous_comp (smallEtalePullback f) (relocalizationFunctor (𝟙 X))
    Y.smallEtaleTopology X.smallEtaleTopology (Scheme.bigPhSite X)

/-- Site-level identification of the two paths around the small-étale / big-ph square. -/
private noncomputable def smallPhRelocalizationSiteIso :
    smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X) ≅
      relocalizationFunctor (𝟙 Y) ⋙ Over.pullback f :=
  (Functor.associator (smallEtalePullback f)
      (MorphismProperty.Over.forget (@Etale) ⊤ X) (Over.map (𝟙 X))).symm ≪≫
    Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale) (Q := ⊤) f)
      (Over.map (𝟙 X)) ≪≫
    Functor.associator
      (MorphismProperty.Over.forget (@Etale) ⊤ Y) (Over.pullback f) (Over.map (𝟙 X)) ≪≫
    Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale) ⊤ Y)
      (Functor.isoWhiskerLeft (Over.pullback f) (Over.mapId X) ≪≫
        Functor.rightUnitor (Over.pullback f)) ≪≫
    Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale) ⊤ Y)
      ((Functor.leftUnitor (Over.pullback f)).symm ≪≫
        Functor.isoWhiskerRight (Over.mapId Y).symm (Over.pullback f)) ≪≫
    (Functor.associator (MorphismProperty.Over.forget (@Etale) ⊤ Y)
      (Over.map (𝟙 Y)) (Over.pullback f)).symm

/-- The inverse image of the big ph morphism of topoi is the sheaf pullback along
`Over.pullback f`. -/
private noncomputable def phBigInverseImageIsoPullback :
    (Ph.Big.morphismOfTopoi f)⁻¹ ≅
      (Over.pullback f).sheafPullback (Type (u + 1))
        (Scheme.bigPhSite Y) (Scheme.bigPhSite X) :=
  Adjunction.leftAdjointUniq
    (Adjunction.sheafPushforwardContinuous (Over.mapPullbackAdj f)
      (Scheme.bigPhSite X) (Scheme.bigPhSite Y))
    ((Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.bigPhSite Y) (Scheme.bigPhSite X))

section TypeSheaves

variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify Y.smallEtaleTopology (Type (u + 1))]

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on sheaves of sets. -/
@[no_expose]
noncomputable def smallPhInverseImageSquare :
    (toSmallEtale Y)⁻¹ ⋙ (Ph.Big.morphismOfTopoi f)⁻¹ ≅
      (smallMorphism f)⁻¹ ⋙ (toSmallEtale X)⁻¹ :=
  let adjA_Y :=
    (relocalizationFunctor (𝟙 Y)).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology (Scheme.bigPhSite Y)
  let adjA_X :=
    (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology (Scheme.bigPhSite X)
  let adjSmall :=
    (smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology
  let adjBigCont :=
    (Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.bigPhSite Y) (Scheme.bigPhSite X)
  Functor.isoWhiskerLeft ((toSmallEtale Y)⁻¹) (phBigInverseImageIsoPullback f) ≪≫
    Functor.isoWhiskerRight (toSmallEtaleInverseImageIso Y)
      ((Over.pullback f).sheafPullback (Type (u + 1))
        (Scheme.bigPhSite Y) (Scheme.bigPhSite X)) ≪≫
    Adjunction.leftAdjointCompIso adjA_Y adjBigCont (adjSmall.comp adjA_X)
      (Functor.sheafPushforwardContinuousComp'
          (smallPhRelocalizationSiteIso f).symm (Type (u + 1))
          Y.smallEtaleTopology (Scheme.bigPhSite Y)
          (Scheme.bigPhSite X) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)))
          (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology
          (Scheme.bigPhSite X)).symm) ≪≫
    Functor.isoWhiskerLeft ((smallMorphism f)⁻¹) (toSmallEtaleInverseImageIso X).symm

/-- Canonical Type-valued mate `a_Y⁻¹ ∘ f_small,* ⟶ f_big,ph,* ∘ a_X⁻¹`. -/
noncomputable def smallPhPushforwardHom :
    (smallMorphism f).pushforward ⋙ (toSmallEtale Y)⁻¹ ⟶
      (toSmallEtale X)⁻¹ ⋙ (Ph.Big.morphismOfTopoi f).pushforward :=
  DerivedBaseChange.map
    (smallMorphism f).adjunction
    (Ph.Big.morphismOfTopoi f).adjunction
    (smallPhInverseImageSquare f)

/-- For a proper morphism of schemes, the canonical mate comparing small étale
pushforward followed by inverse image to the big ph site with big ph pushforward
after inverse image is an isomorphism on sheaves of sets. -/
theorem proper_smallPhPushforward_isIso [IsProper f] :
    IsIso (smallPhPushforwardHom f) := sorry

attribute [instance] proper_smallPhPushforward_isIso

end TypeSheaves

end AlgebraicGeometry.Scheme.PhComparison

end

end
