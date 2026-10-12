/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Sites.Over.Adjunction

/-!
# Small-étale to big-fppf pushforward comparisons

Canonical inverse-image squares and right mates identifying small étale direct
images with big fppf direct images after the composite comparison
`a_S = π_S ∘ ε_S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- The identity on `Over S` is continuous from the big étale topology to the big fppf topology. -/
instance etaleToFppf_id_isContinuous (S : Scheme.{u}) :
    Functor.IsContinuous (𝟭 (Over S))
      (S.overGrothendieckTopology @Etale) (Scheme.fppfTopology.over S) :=
  (StandardTopology.toFppf_isMorphismOfSites .etale S).toIsContinuous

/-- Relocalization from the small étale site of `S` is continuous for the big fppf topology,
as the composite of étale relocalization with the identity site functor to fppf. -/
instance relocalizationFunctor_isContinuous_fppf (S : Scheme.{u}) :
    Functor.IsContinuous (relocalizationFunctor (𝟙 S))
      S.smallEtaleTopology (Scheme.fppfTopology.over S) :=
  Functor.isContinuous_comp' (Functor.rightUnitor (relocalizationFunctor (𝟙 S)))
    S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
    (Scheme.fppfTopology.over S)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The composite `smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)` is continuous from the
small étale topology of `Y` to the big fppf topology of `X`. -/
instance isContinuous_smallEtalePullback_comp_relocalization_fppf :
    Functor.IsContinuous (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X))
      Y.smallEtaleTopology (Scheme.fppfTopology.over X) :=
  Functor.isContinuous_comp (smallEtalePullback f) (relocalizationFunctor (𝟙 X))
    Y.smallEtaleTopology X.smallEtaleTopology (Scheme.fppfTopology.over X)

/-- The morphism of topoi `a_S : Sh((Sch/S)_fppf) ⟶ Sh(S_étale)` obtained by composing the
small-to-big étale morphism `π_S = siteMorphismOfTopoi S` with the fppf-to-étale comparison
`ε_S = StandardTopology.toFppf .etale S`. -/
abbrev fppfComparison (S : Scheme.{u}) :
    MorphismOfTopoiIn S.smallEtaleTopology (Scheme.fppfTopology.over S) :=
  MorphismOfTopoiIn.comp (siteMorphismOfTopoi S) (StandardTopology.toFppf .etale S)

/-- Inverse image along `fppfComparison S` is the composite `π_S⁻¹ ⋙ ε_S⁻¹`. -/
theorem fppfComparison_inverseImage (S : Scheme.{u}) :
    (fppfComparison S)⁻¹ =
      (siteMorphismOfTopoi S)⁻¹ ⋙ (StandardTopology.toFppf .etale S)⁻¹ := sorry

/-- Inverse image along `a_S` is sheaf pullback along étale-to-fppf relocalization. -/
noncomputable def fppfComparisonInverseImageIso (S : Scheme.{u}) :
    (fppfComparison S)⁻¹ ≅
      (relocalizationFunctor (𝟙 S)).sheafPullback (Type (u + 1))
        S.smallEtaleTopology (Scheme.fppfTopology.over S) :=
  let adjπ :=
    (relocalizationFunctor (𝟙 S)).sheafAdjunctionContinuous (Type (u + 1))
      S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
  let adjε :=
    (𝟭 (Over S)).sheafAdjunctionContinuous (Type (u + 1))
      (S.overGrothendieckTopology @Etale) (Scheme.fppfTopology.over S)
  let adjA :=
    (relocalizationFunctor (𝟙 S)).sheafAdjunctionContinuous (Type (u + 1))
      S.smallEtaleTopology (Scheme.fppfTopology.over S)
  Adjunction.leftAdjointCompIso adjπ adjε adjA
    (Functor.sheafPushforwardContinuousComp'
      (Functor.rightUnitor (relocalizationFunctor (𝟙 S))) (Type (u + 1))
      S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
      (Scheme.fppfTopology.over S))

/-- Site-level identification of the two paths around the small-étale / big-fppf square. -/
noncomputable def fppfSmallRelocalizationSiteIso :
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

/-- The inverse image of the big fppf morphism of topoi is the sheaf pullback along
`Over.pullback f`. -/
noncomputable def fppfBigInverseImageIsoPullback :
    (Fppf.Big.morphismOfTopoi f)⁻¹ ≅
      (Over.pullback f).sheafPullback (Type (u + 1))
        (Scheme.fppfTopology.over Y) (Scheme.fppfTopology.over X) :=
  Adjunction.leftAdjointUniq
    (Scheme.fppfTopology.overMapPushforwardAdjunction (Type (u + 1)) f)
    ((Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.fppfTopology.over Y) (Scheme.fppfTopology.over X))

section TypeSheaves

variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify Y.smallEtaleTopology (Type (u + 1))]

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,fppf⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on sheaves of sets. -/
noncomputable def fppfSmallInverseImageSquare :
    (fppfComparison Y)⁻¹ ⋙ (Fppf.Big.morphismOfTopoi f)⁻¹ ≅
      (smallMorphism f)⁻¹ ⋙ (fppfComparison X)⁻¹ :=
  let adjA_Y :=
    (relocalizationFunctor (𝟙 Y)).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology (Scheme.fppfTopology.over Y)
  let adjA_X :=
    (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type (u + 1))
      X.smallEtaleTopology (Scheme.fppfTopology.over X)
  let adjSmall :=
    (smallEtalePullback f).sheafAdjunctionContinuous (Type (u + 1))
      Y.smallEtaleTopology X.smallEtaleTopology
  let adjBigCont :=
    (Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (Scheme.fppfTopology.over Y) (Scheme.fppfTopology.over X)
  Functor.isoWhiskerLeft ((fppfComparison Y)⁻¹) (fppfBigInverseImageIsoPullback f) ≪≫
    Functor.isoWhiskerRight (fppfComparisonInverseImageIso Y)
      ((Over.pullback f).sheafPullback (Type (u + 1))
        (Scheme.fppfTopology.over Y) (Scheme.fppfTopology.over X)) ≪≫
    Adjunction.leftAdjointCompIso adjA_Y adjBigCont (adjSmall.comp adjA_X)
      (Functor.sheafPushforwardContinuousComp'
          (fppfSmallRelocalizationSiteIso f).symm (Type (u + 1))
          Y.smallEtaleTopology (Scheme.fppfTopology.over Y)
          (Scheme.fppfTopology.over X) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (smallEtalePullback f ⋙ relocalizationFunctor (𝟙 X)))
          (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology
          (Scheme.fppfTopology.over X)).symm) ≪≫
    Functor.isoWhiskerLeft ((smallMorphism f)⁻¹) (fppfComparisonInverseImageIso X).symm

/-- Canonical Type-valued mate `a_Y⁻¹ ∘ f_small,* ⟶ f_big,fppf,* ∘ a_X⁻¹`. -/
noncomputable def fppfSmallPushforwardHom :
    (smallMorphism f).pushforward ⋙ (fppfComparison Y)⁻¹ ⟶
      (fppfComparison X)⁻¹ ⋙ (Fppf.Big.morphismOfTopoi f).pushforward :=
  DerivedBaseChange.map
    (smallMorphism f).adjunction
    (Fppf.Big.morphismOfTopoi f).adjunction
    (fppfSmallInverseImageSquare f)

/-- `fppfSmallPushforwardHom` is the right mate of the fppf-small inverse-image square. -/
theorem fppfSmallPushforwardHom_eq :
    fppfSmallPushforwardHom f =
      DerivedBaseChange.map
        (smallMorphism f).adjunction
        (Fppf.Big.morphismOfTopoi f).adjunction
        (fppfSmallInverseImageSquare f) := sorry

end TypeSheaves

end AlgebraicGeometry.Scheme.Etale.SmallToBig

end

end
