/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import stacks_project.Chap84.Lemma_84_5_6_Comparison
public import stacks_project.Chap84.Lemma_84_6_4_Comparison

/-!
# Type-valued fppf/étale pushforward comparisons of algebraic spaces

This leaf owns the inverse-image square identifying `a_Y⁻¹ ⋙ f_big,fppf⁻¹` with
`f_small⁻¹ ⋙ a_X⁻¹` on sheaves of types, and the canonical mate
`f_small,* ⋙ a_Y⁻¹ ⟶ a_X⁻¹ ⋙ f_big,fppf,*`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits CategoryTheory.Adjunction
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor
  (associator isoWhiskerLeft isoWhiskerRight leftUnitor rightUnitor)
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Slice pullback along `f` is continuous from `(Spaces/Y)_étale` to `(Spaces/X)_fppf`. -/
instance pullback_etaleToFppf_isContinuous (f : X ⟶ Y) :
    (Over.pullback f).IsContinuous (overEtaleTopology Y) (overFppfTopology X) :=
  Functor.isContinuous_comp' (leftUnitor (Over.pullback f))
    (overEtaleTopology Y) (overFppfTopology Y) (overFppfTopology X)

/-- The identity-site direct-image square
`f_big,fppf,* ⋙ ε_{Y,*} ≅ ε_{X,*} ⋙ f_big,étale,*`. -/
def epsilonPushforwardSquare (f : X ⟶ Y) :
    (Fppf.Big.morphismOfTopoi f).pushforward ⋙ (Fppf.epsilon Y).pushforward ≅
      (Fppf.epsilon X).pushforward ⋙ (Etale.Big.morphismOfTopoi f).pushforward :=
  isoWhiskerRight
      ((fppfTopology S).overMapPushforwardIsoCocontinuous (Type (u + 1)) f).symm
      (Fppf.epsilon Y).pushforward ≪≫
    Functor.sheafPushforwardContinuousComp' (leftUnitor (Over.pullback f))
      (Type (u + 1)) (overEtaleTopology Y) (overFppfTopology Y)
      (overFppfTopology X) ≪≫
    (Functor.sheafPushforwardContinuousComp' (rightUnitor (Over.pullback f))
      (Type (u + 1)) (overEtaleTopology Y) (overEtaleTopology X)
      (overFppfTopology X)).symm ≪≫
    isoWhiskerLeft (Fppf.epsilon X).pushforward
      (etaleTopology.overMapPushforwardIsoCocontinuous (Type (u + 1)) f)

/-- `epsilonPushforwardSquare` is the composite of the continuous/cocontinuous
direct-image comparisons with the identity-site composition isomorphisms. -/
theorem epsilonPushforwardSquare_eq (f : X ⟶ Y) :
    epsilonPushforwardSquare f =
      isoWhiskerRight
          ((fppfTopology S).overMapPushforwardIsoCocontinuous (Type (u + 1)) f).symm
          (Fppf.epsilon Y).pushforward ≪≫
        Functor.sheafPushforwardContinuousComp' (leftUnitor (Over.pullback f))
          (Type (u + 1)) (overEtaleTopology Y) (overFppfTopology Y)
          (overFppfTopology X) ≪≫
        (Functor.sheafPushforwardContinuousComp' (rightUnitor (Over.pullback f))
          (Type (u + 1)) (overEtaleTopology Y) (overEtaleTopology X)
          (overFppfTopology X)).symm ≪≫
        isoWhiskerLeft (Fppf.epsilon X).pushforward
          (etaleTopology.overMapPushforwardIsoCocontinuous (Type (u + 1)) f) :=
  sorry

/-- The identity-site inverse-image square
`ε_Y⁻¹ ⋙ f_big,fppf⁻¹ ≅ f_big,étale⁻¹ ⋙ ε_X⁻¹`. -/
def epsilonInverseImageSquare (f : X ⟶ Y) :
    (Fppf.epsilon Y).inverseImage ⋙ (Fppf.Big.morphismOfTopoi f).inverseImage ≅
      (Etale.Big.morphismOfTopoi f).inverseImage ⋙ (Fppf.epsilon X).inverseImage :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp (Fppf.epsilon Y).adjunction
        (Fppf.Big.morphismOfTopoi f).adjunction).ofNatIsoRight
      (epsilonPushforwardSquare f))
    (Adjunction.comp (Etale.Big.morphismOfTopoi f).adjunction
      (Fppf.epsilon X).adjunction)

/-- `epsilonInverseImageSquare` is the left adjoint of `epsilonPushforwardSquare`. -/
theorem epsilonInverseImageSquare_eq (f : X ⟶ Y) :
    epsilonInverseImageSquare f =
      Adjunction.leftAdjointUniq
        ((Adjunction.comp (Fppf.epsilon Y).adjunction
            (Fppf.Big.morphismOfTopoi f).adjunction).ofNatIsoRight
          (epsilonPushforwardSquare f))
        (Adjunction.comp (Etale.Big.morphismOfTopoi f).adjunction
          (Fppf.epsilon X).adjunction) :=
  sorry

/-- The Type-valued inverse-image square
`a_Y⁻¹ ⋙ f_big,fppf⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹`, obtained by whiskering the
identity-site `ε`-square with `smallBigInverseImageSquare`. -/
def smallFppfInverseImageSquare (f : X ⟶ Y) :
    (fppfComparison Y).inverseImage ⋙ (Fppf.Big.morphismOfTopoi f).inverseImage ≅
      (smallMorphism f).inverseImage ⋙ (fppfComparison X).inverseImage :=
  associator (siteMorphismOfTopoi Y).inverseImage (Fppf.epsilon Y).inverseImage
      (Fppf.Big.morphismOfTopoi f).inverseImage ≪≫
    isoWhiskerLeft (siteMorphismOfTopoi Y).inverseImage (epsilonInverseImageSquare f) ≪≫
    (associator (siteMorphismOfTopoi Y).inverseImage
      (Etale.Big.morphismOfTopoi f).inverseImage
      (Fppf.epsilon X).inverseImage).symm ≪≫
    isoWhiskerRight (smallBigInverseImageSquare f) (Fppf.epsilon X).inverseImage ≪≫
    associator (smallEtaleMorphismOfTopoi f).inverseImage
      (siteMorphismOfTopoi X).inverseImage (Fppf.epsilon X).inverseImage

/-- `smallFppfInverseImageSquare` is the composite of the `ε`-square, associators, and
the whiskered small-to-big étale inverse-image square. -/
theorem smallFppfInverseImageSquare_eq (f : X ⟶ Y) :
    smallFppfInverseImageSquare f =
      associator (siteMorphismOfTopoi Y).inverseImage (Fppf.epsilon Y).inverseImage
          (Fppf.Big.morphismOfTopoi f).inverseImage ≪≫
        isoWhiskerLeft (siteMorphismOfTopoi Y).inverseImage
          (epsilonInverseImageSquare f) ≪≫
        (associator (siteMorphismOfTopoi Y).inverseImage
          (Etale.Big.morphismOfTopoi f).inverseImage
          (Fppf.epsilon X).inverseImage).symm ≪≫
        isoWhiskerRight (smallBigInverseImageSquare f)
          (Fppf.epsilon X).inverseImage ≪≫
        associator (smallEtaleMorphismOfTopoi f).inverseImage
          (siteMorphismOfTopoi X).inverseImage (Fppf.epsilon X).inverseImage :=
  sorry

/-- Canonical Type-valued mate `a_Y⁻¹ ∘ f_small,* ⟶ f_big,fppf,* ∘ a_X⁻¹`. -/
def smallFppfPushforwardHom (f : X ⟶ Y) :
    (smallMorphism f).pushforward ⋙ (fppfComparison Y).inverseImage ⟶
      (fppfComparison X).inverseImage ⋙ (Fppf.Big.morphismOfTopoi f).pushforward :=
  DerivedBaseChange.map
    (smallMorphism f).adjunction
    (Fppf.Big.morphismOfTopoi f).adjunction
    (smallFppfInverseImageSquare f)

/-- `smallFppfPushforwardHom` is the right mate of `smallFppfInverseImageSquare`. -/
theorem smallFppfPushforwardHom_eq (f : X ⟶ Y) :
    smallFppfPushforwardHom f =
      DerivedBaseChange.map
        (smallMorphism f).adjunction
        (Fppf.Big.morphismOfTopoi f).adjunction
        (smallFppfInverseImageSquare f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
