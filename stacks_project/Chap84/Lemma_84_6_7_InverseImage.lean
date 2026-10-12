/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap84.Lemma_84_5_6_Comparison
public import stacks_project.Chap84.Lemma_84_6_4_Comparison

/-!
# Small-étale / big-fppf inverse-image square of algebraic spaces

Canonical inverse-image square `a_Y⁻¹ ⋙ f_big,fppf⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on
sheaves of sets, obtained by composing the identity-site comparison `ε` with the
small-to-big étale square of Lemma 84.5.6.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Slice pullback along `f` is continuous from `(Spaces/Y)_étale` to `(Spaces/X)_fppf`. -/
instance overPullback_isContinuous_etale_fppf (f : X ⟶ Y) :
    (Over.pullback f).IsContinuous (overEtaleTopology Y) (overFppfTopology X) :=
  Functor.isContinuous_comp' (Functor.rightUnitor (Over.pullback f))
    (overEtaleTopology Y) (overEtaleTopology X) (overFppfTopology X)

/-- Inverse image of the big fppf morphism of topoi is sheaf pullback along
`Over.pullback f`. -/
noncomputable def fppfBigInverseImageIsoPullback (f : X ⟶ Y) :
    (Fppf.Big.morphismOfTopoi f)⁻¹ ≅
      (Over.pullback f).sheafPullback (Type (u + 1))
        (overFppfTopology Y) (overFppfTopology X) :=
  Adjunction.leftAdjointUniq
    ((fppfTopology S).overMapPushforwardAdjunction (Type (u + 1)) f)
    ((Over.pullback f).sheafAdjunctionContinuous (Type (u + 1))
      (overFppfTopology Y) (overFppfTopology X))

/-- Inverse image along `ε_X` is sheaf pullback of the identity functor of `Over X`. -/
noncomputable def epsilonInverseImageIso (Z : AlgebraicSpace S) :
    (Fppf.epsilon Z)⁻¹ ≅
      (𝟭 (Over Z)).sheafPullback (Type (u + 1))
        (overEtaleTopology Z) (overFppfTopology Z) :=
  Adjunction.leftAdjointUniq
    (Fppf.epsilon Z).adjunction
    ((𝟭 (Over Z)).sheafAdjunctionContinuous (Type (u + 1))
      (overEtaleTopology Z) (overFppfTopology Z))

/-- Identity-site pullback from étale to fppf, then slice pullback along `f`, agrees with
slice pullback then identity-site pullback. -/
noncomputable def fppfEpsilonRelocalizationPullbackIso (f : X ⟶ Y) :
    (𝟭 (Over Y)).sheafPullback (Type (u + 1))
        (overEtaleTopology Y) (overFppfTopology Y) ⋙
      (Over.pullback f).sheafPullback (Type (u + 1))
        (overFppfTopology Y) (overFppfTopology X) ≅
      (Over.pullback f).sheafPullback (Type (u + 1))
        (overEtaleTopology Y) (overEtaleTopology X) ⋙
        (𝟭 (Over X)).sheafPullback (Type (u + 1))
          (overEtaleTopology X) (overFppfTopology X) :=
  Functor.sheafPullbackComp' (overEtaleTopology Y) (overFppfTopology Y)
      (overFppfTopology X) (𝟭 (Over Y)) (Over.pullback f)
      (Functor.leftUnitor (Over.pullback f)) ≪≫
    (Functor.sheafPullbackComp' (overEtaleTopology Y) (overEtaleTopology X)
      (overFppfTopology X) (Over.pullback f) (𝟭 (Over X))
      (Functor.rightUnitor (Over.pullback f))).symm

/-- Inverse-image square `ε_Y⁻¹ ⋙ f_big,fppf⁻¹ ≅ f_big,étale⁻¹ ⋙ ε_X⁻¹` on sheaves of
sets. -/
noncomputable def fppfEpsilonInverseImageSquare (f : X ⟶ Y) :
    (Fppf.epsilon Y)⁻¹ ⋙ (Fppf.Big.morphismOfTopoi f)⁻¹ ≅
      (Big.morphismOfTopoi f)⁻¹ ⋙ (Fppf.epsilon X)⁻¹ :=
  isoWhiskerLeft ((Fppf.epsilon Y)⁻¹) (fppfBigInverseImageIsoPullback f) ≪≫
    isoWhiskerRight (epsilonInverseImageIso Y)
      ((Over.pullback f).sheafPullback (Type (u + 1))
        (overFppfTopology Y) (overFppfTopology X)) ≪≫
    fppfEpsilonRelocalizationPullbackIso f ≪≫
    isoWhiskerRight (bigInverseImageIsoPullback f).symm
      ((𝟭 (Over X)).sheafPullback (Type (u + 1))
        (overEtaleTopology X) (overFppfTopology X)) ≪≫
    isoWhiskerLeft ((Big.morphismOfTopoi f)⁻¹) (epsilonInverseImageIso X).symm

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,fppf⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on sheaves of
sets, where `a = π ∘ ε`. -/
noncomputable def fppfSmallInverseImageSquare (f : X ⟶ Y) :
    (fppfComparison Y)⁻¹ ⋙ (Fppf.Big.morphismOfTopoi f)⁻¹ ≅
      (smallMorphism f)⁻¹ ⋙ (fppfComparison X)⁻¹ :=
  associator ((siteMorphismOfTopoi Y)⁻¹) ((Fppf.epsilon Y)⁻¹)
      ((Fppf.Big.morphismOfTopoi f)⁻¹) ≪≫
    isoWhiskerLeft ((siteMorphismOfTopoi Y)⁻¹) (fppfEpsilonInverseImageSquare f) ≪≫
    (associator ((siteMorphismOfTopoi Y)⁻¹) ((Big.morphismOfTopoi f)⁻¹)
      ((Fppf.epsilon X)⁻¹)).symm ≪≫
    isoWhiskerRight (smallBigInverseImageSquare f) ((Fppf.epsilon X)⁻¹) ≪≫
    associator ((smallEtaleMorphismOfTopoi f)⁻¹) ((siteMorphismOfTopoi X)⁻¹)
      ((Fppf.epsilon X)⁻¹)

/-- `fppfSmallInverseImageSquare` is the composite of the identity-site `ε`-square with the
small-to-big étale inverse-image square. -/
theorem fppfSmallInverseImageSquare_eq (f : X ⟶ Y) :
    fppfSmallInverseImageSquare f =
      associator ((siteMorphismOfTopoi Y)⁻¹) ((Fppf.epsilon Y)⁻¹)
          ((Fppf.Big.morphismOfTopoi f)⁻¹) ≪≫
        isoWhiskerLeft ((siteMorphismOfTopoi Y)⁻¹)
          (fppfEpsilonInverseImageSquare f) ≪≫
        (associator ((siteMorphismOfTopoi Y)⁻¹) ((Big.morphismOfTopoi f)⁻¹)
          ((Fppf.epsilon X)⁻¹)).symm ≪≫
        isoWhiskerRight (smallBigInverseImageSquare f) ((Fppf.epsilon X)⁻¹) ≪≫
        associator ((smallEtaleMorphismOfTopoi f)⁻¹) ((siteMorphismOfTopoi X)⁻¹)
          ((Fppf.epsilon X)⁻¹) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end

end
