/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.Over.Derived
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap84.Lemma_84_5_6_Comparison
public import stacks_project.Chap84.Lemma_84_6_6_Comparison
public import stacks_project.Chap84.Lemma_84_8_2_Adjunction

/-!
# Small-étale to big-ph pushforward comparisons of algebraic spaces

Canonical inverse-image squares and right mates identifying small étale direct
images with big ph direct images after `a = π ∘ ε`, at the level of sheaves of
sets and of `D⁺` of abelian sheaves.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
  (piDerivedSquareIso smallInverseExact smallInverseImagePlus sheafPushforwardAdjunction)
open CategoryTheory CategoryTheory.Limits CategoryTheory.Adjunction
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor (associator isoWhiskerLeft isoWhiskerRight)
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PhComparison

variable {S : Scheme.{u}}

/-- Morphisms of algebraic spaces over `S` admit fibre products against arbitrary
test morphisms. -/
instance hasPullbacksAlong {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    HasPullbacksAlong f :=
  fun {_} _ => inferInstance

/-- Type-valued sheafification exists on every small étale site at the coefficient
universe of algebraic spaces over `S`. -/
instance smallEtale_hasSheafify_type (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) (Type (u + 1)) := sorry

/-- Type-valued sheafification exists on every big ph slice at the coefficient
universe of algebraic spaces over `S`. -/
instance phOver_hasSheafify_type (X : AlgebraicSpace S) :
    HasSheafify (bigPhSite X) (Type (u + 1)) := sorry

/-- The opposite of postcomposition on algebraic-space slices admits pointwise right
Kan extensions of type-valued presheaves. -/
instance overMap_op_hasPointwiseRightKanExtension_type
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (P : (Over X)ᵒᵖ ⥤ Type (u + 1)) :
    (Over.map f).op.HasPointwiseRightKanExtension P := sorry

/-- The bounded-below right-derived functor of big ph direct image exists. -/
instance phPushforward_hasRightDerivedFunctor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (bigPhSite X) (bigPhSite Y)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1})) := sorry

/-- Inverse image along `a_Z` is topology-comparison inverse image of identity
relocalization from `(Spaces/Z)_étale` to `(Spaces/Z)_ph`. -/
def toSmallEtaleInverseImageIso (Z : AlgebraicSpace S) :
    (toSmallEtale Z)⁻¹ ≅
      (siteMorphismOfTopoi Z)⁻¹ ⋙
        comparisonTopologyPullback (Type (u + 1)) etale_le_ph Z :=
  isoWhiskerLeft ((siteMorphismOfTopoi Z)⁻¹)
    (Adjunction.leftAdjointUniq (epsilon Z).adjunction
      (comparisonTopologyAdjunction (Type (u + 1)) etale_le_ph Z))

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Inverse-image square `ε_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_big,étale⁻¹ ⋙ ε_X⁻¹` on sheaves of
sets, obtained from the topology-comparison relocalization square. -/
def epsilonInverseImageSquare :
    (epsilon Y)⁻¹ ⋙ (Ph.Big.morphismOfTopoi f)⁻¹ ≅
      (Etale.Big.morphismOfTopoi f)⁻¹ ⋙ (epsilon X)⁻¹ :=
  let eY :=
    Adjunction.leftAdjointUniq (epsilon Y).adjunction
      (comparisonTopologyAdjunction (Type (u + 1)) etale_le_ph Y)
  let eX :=
    Adjunction.leftAdjointUniq (epsilon X).adjunction
      (comparisonTopologyAdjunction (Type (u + 1)) etale_le_ph X)
  isoWhiskerRight eY ((Ph.Big.morphismOfTopoi f)⁻¹) ≪≫
    (overMapPullbackComparisonIso etale_le_ph f).symm ≪≫
    isoWhiskerLeft ((Etale.Big.morphismOfTopoi f)⁻¹) eX.symm

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on sheaves of
sets. Here `a_Z = π_Z ∘ ε_Z` is `toSmallEtale Z`. -/
def smallPhInverseImageSquare :
    (toSmallEtale Y)⁻¹ ⋙ (Ph.Big.morphismOfTopoi f)⁻¹ ≅
      (smallEtaleMorphismOfTopoi f)⁻¹ ⋙ (toSmallEtale X)⁻¹ :=
  associator ((siteMorphismOfTopoi Y)⁻¹) ((epsilon Y)⁻¹)
      ((Ph.Big.morphismOfTopoi f)⁻¹) ≪≫
    isoWhiskerLeft ((siteMorphismOfTopoi Y)⁻¹) (epsilonInverseImageSquare f) ≪≫
    (associator ((siteMorphismOfTopoi Y)⁻¹) ((Etale.Big.morphismOfTopoi f)⁻¹)
      ((epsilon X)⁻¹)).symm ≪≫
    isoWhiskerRight (smallBigInverseImageSquare f) ((epsilon X)⁻¹) ≪≫
    associator ((smallEtaleMorphismOfTopoi f)⁻¹) ((siteMorphismOfTopoi X)⁻¹)
      ((epsilon X)⁻¹)

/-- Canonical Type-valued mate `a_Y⁻¹ ∘ f_small,* ⟶ f_big,ph,* ∘ a_X⁻¹`. -/
def smallPhPushforwardHom :
    (smallEtaleMorphismOfTopoi f).pushforward ⋙ (toSmallEtale Y)⁻¹ ⟶
      (toSmallEtale X)⁻¹ ⋙ (Ph.Big.morphismOfTopoi f).pushforward :=
  DerivedBaseChange.map
    (smallEtaleMorphismOfTopoi f).adjunction
    (Ph.Big.morphismOfTopoi f).adjunction
    (smallPhInverseImageSquare f)

/-- `smallPhPushforwardHom` is the right mate of the ph-small inverse-image square. -/
theorem smallPhPushforwardHom_eq :
    smallPhPushforwardHom f =
      DerivedBaseChange.map
        (smallEtaleMorphismOfTopoi f).adjunction
        (Ph.Big.morphismOfTopoi f).adjunction
        (smallPhInverseImageSquare f) :=
  sorry

/-- The bounded-below inverse-image square
`a_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on `D⁺`. -/
def plusSmallPhInverseImageSquare :
    aInverseAbPlus Y ⋙ Derived.Over.Plus.pullback (phTopology S) f ≅
      smallInverseImagePlus f ⋙ aInverseAbPlus X :=
  associator (piInverseImagePlus Y) (Derived.Plus.pullback etale_le_ph Y)
      (Derived.Over.Plus.pullback (phTopology S) f) ≪≫
    isoWhiskerLeft (piInverseImagePlus Y)
      (Derived.Plus.overMapPullbackComparisonIso etale_le_ph f).symm ≪≫
    (associator (piInverseImagePlus Y) (Derived.Over.Plus.pullback etaleTopology f)
      (Derived.Plus.pullback etale_le_ph X)).symm ≪≫
    isoWhiskerRight (piDerivedSquareIso f) (Derived.Plus.pullback etale_le_ph X) ≪≫
    associator (smallInverseImagePlus f) (piInverseImagePlus X)
      (Derived.Plus.pullback etale_le_ph X)

/-- Canonical `D⁺` mate `a_Y⁻¹ ∘ R f_small,* ⟶ R f_big,ph,* ∘ a_X⁻¹`. -/
def plusSmallPhPushforwardHom :
    Adjunction.Derived.Plus.right (sheafPushforward AddCommGrpCat.{u + 1} f) ⋙
        aInverseAbPlus Y ⟶
      aInverseAbPlus X ⋙ Derived.Over.Plus.pushforward (phTopology S) f :=
  DerivedBaseChange.map
    (Adjunction.Derived.Plus.adjunction (smallInverseExact f)
      (sheafPushforward AddCommGrpCat.{u + 1} f) (sheafPushforwardAdjunction f))
    (Derived.Over.Plus.adjunction (phTopology S) f)
    (plusSmallPhInverseImageSquare f)

/-- `plusSmallPhPushforwardHom` is the right mate of the `D⁺` inverse-image square. -/
theorem plusSmallPhPushforwardHom_eq :
    plusSmallPhPushforwardHom f =
      DerivedBaseChange.map
        (Adjunction.Derived.Plus.adjunction (smallInverseExact f)
          (sheafPushforward AddCommGrpCat.{u + 1} f) (sheafPushforwardAdjunction f))
        (Derived.Over.Plus.adjunction (phTopology S) f)
        (plusSmallPhInverseImageSquare f) :=
  sorry

/-- The component of canonical `D⁺` base change at `K ∈ D⁺(X_étale)`. -/
abbrev plusSmallPhPushforwardHom_app
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (aInverseAbPlus Y).obj
        ((Adjunction.Derived.Plus.right (sheafPushforward AddCommGrpCat.{u + 1} f)).obj K) ⟶
      (Derived.Over.Plus.pushforward (phTopology S) f).obj ((aInverseAbPlus X).obj K) :=
  (plusSmallPhPushforwardHom f).app K

/-- `plusSmallPhPushforwardHom_app` is the component of `plusSmallPhPushforwardHom`. -/
theorem plusSmallPhPushforwardHom_app_eq
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    plusSmallPhPushforwardHom_app f K = (plusSmallPhPushforwardHom f).app K :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
