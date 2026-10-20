/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallToBig.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Adjunction
public import ReasLib.CategoryTheory.Sites.Over.Topos
import Mathlib.Tactic.CrossRefAttribute

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

/-- The bounded-below right-derived functor of big ph direct image exists. -/
instance phPushforward_hasRightDerivedFunctor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (bigPhSite X) (bigPhSite Y)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1})) := sorry

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Inverse-image square `ε_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_big,étale⁻¹ ⋙ ε_X⁻¹` on sheaves of
sets, obtained from the topology-comparison relocalization square. -/
def epsilonInverseImageSquare :
    (epsilon Y)⁻¹ ⋙ (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f)⁻¹ ≅
      (Etale.Big.morphismOfTopoi f)⁻¹ ⋙ (epsilon X)⁻¹ :=
  let eY :=
    Adjunction.leftAdjointUniq (epsilon Y).adjunction
      (comparisonTopologyAdjunction (Type (u + 1)) etale_le_ph Y)
  let eX :=
    Adjunction.leftAdjointUniq (epsilon X).adjunction
      (comparisonTopologyAdjunction (Type (u + 1)) etale_le_ph X)
  isoWhiskerRight eY ((CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f)⁻¹) ≪≫
    (overMapPullbackComparisonIso etale_le_ph f).symm ≪≫
    isoWhiskerLeft ((Etale.Big.morphismOfTopoi f)⁻¹) eX.symm

/-- Inverse-image square `a_Y⁻¹ ⋙ f_big,ph⁻¹ ≅ f_small⁻¹ ⋙ a_X⁻¹` on sheaves of
sets. Here `a_Z = π_Z ∘ ε_Z` is `toSmallEtale Z`. -/
def smallPhInverseImageSquare :
    (toSmallEtale Y)⁻¹ ⋙ (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f)⁻¹ ≅
      (smallEtaleMorphismOfTopoi f)⁻¹ ⋙ (toSmallEtale X)⁻¹ :=
  associator ((siteMorphismOfTopoi Y)⁻¹) ((epsilon Y)⁻¹)
      ((CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f)⁻¹) ≪≫
    isoWhiskerLeft ((siteMorphismOfTopoi Y)⁻¹) (epsilonInverseImageSquare f) ≪≫
    (associator ((siteMorphismOfTopoi Y)⁻¹) ((Etale.Big.morphismOfTopoi f)⁻¹)
      ((epsilon X)⁻¹)).symm ≪≫
    isoWhiskerRight (smallBigInverseImageSquare f) ((epsilon X)⁻¹) ≪≫
    associator ((smallEtaleMorphismOfTopoi f)⁻¹) ((siteMorphismOfTopoi X)⁻¹)
      ((epsilon X)⁻¹)

/-- Canonical Type-valued mate `a_Y⁻¹ ∘ f_small,* ⟶ f_big,ph,* ∘ a_X⁻¹`. -/
def smallPhPushforwardHom :
    (smallEtaleMorphismOfTopoi f).pushforward ⋙ (toSmallEtale Y)⁻¹ ⟶
      (toSmallEtale X)⁻¹ ⋙ (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f).pushforward :=
  DerivedBaseChange.map
    (smallEtaleMorphismOfTopoi f).adjunction
    (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f).adjunction
    (smallPhInverseImageSquare f)

/-- `smallPhPushforwardHom` is the right mate of the ph-small inverse-image square. -/
theorem smallPhPushforwardHom_eq :
    smallPhPushforwardHom f =
      DerivedBaseChange.map
        (smallEtaleMorphismOfTopoi f).adjunction
        (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1} (phTopology S) f).adjunction
        (smallPhInverseImageSquare f) := rfl

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
        (plusSmallPhInverseImageSquare f) := rfl

/-- For a proper morphism of algebraic spaces, the canonical small-étale to
big-ph direct-image comparison on sheaves of sets is invertible. -/
@[stacks 0DGX, instance]
theorem proper_smallPhPushforward_isIso [Proper f] :
    IsIso (smallPhPushforwardHom f) := sorry

/-- For a proper morphism of algebraic spaces, the canonical small-étale to
big-ph derived direct-image comparison is invertible on bounded-below complexes
with torsion cohomology sheaves. -/
@[stacks 0DGX]
theorem proper_plusSmallPhPushforward_isIso [Proper f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion (smallEtaleTopology X)) K) :
    IsIso ((plusSmallPhPushforwardHom f).app K) := sorry

/-- The proper derived direct-image comparison is invertible when torsion
cohomology is supplied as a fact. -/
instance proper_plusSmallPhPushforward_isIso_of_fact [Proper f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    [Fact (DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion (smallEtaleTopology X)) K)] :
    IsIso ((plusSmallPhPushforwardHom f).app K) :=
  proper_plusSmallPhPushforward_isIso f K
    (Fact.out : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion (smallEtaleTopology X)) K)

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
