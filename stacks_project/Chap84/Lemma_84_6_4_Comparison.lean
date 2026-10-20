/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import stacks_project.Chap73.Lemma_73_7_8_Big
public import stacks_project.Chap84.Lemma_84_8_4_Comparison

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison

/-! # Compatibility checks for fppf and étale comparison morphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Fppf
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open scoped MorphismOfTopoiIn

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.overFppfTopology :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    GrothendieckTopology (Over X))

#check (AlgebraicGeometry.AlgebraicSpace.overFppfTopology_def :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    overFppfTopology X = (fppfTopology S).over X)

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.epsilon_isMorphismOfSites :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    IsMorphismOfSites
      (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
      (overFppfTopology X) (𝟭 (Over X)))

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.epsilon_sheafPullback_preservesFiniteLimits :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    PreservesFiniteLimits
      ((𝟭 (Over X)).sheafPullback (Type (u + 1))
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
        (overFppfTopology X)))

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.epsilon_op_hasLeftKanExtension :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (P : (Over X)ᵒᵖ ⥤ Type (u + 1)),
    (𝟭 (Over X)).op.HasLeftKanExtension P)

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.epsilon :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    MorphismOfTopoiIn
      (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
      (overFppfTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.epsilon_pushforward :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (epsilon X).pushforward =
      (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
        (overFppfTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.Fppf.epsilon_inverseImage :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (epsilon X)⁻¹ =
      (𝟭 (Over X)).sheafPullback (Type (u + 1))
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)
        (overFppfTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.fppfComparison :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    MorphismOfTopoiIn.{u + 1, u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (overFppfTopology X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.fppfComparison_eq_comp :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    fppfComparison X =
      MorphismOfTopoiIn.comp (siteMorphismOfTopoi X) (Fppf.epsilon X))

#check (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.fppfComparison_pushforward :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (fppfComparison X).pushforward =
      (Fppf.epsilon X).pushforward ⋙ (siteMorphismOfTopoi X).pushforward)

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}}

variable {X Y : AlgebraicSpace S}

/-- The morphism of small étale topoi `f_small` associated to a morphism of
algebraic spaces, at coefficients `Type (u + 1)`. -/
abbrev smallMorphism (f : X ⟶ Y) :
    MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X) :=
  smallEtaleMorphismOfTopoi f

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

end

end
