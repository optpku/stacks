/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
public import stacks_project.Chap78.Lemma_78_20_3_Comparison
public import stacks_project.Chap78.Lemma_78_21_2_Square

/-!
# 2-cartesian square of a quotient-stack atlas

A groupoid in algebraic spaces determines cartesian functors `s, t : 𝒮_R ⟶ 𝒮_U` and
`π : 𝒮_U ⟶ [U/R]` over `(Sch/S)_fppf`, together with an invertible 2-cell
`α : π ∘ s ≅ π ∘ t`. After aligning Hom-universes, this square is a cone on the cospan
`(π, π)` whose apex is `𝒮_R`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open CategoryTheory.Bicategory CategoryTheory.Functor
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.stackInSetsULift.map_id :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      stackInSetsULift.map (𝟙 X) = 𝟙 (stackInSetsULift X))

#check
  (AlgebraicGeometry.AlgebraicSpace.stackInSetsULift.map_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      stackInSetsULift.map (f ≫ g) =
        stackInSetsULift.map f ≫ stackInSetsULift.map g)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceTargetCone_isBilimit :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      (sourceTargetCone G).IsBilimit)
