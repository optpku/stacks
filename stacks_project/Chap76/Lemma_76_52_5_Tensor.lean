module

public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Relative perfectness and derived tensor products on algebraic spaces

This file gives preservation results for perfectness relative to a flat, locally finitely
presented morphism of algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.DerivedCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}}

/-- The fixed-right derived tensor product of objects of `D(𝒪_X)` on an algebraic space. -/
noncomputable abbrev tensorObj {X : AlgebraicSpace S} (K M : ModuleDerived X) :
    ModuleDerived X :=
  @DerivedTensor.Right.obj (Modules X) _ _ _
    (modulesMonoidalCategory X) (modulesMonoidalPreadditive X)
    (modulesHasMapBifunctor X) K M (hasDerivedTensorRight X)

/-- An absolutely perfect derived module on the source of a flat, locally finitely presented
morphism of algebraic spaces is perfect relative to that morphism. -/
theorem IsPerfect.isPerfectRelativeTo {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    {K : ModuleDerived X} (hK : IsPerfect K) :
    IsPerfectRelativeTo f K := sorry

/-- Tensoring a relatively perfect derived module on the left by an absolutely perfect derived
module preserves perfectness relative to a flat, locally finitely presented morphism of
algebraic spaces. -/
theorem IsPerfect.tensor_isPerfectRelativeTo {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    {K M : ModuleDerived X} (hK : IsPerfect K) (hM : IsPerfectRelativeTo f M) :
    IsPerfectRelativeTo f (tensorObj K M) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
