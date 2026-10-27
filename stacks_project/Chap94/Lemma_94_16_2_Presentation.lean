/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap94.Definition_94_16_4_Smooth
public import stacks_project.Chap94.Definition_94_16_5_Presentation
public import stacks_project.Chap94.Lemma_94_16_1_QuotientMap
public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Presentation

/-!
# Smooth surjective algebraic-space atlases as presentations

A surjective smooth 1-morphism from a space-representable algebraic stack
yields a smooth kernel-pair groupoid and an equivalence from the quotient
stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.groupoid_smooth :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f],
    GroupoidAlgebraicSpace.Smooth (AlgebraicGeometry.AlgebraicStack.groupoid f hU))

#check (AlgebraicGeometry.AlgebraicStack.fCan_isEquivalence :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f],
    (toBasedFunctor (AlgebraicGeometry.AlgebraicStack.fCan f hU)).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicStack.Presentation.ofSmoothSurjective :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S}
    (f : U ⟶ X) [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f],
    Presentation X)

end AlgebraicGeometry.AlgebraicStack

