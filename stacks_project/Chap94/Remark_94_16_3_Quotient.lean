/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap94.Lemma_94_16_1_QuotientMap
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Flat locally of finite presentation atlases

A surjective, flat, locally of finite presentation 1-morphism from a
space-representable algebraic stack still yields an equivalence from the
quotient stack, and the kernel-pair groupoid is flat and locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The kernel-pair groupoid of a surjective flat locally of finite presentation
1-morphism from a space-representable algebraic stack is a flat groupoid in
algebraic spaces. -/
instance groupoid_flat {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f] :
    GroupoidAlgebraicSpace.Flat (groupoid f hU) := sorry

/-- The kernel-pair groupoid of a surjective flat locally of finite presentation
1-morphism from a space-representable algebraic stack is locally of finite
presentation. -/
instance groupoid_locallyOfFinitePresentation {S : Scheme.{u}}
    {X U : GroupoidsOver S} (f : U ⟶ X) [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f] :
    GroupoidAlgebraicSpace.LocallyOfFinitePresentation (groupoid f hU) := sorry

/-- The canonical 1-morphism `fCan f hU : [U / R] ⟶ X` associated to a
surjective, flat, locally of finite presentation atlas is an equivalence of
categories fibred in groupoids. The kernel-pair maps need not be smooth. -/
instance fCan_isEquivalence_of_flat {S : Scheme.{u}} {X U : GroupoidsOver S}
    (f : U ⟶ X) [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f] :
    (toBasedFunctor (fCan f hU)).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicStack
