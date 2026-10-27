/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

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
theorem groupoid_flat {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f] :
    GroupoidAlgebraicSpace.Flat (groupoid f hU) := sorry

/-- The kernel-pair groupoid of a surjective flat locally of finite presentation
1-morphism from a space-representable algebraic stack is locally of finite
presentation. -/
theorem groupoid_locallyOfFinitePresentation {S : Scheme.{u}}
    {X U : GroupoidsOver S} (f : U ⟶ X) [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f] :
    GroupoidAlgebraicSpace.LocallyOfFinitePresentation (groupoid f hU) := sorry

/-- The canonical 1-morphism `fCan f hU : [U / R] ⟶ X` associated to a
surjective, flat, locally of finite presentation atlas is an equivalence of
categories fibred in groupoids. The kernel-pair maps need not be smooth. -/
theorem fCan_isEquivalence_of_flat {S : Scheme.{u}} {X U : GroupoidsOver S}
    (f : U ⟶ X) [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f] :
    (toBasedFunctor (fCan f hU)).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicStack
