/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation

/-!
# Presentations from smooth surjective algebraic-space atlases

A smooth surjective algebraic-space atlas has a smooth kernel-pair groupoid
whose quotient stack is equivalent to the target algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The kernel-pair groupoid of a smooth surjective morphism from an
algebraic-space-representable groupoid fibration to an algebraic stack is smooth. -/
theorem groupoid_smooth {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f] :
    GroupoidAlgebraicSpace.Smooth (groupoid f hU) := sorry

/-- The canonical quotient-stack morphism associated to a smooth surjective
algebraic-space atlas is an equivalence of categories fibred in groupoids. -/
theorem fCan_isEquivalence {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f] :
    (toBasedFunctor (fCan f hU)).IsEquivalence := sorry

/-- A smooth surjective morphism from an algebraic-space-representable groupoid
fibration supplies a presentation of the target algebraic stack. -/
def Presentation.ofSmoothSurjective {S : Scheme.{u}} {X U : GroupoidsOver S}
    (f : U ⟶ X) [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f] :
    Presentation X where
  groupoid := AlgebraicGeometry.AlgebraicStack.groupoid f hU
  isSmooth := groupoid_smooth f hU
  hom := fCan f hU
  isEquivalence := fCan_isEquivalence f hU

end AlgebraicGeometry.AlgebraicStack
