/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Fppf
import StacksCheckRecall

/-!
# Remark 94.16.3

If a space-representable atlas of an algebraic stack is only surjective, flat,
and locally of finite presentation, then the canonical 1-morphism from the
quotient stack is still an equivalence, and the kernel-pair maps `s`, `t` are
flat and locally of finite presentation, though not smooth in general.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Remark 94.16.3 (1): if `f : U ⟶ X` is only surjective, flat, and locally of
finite presentation, then `fCan : [U / R] ⟶ X` is still an equivalence. -/
@[stacks 04WY]
#check (AlgebraicGeometry.AlgebraicStack.fCan_isEquivalence_of_flat :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f],
    (toBasedFunctor (AlgebraicStack.fCan f hU)).IsEquivalence)

/- Remark 94.16.3 (2): in this case the morphisms `s`, `t` of the kernel-pair
groupoid are flat. -/
@[stacks 04WY]
#check (AlgebraicGeometry.AlgebraicStack.groupoid_flat :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f],
    GroupoidAlgebraicSpace.Flat (AlgebraicStack.groupoid f hU))

/- Remark 94.16.3 (3): in this case the morphisms `s`, `t` of the kernel-pair
groupoid are locally of finite presentation, but not smooth in general. -/
@[stacks 04WY]
#check (AlgebraicGeometry.AlgebraicStack.groupoid_locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f],
    GroupoidAlgebraicSpace.LocallyOfFinitePresentation (AlgebraicStack.groupoid f hU))
