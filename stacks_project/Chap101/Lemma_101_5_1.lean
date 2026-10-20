/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_11_2_LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia
import StacksCheckRecall

/-!
# Inertia of algebraic stacks

If `X` is an algebraic stack, then so is its inertia stack, and `I_X ⟶ X` is
representable by algebraic spaces and locally of finite type. The same holds
for relative inertia of a morphism of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (inertia relativeInertia)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Inertia

open FiberedCategoryOver.Groupoids.Inertia (forget)

/- Lemma 101.5.1 (1): the inertia stack of an algebraic stack is an algebraic
stack. -/
@[stacks 050Q] #check (AlgebraicGeometry.AlgebraicStack.Inertia.instAlgebraicStack :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    AlgebraicStack (inertia X))

/- Lemma 101.5.1 (2): the inertia morphism `I_X ⟶ X` of an algebraic stack is
representable by algebraic spaces and locally of finite type. -/
@[stacks 050Q] #check (AlgebraicGeometry.AlgebraicStack.Inertia.instLocallyOfFiniteType_forget :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    Groupoids.Hom.LocallyOfFiniteType (forget.{u + 1, u, u, u + 1} X))

end AlgebraicGeometry.AlgebraicStack.Inertia

namespace AlgebraicGeometry.AlgebraicStack.RelativeInertia

open FiberedCategoryOver.Groupoids.RelativeInertia (forget)

/- Lemma 101.5.1 (3): the relative inertia of a morphism of algebraic stacks is
an algebraic stack. -/
@[stacks 050Q] #check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.instAlgebraicStack :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    AlgebraicStack (relativeInertia f))

/- Lemma 101.5.1 (4): the morphism `relativeInertia f ⟶ X` is representable by
algebraic spaces and locally of finite type. -/
@[stacks 050Q] #check (AlgebraicGeometry.AlgebraicStack.RelativeInertia.instLocallyOfFiniteType_forget :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    Groupoids.Hom.LocallyOfFiniteType (forget.{u + 1, u, u, u + 1} f))

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
