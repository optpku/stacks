/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Quotient

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap94.«94_16_1_1_CanonicalHom»

import StacksCheckRecall

/-! # Kernel-pair quotient source compatibility -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidAlgebraicSpace FiberedCategoryOver.Groupoids Opposite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A point of an algebraic space as an object in its presheaf fibration. -/
def pointAsPresentedFiber {S : Scheme.{u}} {F : AlgebraicSpace S} {T : Over S}
    (x : F.functorOfPoints.obj (op T)) : F.toGroupoids.p.Fiber T :=
  FiberedCategoryOver.Sets.ofPresheaf.valueToFiber F.functorOfPoints T x

end AlgebraicGeometry.AlgebraicStack

/- Lemma 94.16.1 (5): the canonical map from the quotient stack. -/
@[stacks 04T4] #check (AlgebraicGeometry.AlgebraicStack.fCan :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U),
    SmallQuotient.quotientStack (groupoid f hU) ⟶ X)

/- Lemma 94.16.1 (6): full faithfulness of the canonical map. -/
@[stacks 04T4] #check (AlgebraicGeometry.AlgebraicStack.fCan_fullyFaithful :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) [AlgebraicStack X]
    (hU : IsRepresentableByAlgebraicSpace U),
    Nonempty (toBasedFunctor (fCan f hU)).FullyFaithful)
