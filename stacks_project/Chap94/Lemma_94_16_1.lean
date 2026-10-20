/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Quotient

public import stacks_project.Chap94.Lemma_94_16_1_KernelPair
public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap94.Lemma_94_16_1_QuotientMap
import StacksCheckRecall

/-! # Lemma 94.16.1

The kernel pair of a morphism from a space-representable algebraic stack gives a groupoid
in algebraic spaces and a fully faithful morphism from its quotient stack.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory
universe u

/- Lemma 94.16.1 (1): representability of the kernel pair. -/
@[stacks 04T4] #check (AlgebraicGeometry.AlgebraicStack.kernelPair_isRepresentableByAlgebraicSpace :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) [AlgebraicStack X],
    IsRepresentableByAlgebraicSpace U → IsRepresentableByAlgebraicSpace
      (KernelPair.kernelPair.{u + 1, u, u + 1} f))


/- Lemma 94.16.1 (2): canonical regrouping of the triple product. -/
@[stacks 04T4] #check (CategoryTheory.FiberedCategoryOver.Groupoids.KernelPair.tripleEquiv.{u + 1, u, u + 1} :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X),
    KernelPair.tripleProduct.{u + 1, u, u + 1} f ≌
      KernelPair.composablePairs.{u + 1, u, u + 1} f)


/- Lemma 94.16.1 (3): the outer projection. -/
@[stacks 04T4] #check (CategoryTheory.FiberedCategoryOver.Groupoids.KernelPair.pr02.{u + 1, u, u + 1} :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X),
    KernelPair.composablePairs.{u + 1, u, u + 1} f ⟶
      KernelPair.kernelPair.{u + 1, u, u + 1} f)

/- Lemma 94.16.1 (4): arbitrary representing spaces inherit the kernel-pair groupoid. -/
@[stacks 04T4] #check (AlgebraicGeometry.AlgebraicStack.groupoidWith :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    {FU FR : AlgebraicSpace S},
    (U ≌ FU.toGroupoids) →
    (KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) →
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))))

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
