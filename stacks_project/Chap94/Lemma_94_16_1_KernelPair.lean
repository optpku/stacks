/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.KernelPair.Operations
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Symmetry.Swap
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Lemma_94_9_8
public import stacks_project.Chap94.Lemma_94_10_11
public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair

import StacksCheckRecall

/-! # Kernel-pair source compatibility -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The self two-fibre product of a morphism of groupoid fibrations. -/
abbrev kernelPair {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) :
    GroupoidsOver S := KernelPair.kernelPair.{u + 1, u, u + 1} f

/-- The first projection of the self two-fibre product. -/
abbrev pr0 {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) :
    kernelPair f ⟶ U := KernelPair.pr0.{u + 1, u, u + 1} f

/-- The second projection of the self two-fibre product. -/
abbrev pr1 {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) :
    kernelPair f ⟶ U := KernelPair.pr1.{u + 1, u, u + 1} f

end AlgebraicGeometry.AlgebraicStack

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
