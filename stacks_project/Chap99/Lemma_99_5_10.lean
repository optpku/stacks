/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EssentialImage
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap99.Lemma_99_5_10_Approximation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Approximation of `Coh_{X/B}` is an equivalence

In Situation 99.5.1, if `S` is locally Noetherian and `f : X ⟶ B` is separated,
then the Artin approximation functor from complete local objects of
`Coh_{X/B}` to formal objects is an equivalence of categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- Lemma 99.5.10: in Situation 99.5.1 assume that `S` is a locally Noetherian
scheme and that `f : X ⟶ B` is separated. Let `𝒳 = Coh_{X/B}`. Then the functor
`approximation f` of Artin's Axioms, Equation 98.9.3.1, from complete local
objects over `Spec(R)` to formal objects, is an equivalence of categories. -/
@[stacks 08W9, instance]
instance approximation.instIsEquivalence {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    (approximation f).IsEquivalence :=
  sorry

/-- Every formal object of `Coh_{X/B}` lies in the essential image of
`approximation f` when `f` is separated. -/
theorem mem_essImage {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (ξ : FormalObject f) :
    (approximation f).essImage ξ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
