/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_33_1_Affine
public import stacks_project.Chap99.Lemma_99_13_1
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic

/-!
# The stack of proper algebraic spaces is not algebraic
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace FpFlatProperGroupoids

/-- Lemma 110.71.1: the stack in groupoids `pFpFlatProperGroupoids specZ` of
`FpFlatProperGroupoids.toGroupoids specZ` over `Sch_fppf` (`Over specZ`), whose
category of sections over a scheme `T` is the category of flat, proper, finitely
presented algebraic spaces over `T`, is not an algebraic stack. -/
@[stacks 0D1R]
theorem not_isAlgebraic :
    ¬ CohStack.AlgebraicStack (toGroupoids specZ) :=
  sorry

end FpFlatProperGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
