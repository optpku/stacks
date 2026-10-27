/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Comparison

/-!
# Quasi-coherent derived objects on an algebraic stack
-/

@[expose] public section

universe u

/- Proposition 104.8.4: let `𝒳` be an algebraic stack. Then `QC(𝒳)` is
canonically equivalent to `D_QCoh(𝒪_𝒳)`. -/
@[stacks 0H16]
#check (AlgebraicGeometry.AlgebraicStack.toDerivedQCoh_isEquivalence :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X],
    (AlgebraicGeometry.AlgebraicStack.toDerivedQCoh X).IsEquivalence)
