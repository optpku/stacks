/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyClosed.FinitePresentation

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 102.7.2: a quasi-compact morphism of algebraic stacks is universally
closed if and only if all locally finitely presented affine base-change
projections are closed, and if and only if some smooth surjective scheme
atlas has closed projections after every finite-dimensional affine-space test. -/
@[stacks 0H2A] #check
  (AlgebraicGeometry.AlgebraicStack.UniversallyClosed.tfae_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiCompact f],
      List.TFAE [UniversallyClosed f, Closed.forallAffineLocallyOfFinitePresentation f,
        Closed.existsSmoothAffineSpace f])

end AlgebraicGeometry.AlgebraicStack
