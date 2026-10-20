/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth.Differentials
import StacksCheckRecall

/-!
# Relative differentials of formally smooth morphisms of algebraic spaces

The sheaf of relative differentials of a formally smooth morphism of algebraic
spaces is locally projective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.19.8: Let `S` be a scheme. Let `f : X ⟶ Y` be a formally smooth morphism of
algebraic spaces over `S`. Then `Ω[f]` is locally projective on `X`. -/
@[stacks 061I] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallySmooth.instIsLocallyProjectiveRelativeDifferentials :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.FormallySmooth f],
      AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective
        (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f))
