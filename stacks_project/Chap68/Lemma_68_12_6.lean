/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Dimension
import StacksCheckRecall

/-!
# Local-ring dimension along locally quasi-finite morphisms

A locally quasi-finite morphism of algebraic spaces cannot increase the
dimension of the local ring at a point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.12.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a locally quasi-finite
morphism of algebraic spaces over `S`. Let `x` be a point of `X`. Then
`localRingDimAt x ≤ localRingDimAt (Points.map f x)`. -/
@[stacks 0ABW] #check
  (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_le_of_locallyQuasiFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyQuasiFinite f]
      (x : Points X), localRingDimAt x ≤ localRingDimAt (Points.map f x))

end AlgebraicGeometry.AlgebraicSpace
