/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Dimension
import StacksCheckRecall

/-!
# Dimension along locally quasi-finite morphisms of algebraic spaces

A locally quasi-finite morphism of algebraic spaces cannot increase global
dimension, in the sense of `AlgebraicSpace.dimension`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.12.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a locally quasi-finite
morphism of algebraic spaces over `S`. Then `dimension X ≤ dimension Y`. -/
@[stacks 0ED0] #check (AlgebraicGeometry.AlgebraicSpace.dimension_le_of_locallyQuasiFinite :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyQuasiFinite f],
    dimension X ≤ dimension Y)
