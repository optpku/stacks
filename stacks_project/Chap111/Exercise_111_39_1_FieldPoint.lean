/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.FieldPoint

/-!
# Field-valued points of standard projective space

The shared field-point API associates to homogeneous coordinates a morphism
`Spec k ⟶ P^n_k` and remains available to existing chapter consumers.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry LinearAlgebra.Projectivization

universe u

#check (AlgebraicGeometry.ProjectiveSpace.fieldPoint :
  ∀ {k : Type u} [Field k] (n : ℕ), ℙ k (Fin (n + 1) → k) →
    (Spec (CommRingCat.of k) ⟶ AlgebraicGeometry.ProjectiveSpace.scheme k n))
