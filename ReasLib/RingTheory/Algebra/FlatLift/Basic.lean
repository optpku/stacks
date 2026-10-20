/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Flat algebra lifts
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u

namespace Algebra.NilpotentLift

/-- Existence of an `A'`-flat algebra `B'` together with an `A`-algebra
identification `B' ⊗[A'] A ≃ₐ[A] B`. -/
def existsFlatLift (A' : Type u) [CommRing A'] (A : Type u) [CommRing A]
    [Algebra A' A] (B : Type u) [CommRing B] [Algebra A B] : Prop :=
  ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra A' B'),
    Module.Flat A' B' ∧ Nonempty ((B' ⊗[A'] A) ≃ₐ[A] B)

/-- A flat algebra lift exists exactly when a flat algebra with the specified
base-change equivalence exists. -/
theorem existsFlatLift_iff (A' : Type u) [CommRing A'] (A : Type u) [CommRing A]
    [Algebra A' A] (B : Type u) [CommRing B] [Algebra A B] :
    existsFlatLift A' A B ↔
      ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra A' B'),
        Module.Flat A' B' ∧ Nonempty ((B' ⊗[A'] A) ≃ₐ[A] B) :=
  Iff.rfl

end Algebra.NilpotentLift

end
