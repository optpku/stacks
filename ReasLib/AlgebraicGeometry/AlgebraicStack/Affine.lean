/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- An algebraic stack (or category fibred in groupoids) is representable by an
affine scheme if it is equivalent to the slice fibration of an affine scheme
over `S`. -/
def IsRepresentableByAffine (X : GroupoidsOver S) : Prop :=
  ∃ U : Over S, IsAffine U.left ∧ Nonempty (X ≌ GroupoidsOver.slice U)

/-- Representability by an affine scheme means equivalence with the slice of an
affine scheme over `S`. -/
theorem isRepresentableByAffine_iff (X : GroupoidsOver S) :
    IsRepresentableByAffine X ↔
      ∃ U : Over S, IsAffine U.left ∧ Nonempty (X ≌ GroupoidsOver.slice U) :=
  Iff.rfl

/-- The slice fibration of an affine scheme over `S` is representable by an
affine scheme. -/
theorem isRepresentableByAffine_slice (U : Over S) [IsAffine U.left] :
    IsRepresentableByAffine (GroupoidsOver.slice U) :=
  ⟨U, inferInstance, ⟨CategoryTheory.Bicategory.Equivalence.id _⟩⟩

end AlgebraicGeometry.AlgebraicStack
