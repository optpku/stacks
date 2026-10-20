/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Chosen representatives of submodule quotients

The choice is deliberately encapsulated behind its computation lemma, so
downstream constructions use the specification rather than the representative.
-/

@[expose] public section

noncomputable section

universe u v

namespace Submodule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A chosen representative of a class in `M ⧸ N`.  Its only public computational interface is
`mkQ_quotientRepresentative`. -/
noncomputable def quotientRepresentative (N : Submodule R M) (x : M ⧸ N) : M :=
  Classical.choose (Submodule.mkQ_surjective N x)

/-- The chosen quotient representative maps back to the class from which it was selected. -/
@[simp]
theorem mkQ_quotientRepresentative (N : Submodule R M) (x : M ⧸ N) :
    N.mkQ (quotientRepresentative N x) = x := sorry

end Submodule
