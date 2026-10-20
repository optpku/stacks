/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.CountablyGenerated.Basic

@[expose] public section

/-!
# Countably generated submodules

This file supplies the elementary complete-lattice operations on countably generated submodules.
It is independent of tensor products and change of rings.
-/

universe u v w

namespace Submodule.CountablyGenerated

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A supremum of two countably generated submodules is countably generated. -/
@[stacks 05A8 "binary supremum"]
theorem sup {P Q : Submodule R M} (hP : P.CountablyGenerated)
    (hQ : Q.CountablyGenerated) : (P ⊔ Q).CountablyGenerated := sorry

/-- A countable supremum of countably generated submodules is countably generated. -/
@[stacks 05A8 "countable supremum"]
theorem iSup {I : Sort w} [Countable I] (P : I → Submodule R M)
    (hP : ∀ i, (P i).CountablyGenerated) :
    (⨆ i, P i).CountablyGenerated := sorry

/-- A supremum indexed by a countable subtype is countably generated when every term is. -/
@[stacks 05A8 "countable-subtype supremum"]
theorem iSup_subtype {I : Type w} {s : Set I} (hs : s.Countable)
    (P : s → Submodule R M) (hP : ∀ i, (P i).CountablyGenerated) :
    (⨆ i, P i).CountablyGenerated := sorry

end Submodule.CountablyGenerated

namespace Submodule

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A submodule is countably generated exactly when its subtype is countably generated as a
module. -/
@[stacks 05A8 "submodule subtype"]
theorem countablyGenerated_iff_subtype (P : Submodule R M) :
    P.CountablyGenerated ↔ Module.CountablyGenerated R P := sorry

end Submodule
