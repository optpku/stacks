/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Ring.CommutatorQuotient.Equiv

/-!
# Additive identification of a commutative ring with its commutator quotient

The shared equivalence gives the canonical identification `R ≃+ R♮` for a commutative
ring `R`, sending `x` to its class in the additive commutator quotient.
-/

@[expose] public section

noncomputable section

universe u

open Ring
open scoped Ring

namespace Ring.CommutatorQuotient

variable {R : Type u} [CommRing R]

/- The canonical additive identification of a commutative ring with its
additive commutator quotient. -/
#check (Ring.CommutatorQuotient.mkAddEquiv : R ≃+ R♮)

/- The canonical additive identification sends `x` to its class in `R♮`. -/
#check (Ring.CommutatorQuotient.mkAddEquiv_apply :
  ∀ (x : R), mkAddEquiv x = mk x)

/- The inverse of the canonical additive identification recovers a representative. -/
#check (Ring.CommutatorQuotient.mkAddEquiv_symm_mk :
  ∀ (x : R), mkAddEquiv.symm (mk x) = x)

end Ring.CommutatorQuotient
