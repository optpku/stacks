/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing
public import ReasLib.RingTheory.Flatness.MittagLeffler.BaseChange
import ReasLib.RingTheory.Flatness.MittagLeffler.Equiv

@[expose] public section

/-!
# Quotients of Mittag-Leffler modules

Quotienting a module by the multiples of an ideal is extension of scalars to the quotient ring,
so it preserves the Mittag-Leffler property.
-/

universe u v

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A quotient of a Mittag-Leffler module by the multiples of an ideal is Mittag-Leffler over the
quotient ring. -/
@[stacks 05A3 "quotient by an ideal"]
theorem quotient (I : Ideal R) (hM : Module.MittagLeffler R M) :
    Module.MittagLeffler (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))) := sorry

end Module.MittagLeffler
