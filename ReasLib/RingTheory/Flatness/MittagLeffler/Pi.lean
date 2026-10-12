/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Coherent.Noetherian
public import ReasLib.RingTheory.Coherent.Products
public import ReasLib.RingTheory.Flatness.MittagLeffler

@[expose] public section

/-!
# Powers of Noetherian Rings as Mittag-Leffler Modules

@stack 05D0

Arbitrary powers of a Noetherian commutative ring are canonical flat Mittag-Leffler modules.  The
instances in this leaf let downstream developments use both properties through typeclass search.
-/

universe u v

namespace Module

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {A : Type v}

namespace MittagLeffler

/-- An arbitrary power of a Noetherian commutative ring is Mittag-Leffler over the ring. -/
@[stacks 05D0 "Mittag-Leffler instance for a power of a Noetherian ring"]
instance piSelf : MittagLeffler R (A → R) := sorry

end MittagLeffler

/-- Chap10 Lemma 10 91 3, tag `05D0`: an arbitrary power of a Noetherian commutative ring is both
flat and Mittag-Leffler over the ring. -/
@[stacks 05D0]
theorem noetherian_pi_flat_and_mittagLeffler :
    Module.Flat R (A → R) ∧ MittagLeffler R (A → R) := sorry

#synth Module.Flat R (A → R)
#synth Module.MittagLeffler R (A → R)

end Module
