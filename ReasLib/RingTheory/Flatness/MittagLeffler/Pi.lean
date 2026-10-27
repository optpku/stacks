/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Coherent.Noetherian
public import ReasLib.RingTheory.Coherent.Products
public import ReasLib.RingTheory.Flatness.MittagLeffler

@[expose] public section

/-!
# Powers of Noetherian Rings as Mittag-Leffler Modules

Arbitrary powers of a Noetherian commutative ring are flat Mittag-Leffler modules over the ring.
-/

universe u v

namespace Module

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {A : Type v}

namespace MittagLeffler

/-- An arbitrary power of a Noetherian commutative ring is Mittag-Leffler over the ring. -/
@[stacks 05D0 "Mittag-Leffler instance for a power of a Noetherian ring"]
instance piSelf [IsNoetherianRing R] : MittagLeffler R (A → R) := sorry

end MittagLeffler

/-- An arbitrary power of a Noetherian commutative ring is both
flat and Mittag-Leffler over the ring. -/
@[stacks 05D0]
theorem noetherian_pi_flat_and_mittagLeffler :
    Module.Flat R (A → R) ∧ MittagLeffler R (A → R) := sorry

end Module
