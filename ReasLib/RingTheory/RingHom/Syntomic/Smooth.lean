/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Syntomic.Basic

@[expose] public section

/-!
# Smooth Ring Homomorphisms Are Syntomic

The intrinsic `RingHom` theorem is the canonical bridge.  The algebra-facing
corollary avoids repeated conversion through `RingHom.smooth_algebraMap`.
-/

universe u v

namespace RingHom.Smooth

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Every smooth commutative ring homomorphism is syntomic. -/
@[stacks 00TA "smooth maps are syntomic"]
theorem syntomic {f : R →+* S} (hf : f.Smooth) : f.Syntomic := sorry

end RingHom.Smooth

namespace Algebra.Smooth

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A smooth `R`-algebra has a syntomic structure map. -/
theorem syntomic [Algebra.Smooth R S] : (algebraMap R S).Syntomic := sorry

end Algebra.Smooth
