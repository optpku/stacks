module

public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.Algebra.Module.Submodule.Intersection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Intersections with a Noetherian submodule

This leaf transports Mathlib's Noetherian-submodule finiteness across the canonical equivalence
between the two subtype presentations of an intersection.  It is separate from the basic finite
submodule recall leaf so callers of `Module.Finite.iff_fg` do not acquire Noetherian dependencies.
-/

@[expose] public section

universe u v

namespace Submodule.Intersection

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Stacks `052N`: an intersection presented as a submodule of `q` is finite when `p` is Noetherian.

The Noetherian assumption belongs to `p`, not to the whole ring.  Mathlib supplies finiteness for
`q.comap p.subtype`; `Submodule.Intersection.swapEquiv` transports it to the caller's native subtype owner.
No local or global `Module.Finite` instance is introduced by this API. -/
@[stacks 052N "finite intersection inside a Noetherian submodule"]
theorem moduleFinite (p q : Submodule R M)
    [IsNoetherian R p] : Module.Finite R (p.comap q.subtype) := sorry

section RingBridge

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Stacks `052N`: explicit finite evidence for `p` is enough to make its intersection with `q`
finite over a Noetherian ring.  This term-level bridge avoids requiring callers to install
`hfinite` as a temporary `Module.Finite` instance. -/
@[stacks 052N "finite intersection from explicit finite evidence over a Noetherian ring"]
theorem moduleFinite_of_isNoetherianRing (p q : Submodule R M)
    [IsNoetherianRing R] (hfinite : Module.Finite R p) :
    Module.Finite R (p.comap q.subtype) := sorry

end RingBridge

end Submodule.Intersection
