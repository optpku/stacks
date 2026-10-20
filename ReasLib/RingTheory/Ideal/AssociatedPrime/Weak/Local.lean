module

public import Mathlib.RingTheory.LocalRing.Basic
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weak association over a local ring

The maximal ideal of a local ring is weakly associated to a module exactly
when it is an associated prime of that module.
-/

universe u v

namespace Ideal.IsWeaklyAssociatedToModule.Local

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Over a local ring, weak association of the maximal ideal to a module is
equivalent to the maximal ideal being an associated prime of the module. -/
@[stacks 0566 "local maximal-ideal comparison"]
theorem maximalIdeal_iff_associatedPrime :
    Ideal.IsWeaklyAssociatedToModule R M (IsLocalRing.maximalIdeal R) ↔
      IsAssociatedPrime (IsLocalRing.maximalIdeal R) M := sorry

end Ideal.IsWeaklyAssociatedToModule.Local

end
