module

public import Mathlib.RingTheory.PicardGroup
public import ReasLib.RingTheory.Polynomial.Cusp
public import ReasLib.RingTheory.Polynomial.Equalizer

/-!
# Invertible modules on polynomial curves

This file records the polynomial-ring and singular-curve invertible-module statements used by
the polynomial Picard-group examples.
-/

@[expose] public section

universe u

namespace Polynomial

/-- Every invertible module over a field's polynomial ring is linearly equivalent to the ring. -/
theorem invertibleModule_linearEquiv (k : Type u) [Field k] (M : Type u)
    [AddCommGroup M] [Module (Polynomial k) M] [Module.Invertible (Polynomial k) M] :
    Nonempty (M ≃ₗ[Polynomial k] Polynomial k) :=
  sorry

namespace EqualEndpoint

/-- Over a field with nontrivial units, the equal-endpoint polynomial algebra has a nonfree
invertible module. -/
theorem exists_nontrivial_invertibleModule (k : Type u) [Field k] [Nontrivial kˣ] :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (equalEndpoint k) M)
      (_ : Module.Invertible (equalEndpoint k) M),
      ¬ Module.Free (equalEndpoint k) M :=
  sorry

end EqualEndpoint

namespace Cusp

/-- The cusp algebra `k[X ^ 2, X ^ 3]` has a nonfree invertible module over every field. -/
theorem exists_nontrivial_invertibleModule (k : Type u) [Field k] :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (cuspSubalgebra k) M)
      (_ : Module.Invertible (cuspSubalgebra k) M),
      ¬ Module.Free (cuspSubalgebra k) M :=
  sorry

end Cusp

end Polynomial
