/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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

namespace CommRing.Pic

/-- Evaluation at zero is a left inverse of the canonical map from a commutative ring to its
polynomial ring, and the induced map on Picard groups is a retraction. -/
theorem mapRingHom_constantCoeff_comp_mapAlgebra (R : Type u) [CommRing R] :
    (mapRingHom (Polynomial.constantCoeff : Polynomial R →+* R)).comp
        (mapAlgebra R (Polynomial R)) = MonoidHom.id (Pic R) :=
  sorry

/-- An invertible polynomial module whose Picard class specializes to the trivial class at zero
is a free module of rank one. -/
theorem linearEquiv_of_mapRingHom_constantCoeff_eq_one {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (M : Type u)
    [AddCommGroup M] [Module (Polynomial R) M] [Module.Invertible (Polynomial R) M]
    (h_trivial :
      mapRingHom (Polynomial.constantCoeff : Polynomial R →+* R) (Pic.mk (Polynomial R) M) = 1) :
    Nonempty (M ≃ₗ[Polynomial R] Polynomial R) :=
  sorry

/-- For a commutative Noetherian integrally closed domain, adjoining one polynomial variable
induces a bijection on Picard groups. -/
theorem mapAlgebra_polynomial_bijective (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] :
    Function.Bijective (mapAlgebra R (Polynomial R)) :=
  sorry

end CommRing.Pic

namespace Polynomial.Cusp

/-- The canonical Picard-group map from the cusp algebra to its polynomial ring is not bijective
over any field. -/
theorem not_bijective_mapAlgebra_polynomial (k : Type u) [Field k] :
    ¬ Function.Bijective (CommRing.Pic.mapAlgebra (cuspSubalgebra k)
      (Polynomial (cuspSubalgebra k))) :=
  sorry

end Polynomial.Cusp
