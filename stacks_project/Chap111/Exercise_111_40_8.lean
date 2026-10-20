/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Picard
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.40.8 (1): if `R` is a Noetherian normal domain, the canonical map on Picard
groups induced by `R → Polynomial R` is bijective. -/
@[stacks 02AN]
#check (CommRing.Pic.mapAlgebra_polynomial_bijective :
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R],
    Function.Bijective (CommRing.Pic.mapAlgebra R (Polynomial R)))

#check (CommRing.Pic.mapRingHom_constantCoeff_comp_mapAlgebra :
  ∀ (R : Type u) [CommRing R],
    (CommRing.Pic.mapRingHom (Polynomial.constantCoeff : Polynomial R →+* R)).comp
        (CommRing.Pic.mapAlgebra R (Polynomial R)) = MonoidHom.id (CommRing.Pic R))

#check (CommRing.Pic.linearEquiv_of_mapRingHom_constantCoeff_eq_one :
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (M : Type u) [AddCommGroup M] [Module (Polynomial R) M]
    [Module.Invertible (Polynomial R) M],
    CommRing.Pic.mapRingHom (Polynomial.constantCoeff : Polynomial R →+* R)
        (CommRing.Pic.mk (Polynomial R) M) = 1 →
      Nonempty (M ≃ₗ[Polynomial R] Polynomial R))

/- Exercise 111.40.8 (2): for every field `k`, the canonical Picard-group map from
the cusp algebra to its polynomial ring is not bijective. -/
@[stacks 02AN]
#check (Polynomial.Cusp.not_bijective_mapAlgebra_polynomial :
  ∀ (k : Type u) [Field k],
    ¬ Function.Bijective
      (CommRing.Pic.mapAlgebra (Polynomial.cuspSubalgebra k)
        (Polynomial (Polynomial.cuspSubalgebra k))))
