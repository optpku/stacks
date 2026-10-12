/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.PicardGroup
public import stacks_project.Chap111.Exercise_111_40_5_Cusp
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

open Polynomial CommRing

namespace CommRing.Pic

/-- Evaluation at zero is a left inverse of the canonical map `R → Polynomial R`, so the induced
map on Picard groups is a retraction of `mapAlgebra R (Polynomial R)`. -/
theorem mapRingHom_constantCoeff_comp_mapAlgebra (R : Type u) [CommRing R] :
    (mapRingHom (constantCoeff : Polynomial R →+* R)).comp (mapAlgebra R (Polynomial R)) =
      MonoidHom.id (Pic R) :=
  sorry

/-- Exercise 111.40.8 (1): if `R` is a Noetherian normal domain, then the canonical map
`mapAlgebra R (Polynomial R)` is bijective. -/
@[stacks 02AN]
theorem mapAlgebra_polynomial_bijective (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] :
    Function.Bijective (mapAlgebra R (Polynomial R)) :=
  sorry

/-- An invertible `Polynomial R`-module whose class maps to `1` under evaluation at zero is free
of rank one. -/
theorem free_of_mapRingHom_constantCoeff_eq_one {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (M : Type u)
    [AddCommGroup M] [Module (Polynomial R) M] [Module.Invertible (Polynomial R) M]
    (h : mapRingHom (constantCoeff : Polynomial R →+* R) (Pic.mk (Polynomial R) M) = 1) :
    Module.Free (Polynomial R) M :=
  sorry

end CommRing.Pic

namespace Polynomial.Cusp

/-- Exercise 111.40.8 (2): if `k` is a field, then the canonical map
`Pic.mapAlgebra (cuspSubalgebra k) (Polynomial (cuspSubalgebra k))` is not bijective. -/
@[stacks 02AN]
theorem not_bijective_mapAlgebra_polynomial (k : Type u) [Field k] :
    ¬ Function.Bijective (Pic.mapAlgebra (cuspSubalgebra k) (Polynomial (cuspSubalgebra k))) :=
  sorry

end Polynomial.Cusp
