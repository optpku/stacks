module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier

/-!
# Extension of effective Cartier divisors

This file owns extension results for effective Cartier divisors from open subschemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- An effective Cartier divisor on an open subscheme of a locally Noetherian scheme extends
to the ambient scheme when every stalk outside the open is a unique factorization monoid. -/
theorem exists_extension_of_stalks_uniqueFactorizationMonoid
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (D : U.toScheme.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (hUFD : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ D' : X.IdealSheafData,
      AlgebraicGeometry.IsEffectiveCartierDivisor D'.subschemeι ∧ D = D'.comap U.ι := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
