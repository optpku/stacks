module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-!
# Presentations of invertible modules by effective Cartier divisors

This file records existence results expressing invertible modules as sheaves associated to
effective Cartier divisors.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- On a Noetherian quasi-affine scheme admitting an ample invertible module, every invertible
module is isomorphic to the sheaf associated to an effective Cartier divisor avoiding any
prescribed finite subset. -/
theorem exists_iso_associatedSheaf_avoiding_of_isQuasiAffine
    {X : Scheme.{u}} [IsNoetherian X] [X.IsQuasiAffine]
    (hample : HasAmpleInvertibleModule X)
    (L : X.Modules) [Scheme.Modules.Invertible L] (E : Set X) (hE : E.Finite) :
    ∃ (D : X.IdealSheafData)
      (hD : IsEffectiveCartierDivisor D.subschemeι),
      Disjoint E (D.support : Set X) ∧
        Nonempty (L ≅ @IdealSheafData.associatedSheaf X D hD) := sorry

/-- On a Noetherian scheme admitting an ample invertible module, every invertible module is
isomorphic to the difference sheaf of two effective Cartier divisors that both avoid any
prescribed finite subset. -/
theorem exists_iso_differenceSheaf_avoiding_of_hasAmpleInvertibleModule
    {X : Scheme.{u}} [IsNoetherian X]
    (hample : HasAmpleInvertibleModule X)
    (L : X.Modules) [Scheme.Modules.Invertible L] (E : Set X) (hE : E.Finite) :
    ∃ (D : X.IdealSheafData)
      (hD : IsEffectiveCartierDivisor D.subschemeι)
      (D' : X.IdealSheafData)
      (hD' : IsEffectiveCartierDivisor D'.subschemeι),
      Disjoint E (D.support : Set X) ∧
        Disjoint E (D'.support : Set X) ∧
          Nonempty (L ≅ @IdealSheafData.differenceSheaf X D D' hD hD') := sorry

end AlgebraicGeometry.Scheme.Modules.Invertible
