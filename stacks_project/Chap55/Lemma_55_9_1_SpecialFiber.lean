/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- The special-fibre ideal is available with its complete local-base type. -/
#check
  (AlgebraicGeometry.Scheme.Hom.specialFiberIdeal :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}},
      (X ⟶ Spec (CommRingCat.of R)) → X.IdealSheafData)

/- The special-fibre comparison isomorphism is available with its complete local-base type. -/
#check
  (AlgebraicGeometry.Scheme.Hom.specialFiberIso :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}},
      (f : X ⟶ Spec (CommRingCat.of R)) →
        f.specialFiberIdeal.subscheme ≅ f.fiber (IsLocalRing.closedPoint R))

/- The reduced component ideal-sheaf datum is available with its complete local-base type. -/
#check
  (AlgebraicGeometry.Scheme.Hom.specialFiberComponent :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}},
      (f : X ⟶ Spec (CommRingCat.of R)) →
        irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) → X.IdealSheafData)

/- The special-fibre multiplicity vector is available with its complete discrete-valuation-ring
type. -/
#check
  (AlgebraicGeometry.Scheme.Hom.specialFiberMultiplicities :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {X : Scheme.{u}},
      (f : X ⟶ Spec (CommRingCat.of R)) → [FiniteType f] →
        irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) →₀ ℕ)

end AlgebraicGeometry.Scheme.Hom
