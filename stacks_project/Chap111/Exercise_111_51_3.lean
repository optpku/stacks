/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SpecialFiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Exercise 111.51.3: if `f : X ⟶ Spec (CommRingCat.of R)` is proper, `R` is a discrete
valuation ring with residue field `k`, and the scheme-theoretic fibre
`X ×_{Spec R} Spec(k)` is empty, then `X` is empty. -/
@[stacks 02FI] #check
  (AlgebraicGeometry.Scheme.Hom.isEmpty_of_isEmpty_specialFiber :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f],
      IsEmpty (f.fiber (IsLocalRing.closedPoint R)) → IsEmpty X)

/- Emptiness of the scheme-theoretic fibre of `f` at the closed point of `Spec R` is
equivalent to emptiness of the pullback of `f` along `Spec.map` of the residue
homomorphism `IsLocalRing.residue R`. -/
#check
  (AlgebraicGeometry.Scheme.Hom.isEmpty_specialFiber_iff_isEmpty_pullback_residue :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)),
      IsEmpty (f.fiber (IsLocalRing.closedPoint R)) ↔
        IsEmpty (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) : Scheme))

end AlgebraicGeometry.Scheme.Hom
