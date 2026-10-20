/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Dimension
import StacksCheckRecall

/-!
# Dimension of the special fibre over a Noetherian local domain
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 89.2.3. The special fibre has dimension at most the dimension of the
base minus one. The general decent, locally finite-type case is followed by
the modification, alteration, and unique generic-point preimage cases. -/
@[stacks 0AYJ]
#check (AlgebraicGeometry.AlgebraicSpace.dimension_specialFiber_le_of_genericPoint_preimage_eq_genericPoints :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsDecent X] (f : X ⟶ specSpace A) [LocallyOfFiniteType f]
    (hη : Points.map f ⁻¹' {specSpaceGenericPoint A} = genericPoints X),
      dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1))

#check (AlgebraicGeometry.AlgebraicSpace.dimension_specialFiber_le_of_isModification :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsIntegral X] (f : X ⟶ specSpace A)
    [IsModification f],
      dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1))

#check (AlgebraicGeometry.AlgebraicSpace.dimension_specialFiber_le_of_isAlteration :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsIntegral X] (f : X ⟶ specSpace A)
    [IsAlteration f],
      dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1))

#check (AlgebraicGeometry.AlgebraicSpace.dimension_specialFiber_le_of_unique_genericPoint_preimage :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsIntegral X] (f : X ⟶ specSpace A) [LocallyOfFiniteType f]
    [QuasiSeparated f]
    (hη : ∃! x : Points X, Points.map f x = specSpaceGenericPoint A),
      dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1))
