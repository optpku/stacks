/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Approximation
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.PrimitiveDivisor
public import stacks_project.Chap55.Lemma_55_9_1_SpecialFiber

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f]
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
variable (i : Fin n)

/- The multiplicity gcd and its divisibility specification. -/
#check (AlgebraicGeometry.Scheme.Hom.specialFiberMultiplicityGcd f n components : ℕ)
#check (AlgebraicGeometry.Scheme.Hom.specialFiberMultiplicityGcd_dvd f n components i :
  specialFiberMultiplicityGcd f n components ∣ f.specialFiberMultiplicities (components i))

/- The normalized multiplicity vector and its pointwise specification. -/
#check (AlgebraicGeometry.Scheme.Hom.primitiveSpecialFiberCoefficients f n components :
  Fin n →₀ ℕ)
#check (AlgebraicGeometry.Scheme.Hom.primitiveSpecialFiberCoefficients_apply f n components i :
  primitiveSpecialFiberCoefficients f n components i =
    f.specialFiberMultiplicities (components i) / specialFiberMultiplicityGcd f n components)

/- The normalized divisor and its weighted-sum specification. -/
#check (AlgebraicGeometry.Scheme.Hom.primitiveSpecialFiberDivisor f n components :
  X.IdealSheafData)
#check (AlgebraicGeometry.Scheme.Hom.primitiveSpecialFiberDivisor_def f n components :
  primitiveSpecialFiberDivisor f n components =
    IdealSheafData.effectiveCartierDivisorWeightedSum
      (primitiveSpecialFiberCoefficients f n components)
      (fun i ↦ f.specialFiberComponent (components i)))

end AlgebraicGeometry.Scheme.Hom
