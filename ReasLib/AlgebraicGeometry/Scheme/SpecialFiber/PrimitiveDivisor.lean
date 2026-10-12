/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The gcd of the multiplicities of the indexed irreducible components of the special fibre. -/
noncomputable def specialFiberMultiplicityGcd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) : ℕ :=
  Finset.univ.gcd (fun i ↦ f.specialFiberMultiplicities (components i))

/-- Each special-fibre multiplicity is divisible by the gcd of all indexed multiplicities. -/
theorem specialFiberMultiplicityGcd_dvd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (i : Fin n) :
    specialFiberMultiplicityGcd f n components ∣ f.specialFiberMultiplicities (components i) := sorry

/-- The normalized multiplicity vector obtained by dividing each multiplicity by their gcd. -/
noncomputable def primitiveSpecialFiberCoefficients
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun i ↦ f.specialFiberMultiplicities (components i) /
      specialFiberMultiplicityGcd f n components)

/-- The normalized coefficient vector evaluates to the multiplicity divided by the gcd. -/
theorem primitiveSpecialFiberCoefficients_apply
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (i : Fin n) :
    primitiveSpecialFiberCoefficients f n components i =
      f.specialFiberMultiplicities (components i) /
        specialFiberMultiplicityGcd f n components := sorry

/-- The ideal-sheaf datum given by the normalized weighted sum of the special-fibre components. -/
noncomputable def primitiveSpecialFiberDivisor
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    X.IdealSheafData :=
  IdealSheafData.effectiveCartierDivisorWeightedSum
    (primitiveSpecialFiberCoefficients f n components)
    (fun i ↦ f.specialFiberComponent (components i))

/-- The normalized special-fibre divisor is the weighted sum of its component divisors. -/
theorem primitiveSpecialFiberDivisor_def
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    primitiveSpecialFiberDivisor f n components =
      IdealSheafData.effectiveCartierDivisorWeightedSum
        (primitiveSpecialFiberCoefficients f n components)
        (fun i ↦ f.specialFiberComponent (components i)) := sorry

/-- The normalized special-fibre divisor is an effective Cartier divisor on a regular model. -/
theorem isEffectiveCartierDivisorPrimitiveSpecialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    IsEffectiveCartierDivisor (primitiveSpecialFiberDivisor f n components).subschemeι := sorry

/-- The ideal of the special fibre is contained in the ideal of its primitive divisor. -/
theorem specialFiberIdeal_le_primitiveSpecialFiberDivisor
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    f.specialFiberIdeal ≤ primitiveSpecialFiberDivisor f n components := sorry

/-- The canonical inclusion of the primitive special-fibre divisor into the special fibre. -/
noncomputable def primitiveSpecialFiberToFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    (primitiveSpecialFiberDivisor f n components).subscheme ⟶
      f.fiber (IsLocalRing.closedPoint R) :=
  IdealSheafData.inclusion (specialFiberIdeal_le_primitiveSpecialFiberDivisor f n components) ≫
    f.specialFiberIso.hom

/-- The inclusion of the primitive special-fibre divisor commutes with the immersions into
the total space. -/
theorem primitiveSpecialFiberToFiber_fiberι
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    primitiveSpecialFiberToFiber f n components ≫ f.fiberι (IsLocalRing.closedPoint R) =
      (primitiveSpecialFiberDivisor f n components).subschemeι := sorry

/-- The canonical structure morphism of the primitive special-fibre divisor over the
residue field of the closed point. -/
noncomputable def primitiveSpecialFiberToResidueField
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    (primitiveSpecialFiberDivisor f n components).subscheme ⟶
      Spec (CommRingCat.of
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) :=
  primitiveSpecialFiberToFiber f n components ≫
    f.fiberToSpecResidueField (IsLocalRing.closedPoint R)

end AlgebraicGeometry.Scheme.Hom
