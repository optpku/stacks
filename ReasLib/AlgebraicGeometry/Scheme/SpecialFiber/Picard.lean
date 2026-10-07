module

public import Mathlib.GroupTheory.OrderOfElement
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.PrimitiveDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The conormal sheaf of the normalized special-fibre divisor of a regular finite-type flat
model over a discrete valuation ring is invertible. -/
theorem invertibleConormalPrimitiveSpecialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    Scheme.Modules.Invertible
      (Scheme.Hom.conormalSheaf
        (primitiveSpecialFiberDivisor f n components).subschemeι) := sorry

/-- The explicit associated sheaf of the normalized special-fibre divisor. -/
noncomputable def primitiveSpecialFiberAssociatedSheaf
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) : X.Modules :=
  @IdealSheafData.associatedSheaf X (primitiveSpecialFiberDivisor f n components)
    (isEffectiveCartierDivisorPrimitiveSpecialFiber f n components)

/-- The Picard class of the associated sheaf of the normalized special-fibre divisor. -/
noncomputable def primitiveSpecialFiberPicardClass
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) : X.PicardGroup :=
  @Scheme.Modules.picardClass X (primitiveSpecialFiberAssociatedSheaf f n components)
    (@Scheme.effectiveCartierDivisorAssociatedSheaf_isInvertible X _
      (primitiveSpecialFiberDivisor f n components).toSubobject
      (IdealSheafData.effectiveCartierIdealFact
        (primitiveSpecialFiberDivisor f n components)
        (isEffectiveCartierDivisorPrimitiveSpecialFiber f n components)))

/-- The explicit Picard class of the normalized divisor's conormal sheaf. -/
noncomputable def primitiveSpecialFiberConormalPicardClass
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    (primitiveSpecialFiberDivisor f n components).subscheme.PicardGroup :=
  @Scheme.Modules.picardClass (primitiveSpecialFiberDivisor f n components).subscheme
    (Scheme.Hom.conormalSheaf (primitiveSpecialFiberDivisor f n components).subschemeι)
    (invertibleConormalPrimitiveSpecialFiber f n components)

/-- On a regular finite-type flat scheme over a discrete valuation ring, the associated sheaf
of the normalized special-fibre divisor has Picard order dividing the multiplicity gcd. -/
theorem primitiveSpecialFiberDivisor_picardOrder
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
  addOrderOf
        (primitiveSpecialFiberPicardClass f n components) ∣
      specialFiberMultiplicityGcd f n components := sorry

/-- On a regular finite-type flat scheme over a discrete valuation ring, the conormal sheaf
of the normalized special-fibre divisor is invertible and has Picard order dividing the
multiplicity gcd. -/
theorem primitiveSpecialFiberDivisor_conormalPicardOrder
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    Scheme.Modules.Invertible
        (Scheme.Hom.conormalSheaf
          (primitiveSpecialFiberDivisor f n components).subschemeι) ∧
      addOrderOf
          (primitiveSpecialFiberConormalPicardClass f n components) ∣
        specialFiberMultiplicityGcd f n components := sorry

end AlgebraicGeometry.Scheme.Hom
