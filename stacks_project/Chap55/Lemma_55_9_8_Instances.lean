module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.NormalCone.Nested
public import stacks_project.Chap55.Lemma_55_9_8_Divisor
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Picard

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [Flat f] [FiniteType f] [Scheme.Regular X]
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))

/- The normalized special-fibre divisor is Cartier on a regular model. -/
#check
  (AlgebraicGeometry.Scheme.Hom.isEffectiveCartierDivisorPrimitiveSpecialFiber f n components :
    IsEffectiveCartierDivisor (primitiveSpecialFiberDivisor f n components).subschemeι)

/- Its conormal sheaf is invertible. -/
#check (AlgebraicGeometry.Scheme.Hom.invertibleConormalPrimitiveSpecialFiber f n components :
  Scheme.Modules.Invertible
    (Scheme.Hom.conormalSheaf (primitiveSpecialFiberDivisor f n components).subschemeι))

end AlgebraicGeometry.Scheme.Hom
