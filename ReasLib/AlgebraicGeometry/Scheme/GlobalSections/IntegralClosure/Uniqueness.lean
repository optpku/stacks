module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalUnits.BaseField

/-!
# Uniqueness of base-field integral closures in global sections

This module compares the integral closures arising from different field-valued
structure morphisms on the same scheme.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Two locally finite type structure morphisms from the same connected reduced scheme
determine the same integral-closure subring of global sections. -/
@[stacks 04MK]
theorem baseFieldIntegralClosure_eq_of_connectedReduced_of_locallyOfFiniteType
    {X : Scheme.{u}} {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    (a : X ⟶ Spec (CommRingCat.of k₁)) (b : X ⟶ Spec (CommRingCat.of k₂))
    [LocallyOfFiniteType a] [LocallyOfFiniteType b] [ConnectedSpace X] [IsReduced X] :
    a.baseFieldIntegralClosure = b.baseFieldIntegralClosure := sorry

end AlgebraicGeometry.Scheme.Hom
