module

public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.CycleGroup.Degree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.Degree

/-!
# Degrees on zero-dimensional Chow groups

This module descends the degree of relative zero-cycles on a proper scheme over a field to
the zero-dimensional Chow group and gives its coefficient formula.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

namespace RationalEquivalence

/-- Rational-equivalence boundaries among relative zero-cycles have degree zero. -/
theorem boundaries_le_ker_degree (X : SchemeOverField k) [IsProper X.hom] :
    @boundaries X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
        inferInstance 0 ≤
      (CycleGroup.degree X).ker := sorry

end RationalEquivalence

namespace ChowGroup

/-- The degree homomorphism on the zero-dimensional Chow group of a proper scheme over a field. -/
noncomputable def degree (X : SchemeOverField k) [IsProper X.hom] :
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
        inferInstance 0 →+ ℤ :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X.left
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
        (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
          (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
      inferInstance 0)
    (CycleGroup.degree X) (RationalEquivalence.boundaries_le_ker_degree.{u, u} X)

/-- The degree of the Chow class of a relative zero-cycle is its cycle-level degree. -/
theorem degree_chowClass (X : SchemeOverField k) [IsProper X.hom]
    (α : CycleGroup X.left
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0) :
    degree X
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
          inferInstance 0 α) =
      CycleGroup.degree X α := sorry

/-- The degree of a zero-cycle class on a proper scheme over a field is the finite sum of its
coefficients multiplied by the dimensions over the base field of the global-sections algebras
of the corresponding reduced point closures. -/
theorem degree_chowClass_eq_finsum (X : SchemeOverField k) [IsProper X.hom]
    (α : CycleGroup X.left
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0) :
    degree X
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
          inferInstance 0 α) =
      ∑ᶠ x : X.left,
        CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0 α x *
          (Module.finrank k
            (Scheme.Hom.globalSectionsAlg (Scheme.PointClosure.ι x ≫ X.hom)) : ℤ) := sorry

end ChowGroup

end AlgebraicGeometry
