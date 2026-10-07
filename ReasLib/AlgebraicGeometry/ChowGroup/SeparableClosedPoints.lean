module

public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Separable closed points and Chow groups

This module records the generation of the degree-zero Chow group of a smooth projective scheme
over a field by closed points with separable residue fields.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- If `X` is smooth and projective over a field `k`, then its degree-zero Chow group is generated
by the classes of closed points whose residue fields are separable over `k`. -/
theorem closure_separableClosedPointClasses_eq_top
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] :
    AddSubgroup.closure
      {alpha : @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction
            (fun _ : Spec (CommRingCat.of k) ↦ 0)) inferInstance 0 |
        ∃ x : closedPoints X.left,
          Algebra.IsSeparable k (X.left.residueField x) ∧
            alpha = @chowClass X.left
              (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction
                (fun _ : Spec (CommRingCat.of k) ↦ 0)) inferInstance 0
              (CycleGroup.point
                (X.hom.relativeDimensionFunction
                  (fun _ : Spec (CommRingCat.of k) ↦ 0)) 0 x
                (SchemeOverField.closedPoint_relativeDimensionFunction_eq_zero X x))} = ⊤ := sorry

end AlgebraicGeometry.ChowGroup
