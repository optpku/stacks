module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.GeometricGenus

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A one-dimensional irreducible component with its reduced induced scheme structure,
viewed as a scheme over the same field. -/
noncomputable def oneDimensionalComponent
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left)
    (hZ : topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1) :
    SchemeOverField k :=
  Over.mk (X.left.irreducibleComponentSubschemeι Z ≫ X.hom)

/-- The structure morphism of `oneDimensionalComponent X Z hZ` is the composite of the
component immersion with the structure morphism of `X`. -/
theorem oneDimensionalComponent_hom
    {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left)
    (hZ : topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1) :
    (oneDimensionalComponent X Z hZ).hom =
      X.left.irreducibleComponentSubschemeι Z ≫ X.hom := sorry

namespace OneDimensionalComponent

/-- A reduced irreducible component of a proper scheme is proper over the same field. -/
instance instIsProper
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (Z : irreducibleComponents X.left)
    (hZ : topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1) :
    IsProper (oneDimensionalComponent X Z hZ).hom := sorry

/-- A reduced one-dimensional irreducible component of a proper scheme over a field is a
curve. -/
instance instCurve
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (Z : irreducibleComponents X.left)
    (hZ : topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1) :
    Curve (oneDimensionalComponent X Z hZ) := sorry

/-- Over a separably closed field, a reduced irreducible component is geometrically
irreducible. -/
instance instGeometricallyIrreducible
    {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left)
    (hZ : topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1) :
    GeometricallyIrreducible (oneDimensionalComponent X Z hZ).hom := sorry

end OneDimensionalComponent

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.GeometricGenus

/-- The geometric genus of a proper scheme of dimension at most one, defined as the finsum
of the geometric genera of the one-dimensional irreducible components after base change to
an algebraic closure. -/
noncomputable def ofScheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) : ℕ :=
  ∑ᶠ Z : irreducibleComponents
      (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).left,
    if hZ : topologicalKrullDim ((FieldExtension.Over.baseChange k
        (AlgebraicClosure k) X).left.irreducibleComponentSubscheme Z) = 1 then
      Curve.geometricGenus
        (SchemeOverField.oneDimensionalComponent
          (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) Z hZ)
    else 0

/-- The defining finsum formula for the geometric genus of a proper scheme of dimension at
most one. -/
theorem ofScheme_def
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    ofScheme X hdim =
      ∑ᶠ Z : irreducibleComponents
          (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).left,
        if hZ : topologicalKrullDim ((FieldExtension.Over.baseChange k
            (AlgebraicClosure k) X).left.irreducibleComponentSubscheme Z) = 1 then
          Curve.geometricGenus
            (SchemeOverField.oneDimensionalComponent
              (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) Z hZ)
        else 0 := sorry

/-- On a proper geometrically irreducible curve, `ofScheme` agrees with the established
curve-level geometric genus. -/
theorem ofScheme_eq_curve
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [IsProper X.hom] [GeometricallyIrreducible X.hom] :
    ofScheme X (topologicalKrullDim_eq_one X).le = Curve.geometricGenus X := sorry

/-- The geometric genus of a proper scheme of dimension at most one is the finsum of the
geometric genera of its one-dimensional irreducible components. -/
theorem eq_finsum_irreducibleComponents
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    ofScheme X hdim =
      ∑ᶠ Z : irreducibleComponents X.left,
        if hZ : topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1 then
          ofScheme (SchemeOverField.oneDimensionalComponent X Z hZ) hZ.le
        else 0 := sorry

end AlgebraicGeometry.GeometricGenus
