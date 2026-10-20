module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue-field points over a scheme

This leaf packages when the residue-field-valued points attached to two points
of schemes over a common base are isomorphic over that base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Two points of schemes over `S` have isomorphic residue-field points over
`S` when their canonical residue-field-valued points are isomorphic in
`Over S`. -/
def IsomorphicResidueFieldPointsOver
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] (x : X) (y : Y) : Prop :=
  Nonempty
    (Over.mk (X.fromSpecResidueField x ≫ (X ↘ S)) ≅
      Over.mk (Y.fromSpecResidueField y ≫ (Y ↘ S)))

/-- Unfold isomorphism of residue-field-valued points over a common base. -/
theorem isomorphicResidueFieldPointsOver_iff
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] (x : X) (y : Y) :
    IsomorphicResidueFieldPointsOver S X Y x y ↔
      Nonempty
        (Over.mk (X.fromSpecResidueField x ≫ (X ↘ S)) ≅
          Over.mk (Y.fromSpecResidueField y ≫ (Y ↘ S))) :=
  sorry

end AlgebraicGeometry.Scheme.Hom
