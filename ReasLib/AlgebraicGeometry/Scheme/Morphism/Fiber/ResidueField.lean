module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

/-!
# Residue fields on fibres of scheme morphisms

This leaf specializes the residue-field algebra API to points of a fibre. It
depends on the fibre construction, while the general morphism API remains in
`Scheme.Morphism.ResidueField`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The residue field of a point of the fibre `X_s` has its canonical algebra structure over the
residue field `κ(s)` of the base point. -/
noncomputable instance fiberResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (x : f.fiber s) :
    Algebra (S.residueField s) ((f.fiber s).residueField x) :=
  ResidueField.algebraOfSpec (f.fiberToSpecResidueField s) x

end AlgebraicGeometry.Scheme.Hom
