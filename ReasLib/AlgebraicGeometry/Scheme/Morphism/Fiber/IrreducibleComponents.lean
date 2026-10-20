module

public import Mathlib.SetTheory.Cardinal.Finite
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

/-!
# Numbers of geometric irreducible components of fibres

This module defines the extended-natural-valued number of irreducible components
of a geometric fibre and records its independence and base-change properties.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The number of irreducible components of the geometric fibre of `f` at `y`,
computed over the canonical separable closure of the residue field at `y`. -/
noncomputable def geometricIrreducibleFiberComponentCount {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) : ℕ∞ :=
  ENat.card
    (irreducibleComponents
      (AlgebraicGeometry.FieldExtension.baseChange (Y.residueField y)
        (SeparableClosure (Y.residueField y)) (f.fiberToSpecResidueField y)))

/-- The number of geometric irreducible components of the fibre can be computed
over any separably closed extension of its residue field. -/
theorem geometricIrreducibleFiberComponentCount_eq_enatCard {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) (K : Type u) [Field K] [Algebra (Y.residueField y) K]
    [IsSepClosed K] :
    f.geometricIrreducibleFiberComponentCount y =
      ENat.card
        (irreducibleComponents
          (AlgebraicGeometry.FieldExtension.baseChange (Y.residueField y) K
            (f.fiberToSpecResidueField y))) := sorry

/-- The geometric irreducible-fibre component count is preserved by a pullback
square of scheme morphisms. -/
theorem geometricIrreducibleFiberComponentCount_baseChange {Y X Y' X' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) :
    f'.geometricIrreducibleFiberComponentCount =
      fun y' ↦ f.geometricIrreducibleFiberComponentCount (g y') := sorry

end AlgebraicGeometry.Scheme.Hom
