module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically

/-!
# Geometrically reduced fibre loci of morphisms of algebraic spaces

The geometrically reduced fibre locus tests every field-valued representative of a
point. This locus is stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The locus of points of `Y` at which the scheme-theoretic fibre of `f` is geometrically
reduced. -/
def geometricallyReducedFiberLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Set (Points Y) :=
  {y | ∀ p : FieldValuedPoint Y, Points.mk p = y → GeometricallyReduced (fiberOverField f p)}

/-- Membership in `geometricallyReducedFiberLocus f` means that the fibre over every
field-valued representative is geometrically reduced. -/
theorem mem_geometricallyReducedFiberLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) :
    y ∈ geometricallyReducedFiberLocus f ↔
      ∀ p : FieldValuedPoint Y, Points.mk p = y →
        GeometricallyReduced (fiberOverField f p) :=
  Iff.rfl

/-- For a point of the target of a morphism of algebraic spaces, geometric reducedness
of the fibre over some field-valued representative, geometric reducedness over every
representative, and reducedness over every representative are equivalent. -/
theorem geometricallyReducedFiber_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) :
    List.TFAE
      [∃ p : FieldValuedPoint Y, Points.mk p = y ∧ GeometricallyReduced (fiberOverField f p),
        ∀ p : FieldValuedPoint Y, Points.mk p = y → GeometricallyReduced (fiberOverField f p),
        ∀ p : FieldValuedPoint Y, Points.mk p = y → IsReduced (fiberOverField f p)] :=
  sorry

/-- Existence of a geometrically reduced fibre over some field-valued representative of
`y` is equivalent to geometric reducedness of the fibre over every such representative. -/
theorem exists_geometricallyReduced_fiber_iff_forall
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    (∃ p : FieldValuedPoint Y, Points.mk p = y ∧ GeometricallyReduced (fiberOverField f p)) ↔
      ∀ p : FieldValuedPoint Y, Points.mk p = y → GeometricallyReduced (fiberOverField f p) :=
  sorry

/-- Geometric reducedness of the fibre of `f` over every field-valued representative of
`y` is equivalent to reducedness of the fibre over every such representative. -/
theorem forall_geometricallyReduced_fiber_iff_forall_isReduced
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    (∀ p : FieldValuedPoint Y, Points.mk p = y → GeometricallyReduced (fiberOverField f p)) ↔
      ∀ p : FieldValuedPoint Y, Points.mk p = y → IsReduced (fiberOverField f p) :=
  sorry

/-- Existence of a geometrically reduced fibre over some field-valued representative of
`y` is equivalent to membership of `y` in `geometricallyReducedFiberLocus f`. -/
theorem exists_geometricallyReduced_fiber_iff_mem_locus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    (∃ p : FieldValuedPoint Y, Points.mk p = y ∧ GeometricallyReduced (fiberOverField f p)) ↔
      y ∈ geometricallyReducedFiberLocus f :=
  sorry

/-- Geometric reducedness of fibres is preserved and reflected by a pullback square of
morphisms of algebraic spaces. -/
theorem geometricallyReducedFiber_iff_of_isPullback {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) (y' : Points Y') :
    y' ∈ geometricallyReducedFiberLocus f' ↔
      Points.map g y' ∈ geometricallyReducedFiberLocus f :=
  sorry

/-- The geometrically reduced fibre locus of a base-changed morphism of algebraic spaces
is the inverse image of the original locus. -/
theorem geometricallyReducedFiberLocus_baseChange {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) :
    geometricallyReducedFiberLocus f' =
      Points.map g ⁻¹' geometricallyReducedFiberLocus f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
