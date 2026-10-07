module

public import stacks_project.Chap65.Lemma_65_16_3_Equivalence
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import stacks_project.Chap72.Definition_72_11_1_GeometricallyReduced

/-!
# Geometrically reduced fibre loci of morphisms of algebraic spaces

The scheme-theoretic fibre of a morphism of algebraic spaces over a field-valued
point, viewed over that field, and the locus in `|Y|` where this fibre is
geometrically reduced. The locus is stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme-theoretic fibre of `f` over a field-valued point `p`, viewed as an algebraic
space over `Spec (.of p.K)` by reindexing along `fiberToSpec f p`. -/
def fiberOverField {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) : AlgebraicSpace (Spec (.of p.K)) :=
  restrictOver (Over.mk (fiberToSpec f p))

/-- `fiberOverField f p` is `restrictOver` of the slice object of `fiberToSpec f p`. -/
theorem fiberOverField_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) :
    fiberOverField f p = restrictOver (Over.mk (fiberToSpec f p)) :=
  sorry

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

