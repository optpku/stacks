module

public import Mathlib.AlgebraicGeometry.ResidueField
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Definition_100_4_2_Points

/-!
# Scheme and algebraic-space points of an algebraic stack

A scheme point of a slice, or a point of an algebraic space, determines a point
of the associated algebraic stack. Smooth charts through a stack point are
compared by these induced maps on `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The field-valued point of the slice of `U` associated to a scheme point of `U`. -/
def FieldValuedPoint.ofResidue {S : Scheme.{u}} {U : Over S} (u : U.left) :
    FieldValuedPoint (GroupoidsOver.slice U) :=
  of (U.left.residueField u) (U.left.fromSpecResidueField u ≫ U.hom)
    (overMap (Over.homMk (U.left.fromSpecResidueField u)))

/-- The structure morphism of `ofResidue u` is the residue-field map of `u` over `S`. -/
theorem FieldValuedPoint.ofResidue_structureHom {S : Scheme.{u}} {U : Over S}
    (u : U.left) :
    (FieldValuedPoint.ofResidue u).structureHom =
      U.left.fromSpecResidueField u ≫ U.hom :=
  sorry

/-- The morphism of `ofResidue u` is `overMap` of the residue-field map of `u`. -/
theorem FieldValuedPoint.ofResidue_hom {S : Scheme.{u}} {U : Over S} (u : U.left) :
    (FieldValuedPoint.ofResidue u).hom =
      overMap (Over.homMk (U.left.fromSpecResidueField u)) :=
  sorry

/-- The field-valued point of `F.toGroupoids` associated to a field-valued point of an
algebraic space `F`. -/
def FieldValuedPoint.ofAlgebraicSpace {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) : FieldValuedPoint F.toGroupoids :=
  of p.K p.structureHom
    ((AlgebraicSpace.ofOverSliceEquiv p.overObj).inv ≫
      AlgebraicSpace.toGroupoids.map p.hom)

/-- `ofAlgebraicSpace` preserves the structure morphism to `S`. -/
theorem FieldValuedPoint.ofAlgebraicSpace_structureHom {S : Scheme.{u}}
    {F : AlgebraicSpace S} (p : AlgebraicSpace.FieldValuedPoint F) :
    (FieldValuedPoint.ofAlgebraicSpace p).structureHom = p.structureHom :=
  sorry

/-- The morphism of `ofAlgebraicSpace p` is the slice comparison followed by `toGroupoids.map`. -/
theorem FieldValuedPoint.ofAlgebraicSpace_hom {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) :
    (FieldValuedPoint.ofAlgebraicSpace p).hom =
      (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv ≫
        AlgebraicSpace.toGroupoids.map p.hom :=
  sorry

namespace FieldValuedPoint.Equivalent

/-- Equivalence of field-valued points of an algebraic space is preserved by
passage to the associated algebraic stack. -/
theorem ofAlgebraicSpace {S : Scheme.{u}} {F : AlgebraicSpace S}
    {p q : AlgebraicSpace.FieldValuedPoint F}
    (h : AlgebraicSpace.FieldValuedPoint.Equivalent p q) :
    Equivalent (FieldValuedPoint.ofAlgebraicSpace p)
      (FieldValuedPoint.ofAlgebraicSpace q) :=
  sorry

end FieldValuedPoint.Equivalent

namespace Points

/-- The point of `|slice U|` associated to a scheme point of `U`. -/
def ofSlice {S : Scheme.{u}} {U : Over S} (u : U.left) :
    Points (GroupoidsOver.slice U) :=
  mk (FieldValuedPoint.ofResidue u)

/-- `ofSlice u` is the class of the residue-field point of `u`. -/
theorem ofSlice_eq {S : Scheme.{u}} {U : Over S} (u : U.left) :
    ofSlice u = mk (FieldValuedPoint.ofResidue u) :=
  sorry

/-- The image in `|X|` of a scheme point of `U` along a morphism `slice U ⟶ X`. -/
def mapSlice {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (u : U.left) : Points X :=
  mk ((FieldValuedPoint.ofResidue u).map p)

/-- `mapSlice p u` is the class of the postcomposition of the residue-field point of `u`. -/
theorem mapSlice_mk {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) (u : U.left) :
    mapSlice p u = mk ((FieldValuedPoint.ofResidue u).map p) :=
  sorry

/-- The image in `|F.toGroupoids|` of a point of an algebraic space `F`. -/
def ofAlgebraicSpace {S : Scheme.{u}} {F : AlgebraicSpace S}
    (x : AlgebraicSpace.Points F) : Points F.toGroupoids :=
  Quotient.map (fun p : AlgebraicSpace.FieldValuedPoint F ↦
      FieldValuedPoint.ofAlgebraicSpace p)
    (fun _ _ h ↦ FieldValuedPoint.Equivalent.ofAlgebraicSpace h) x

/-- Passage to stack points sends the class of a field-valued point to the class of
its associated field-valued point of `F.toGroupoids`. -/
theorem ofAlgebraicSpace_mk {S : Scheme.{u}} {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) :
    ofAlgebraicSpace (AlgebraicSpace.Points.mk p) =
      mk (FieldValuedPoint.ofAlgebraicSpace p) :=
  sorry

/-- The image in `|X|` of a point of an algebraic space `F` along a morphism
`F.toGroupoids ⟶ X`. -/
def mapSpace {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {F : AlgebraicSpace S} (p : F.toGroupoids ⟶ X) (u : AlgebraicSpace.Points F) :
    Points X :=
  map p (ofAlgebraicSpace u)

/-- `mapSpace p u` is the image of `ofAlgebraicSpace u` under `Points.map p`. -/
theorem mapSpace_apply {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {F : AlgebraicSpace S} (p : F.toGroupoids ⟶ X) (u : AlgebraicSpace.Points F) :
    mapSpace p u = map p (ofAlgebraicSpace u) :=
  sorry

end Points

end AlgebraicGeometry.AlgebraicStack
