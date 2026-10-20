module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Induced

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
