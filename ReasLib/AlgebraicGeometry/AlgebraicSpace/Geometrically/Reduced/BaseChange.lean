module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldExtension

/-!
# Geometric reducedness after field extension

Geometric reducedness of an algebraic space over a field is invariant under
extension of the ground field, both at a point and globally.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open AlgebraicGeometry.FieldExtension (specMap)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace GeometricallyReducedAt

/-- An algebraic space over a field is geometrically reduced at a point if and
only if its base change along a field extension is geometrically reduced at any
point lying over that point. -/
@[stacks 0E04]
theorem iff_baseChange {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (x : Points X)
    (x' : Points (AlgebraicSpace.baseChange (specMap k k') X))
    (hx : FieldExtension.toSourceOnPoints k k' X x' = x) :
    GeometricallyReducedAt X x ↔
      GeometricallyReducedAt (AlgebraicSpace.baseChange (specMap k k') X) x' :=
  sorry

/-- If `X` is geometrically reduced at `x`, then the field-extension base change
is geometrically reduced at any point lying over `x`. -/
theorem baseChange {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (x : Points X)
    (x' : Points (AlgebraicSpace.baseChange (specMap k k') X))
    (hx : FieldExtension.toSourceOnPoints k k' X x' = x)
    (h : GeometricallyReducedAt X x) :
    GeometricallyReducedAt (AlgebraicSpace.baseChange (specMap k k') X) x' :=
  (iff_baseChange X x x' hx).mp h

/-- If the field-extension base change is geometrically reduced at a point lying
over `x`, then `X` is geometrically reduced at `x`. -/
theorem of_baseChange {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (x : Points X)
    (x' : Points (AlgebraicSpace.baseChange (specMap k k') X))
    (hx : FieldExtension.toSourceOnPoints k k' X x' = x)
    (h : GeometricallyReducedAt (AlgebraicSpace.baseChange (specMap k k') X) x') :
    GeometricallyReducedAt X x :=
  (iff_baseChange X x x' hx).mpr h

end GeometricallyReducedAt

namespace GeometricallyReduced

/-- An algebraic space over a field is geometrically reduced if and only if its
base change along a field extension is geometrically reduced. -/
@[stacks 0E04]
theorem iff_baseChange {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    GeometricallyReduced X ↔
      GeometricallyReduced (AlgebraicSpace.baseChange (specMap k k') X) :=
  sorry

/-- A geometrically reduced algebraic space remains geometrically reduced after
base change along a field extension. -/
instance inst_baseChange {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) [GeometricallyReduced X] :
    GeometricallyReduced (AlgebraicSpace.baseChange (specMap k k') X) :=
  (iff_baseChange X).mp inferInstance

/-- If the field-extension base change of `X` is geometrically reduced, then `X`
is geometrically reduced. -/
theorem of_baseChange {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (h : GeometricallyReduced (AlgebraicSpace.baseChange (specMap k k') X)) :
    GeometricallyReduced X :=
  (iff_baseChange X).mpr h

end GeometricallyReduced

end AlgebraicGeometry.AlgebraicSpace
