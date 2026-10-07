module

public import stacks_project.Chap72.Definition_72_11_1_GeometricallyReduced
public import stacks_project.Chap72.Lemma_72_11_6_BaseChange

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

/-- Lemma 72.11.6 (1): Let `k` be a field. Let `X` be an algebraic space over `k`.
Let `k'/k` be a field extension. Let `x` be a point of `|X|` and let `x'` be a
point of `|AlgebraicSpace.baseChange (specMap k k') X|` lying over `x`. Then `X`
is geometrically reduced at `x` if and only if the base change is geometrically
reduced at `x'`. -/
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
  sorry

/-- If the field-extension base change is geometrically reduced at a point lying
over `x`, then `X` is geometrically reduced at `x`. -/
theorem of_baseChange {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) (x : Points X)
    (x' : Points (AlgebraicSpace.baseChange (specMap k k') X))
    (hx : FieldExtension.toSourceOnPoints k k' X x' = x)
    (h : GeometricallyReducedAt (AlgebraicSpace.baseChange (specMap k k') X) x') :
    GeometricallyReducedAt X x :=
  sorry

end GeometricallyReducedAt

namespace GeometricallyReduced

/-- Lemma 72.11.6 (2): In particular, `X` is geometrically reduced over `k` if and
only if `AlgebraicSpace.baseChange (specMap k k') X` is geometrically reduced
over `k'`. -/
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
  sorry

/-- If the field-extension base change of `X` is geometrically reduced, then `X`
is geometrically reduced. -/
theorem of_baseChange {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (h : GeometricallyReduced (AlgebraicSpace.baseChange (specMap k k') X)) :
    GeometricallyReduced X :=
  sorry

end GeometricallyReduced

end AlgebraicGeometry.AlgebraicSpace
