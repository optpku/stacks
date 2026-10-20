module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced.BaseChange
import StacksCheckRecall

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

/- Lemma 72.11.6 (1): Geometric reducedness at a point is invariant under a
field extension at any point lying over it. -/
@[stacks 0E04]
#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyReducedAt.iff_baseChange :
  {k k' : Type u} → [Field k] → [Field k'] → [Algebra k k'] →
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) → (x : Points X) →
    (x' : Points (AlgebraicSpace.baseChange (specMap k k') X)) →
    FieldExtension.toSourceOnPoints k k' X x' = x →
    (GeometricallyReducedAt X x ↔
      GeometricallyReducedAt (AlgebraicSpace.baseChange (specMap k k') X) x'))

/- Lemma 72.11.6 (2): Geometric reducedness over the ground field is invariant
under field extension. -/
@[stacks 0E04]
#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyReduced.iff_baseChange :
  {k k' : Type u} → [Field k] → [Field k'] → [Algebra k k'] →
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) →
    (GeometricallyReduced X ↔
      GeometricallyReduced (AlgebraicSpace.baseChange (specMap k k') X)))

end AlgebraicGeometry.AlgebraicSpace
