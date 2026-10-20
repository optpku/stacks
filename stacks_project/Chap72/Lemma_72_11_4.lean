module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced.Perfect
import StacksCheckRecall

/-!
# Geometric reducedness over a perfect field

Over a perfect field, reducedness of an étale local ring of an algebraic space
implies geometric reducedness at the corresponding point, and a reduced algebraic
space is geometrically reduced over the field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CommRingCat

noncomputable section

universe u

/- Lemma 72.11.4 (1): Let `X` be an algebraic space over a perfect field `k`
(for example `k` has characteristic zero, via `PerfectField.ofCharZero`). For
`x : Points X`, if `etaleLocalRing X xbar` is reduced for a geometric point
`xbar` lying over `x`, then `X` is geometrically reduced at `x`. -/
@[stacks 0E02] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReducedAt_of_isReduced_etaleLocalRing_of_perfectField :
    {k : Type u} → [Field k] → [PerfectField k] → {X : AlgebraicSpace (Spec (of k))} →
      {x : Points X} → {xbar : GeometricPoint X} → (hx : xbar.liesOver x) →
      [_root_.IsReduced (etaleLocalRing X xbar)] → GeometricallyReducedAt X x)

/- Lemma 72.11.4 (2): Let `X` be an algebraic space over a perfect field `k`
(for example `k` has characteristic zero, via `PerfectField.ofCharZero`). If `X`
is reduced, then `X` is geometrically reduced over `k`. -/
@[stacks 0E02] #check
  (AlgebraicGeometry.AlgebraicSpace.instGeometricallyReduced_of_isReduced_of_perfectField :
    {k : Type u} → [Field k] → [PerfectField k] → {X : AlgebraicSpace (Spec (of k))} →
      [IsReduced X] → GeometricallyReduced X)

/- Over a perfect field, reducedness of the local ring of `X` at `x` in the sense
of `localRingHas` implies that `X` is geometrically reduced at `x`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReducedAt_of_localRingHas_isReduced_of_perfectField :
    {k : Type u} → [Field k] → [PerfectField k] → {X : AlgebraicSpace (Spec (of k))} →
      (x : Points X) → (h : localRingHas (fun R ↦ _root_.IsReduced R) X x) →
      GeometricallyReducedAt X x)

/- Over a perfect field, an algebraic space is geometrically reduced if and only
if it is reduced. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReduced_iff_isReduced_of_perfectField :
    {k : Type u} → [Field k] → [PerfectField k] → (X : AlgebraicSpace (Spec (of k))) →
      (GeometricallyReduced X ↔ IsReduced X))
