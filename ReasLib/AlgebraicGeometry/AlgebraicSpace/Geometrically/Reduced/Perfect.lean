module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Reduced

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

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space over a perfect field is geometrically reduced at a point
if its étale local ring at a geometric point above that point is reduced. -/
@[stacks 0E02]
theorem geometricallyReducedAt_of_isReduced_etaleLocalRing_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : AlgebraicSpace (Spec (of k))}
    {x : Points X} {xbar : GeometricPoint X} (hx : xbar.liesOver x)
    [_root_.IsReduced (etaleLocalRing X xbar)] :
    GeometricallyReducedAt X x :=
  sorry

/-- A reduced algebraic space over a perfect field is geometrically reduced
over that field. -/
@[stacks 0E02, instance]
instance instGeometricallyReduced_of_isReduced_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : AlgebraicSpace (Spec (of k))}
    [IsReduced X] : GeometricallyReduced X :=
  sorry

/-- Over a perfect field, reducedness of the local ring of `X` at `x` in the sense
of `localRingHas` implies that `X` is geometrically reduced at `x`. -/
theorem geometricallyReducedAt_of_localRingHas_isReduced_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : AlgebraicSpace (Spec (of k))}
    (x : Points X) (h : localRingHas (fun R ↦ _root_.IsReduced R) X x) :
    GeometricallyReducedAt X x :=
  sorry

/-- Over a perfect field, an algebraic space is geometrically reduced if and only
if it is reduced. -/
theorem geometricallyReduced_iff_isReduced_of_perfectField
    {k : Type u} [Field k] [PerfectField k] (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyReduced X ↔ IsReduced X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
