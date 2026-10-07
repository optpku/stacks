module

public import Mathlib.FieldTheory.Perfect
public import stacks_project.Chap66.Lemma_66_22_6
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap72.Definition_72_11_1_GeometricallyReduced

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

/-- Lemma 72.11.4 (1): Let `X` be an algebraic space over a perfect field `k`
(for example `k` has characteristic zero, via `PerfectField.ofCharZero`). For
`x : Points X`, if `etaleLocalRing X xbar` is reduced for a geometric point
`xbar` lying over `x`, then `X` is geometrically reduced at `x`. -/
@[stacks 0E02]
theorem geometricallyReducedAt_of_isReduced_etaleLocalRing_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {X : AlgebraicSpace (Spec (of k))}
    {x : Points X} {xbar : GeometricPoint X} (hx : xbar.liesOver x)
    [_root_.IsReduced (etaleLocalRing X xbar)] :
    GeometricallyReducedAt X x :=
  sorry

/-- Lemma 72.11.4 (2): Let `X` be an algebraic space over a perfect field `k`
(for example `k` has characteristic zero, via `PerfectField.ofCharZero`). If `X`
is reduced, then `X` is geometrically reduced over `k`. -/
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
