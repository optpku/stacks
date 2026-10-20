module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Very reasonable algebraic spaces

An algebraic space is very reasonable when it admits a jointly surjective family of
étale scheme charts whose self-relation projections are quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is very reasonable when it admits a jointly surjective family of
étale scheme charts with quasi-compact self-relation projections. -/
class IsVeryReasonable {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- A covering family of étale charts with quasi-compact self-relation projections. -/
  exists_cover :
    ∃ (I : Type (u + 1)) (U : I → Over S) (p : ∀ i, ofOver (U i) ⟶ X),
      (∀ i, Etale (p i)) ∧ (⋃ i, Set.range (Points.map (p i))) = Set.univ ∧
        ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
          IsPullback (ofOverMap s) (ofOverMap t) (p i) (p i) ∧
            AlgebraicGeometry.QuasiCompact s.left ∧ AlgebraicGeometry.QuasiCompact t.left

namespace IsVeryReasonable

/-- The covering family and its actual self-relation pullback witnesses. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsVeryReasonable X] :
    ∃ (I : Type (u + 1)) (U : I → Over S) (p : ∀ i, ofOver (U i) ⟶ X),
      (∀ i, Etale (p i)) ∧ (⋃ i, Set.range (Points.map (p i))) = Set.univ ∧
        ∀ i, ∃ (R : Over S) (s t : R ⟶ U i),
          IsPullback (ofOverMap s) (ofOverMap t) (p i) (p i) ∧
            AlgebraicGeometry.QuasiCompact s.left ∧ AlgebraicGeometry.QuasiCompact t.left :=
  IsVeryReasonable.exists_cover

/-- Every scheme is very reasonable: affine opens give charts with quasi-compact
self-relation projections. -/
instance ofOver {S : Scheme.{u}} (T : Over S) : IsVeryReasonable (AlgebraicSpace.ofOver T) :=
  sorry

end IsVeryReasonable

end AlgebraicGeometry.AlgebraicSpace
