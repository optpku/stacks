module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion

/-!
# Valuative criterion for separated universally closed morphisms

A quasi-compact quasi-separated morphism of algebraic spaces is separated and
universally closed if and only if it satisfies the valuative criterion, if and
only if every solid valuative square admits a unique dotted lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion

/-- For a quasi-compact quasi-separated morphism of algebraic spaces over a scheme,
being separated and universally closed, satisfying the valuative criterion, and
admitting a unique lift in every valuative square are equivalent. -/
theorem separatedUniversallyClosed_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    List.TFAE [Separated f ∧ UniversallyClosed f, ValuativeCriterion f,
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct] :=
  sorry

/-- A quasi-compact quasi-separated morphism of algebraic spaces is separated and
universally closed if and only if it satisfies the valuative criterion. -/
theorem iff_separated_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    Separated f ∧ UniversallyClosed f ↔ ValuativeCriterion f :=
  sorry

/-- A quasi-compact quasi-separated morphism of algebraic spaces satisfies the
valuative criterion if and only if every valuative square admits a unique
dotted arrow. -/
theorem iff_uniqueLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    ValuativeCriterion f ↔
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct :=
  sorry

/-- Every valuative square of a quasi-compact, quasi-separated morphism of
algebraic spaces satisfying the valuative criterion admits a unique dotted
arrow. -/
theorem uniqueLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [QuasiCompact f] [QuasiSeparated f] [ValuativeCriterion f]
    (sq : ValuativeCommSq f) :
    sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct :=
  sorry

end ValuativeCriterion

end AlgebraicGeometry.AlgebraicSpace
