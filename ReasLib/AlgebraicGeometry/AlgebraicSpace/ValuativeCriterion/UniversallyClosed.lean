module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Separated

/-!
# Valuative criterion for universal closedness

A quasi-compact morphism of algebraic spaces satisfying the existence part of
the valuative criterion is universally closed. A quasi-separated universally
closed morphism satisfies the existence part. Thus, under quasi-compactness
and quasi-separatedness, universal closedness is equivalent to existence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.Existence

/-- A quasi-separated universally closed morphism of algebraic spaces satisfies
the existence part of the valuative criterion. -/
instance of_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [UniversallyClosed f] : Existence f :=
  sorry

end ValuativeCriterion.Existence

namespace UniversallyClosed

/-- A quasi-compact morphism satisfying the existence part of the valuative
criterion is universally closed. -/
instance of_quasiCompact_of_existence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [ValuativeCriterion.Existence f] :
    UniversallyClosed f :=
  sorry

/-- A quasi-compact quasi-separated morphism of algebraic spaces is universally
closed if and only if it satisfies the existence part of the valuative criterion. -/
theorem iff_existence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    UniversallyClosed f ↔ ValuativeCriterion.Existence f :=
  sorry

/-- For a quasi-compact separated morphism of algebraic spaces, universal
closedness, the existence part of the valuative criterion allowing dominating
extensions, and existence of a lift over every original valuative square are
equivalent. -/
theorem existence_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Separated f] :
    List.TFAE [UniversallyClosed f, ValuativeCriterion.Existence f,
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift] :=
  sorry

/-- A quasi-compact separated morphism of algebraic spaces is universally closed
if and only if every valuative square admits a dotted arrow. -/
theorem iff_hasLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [Separated f] :
    UniversallyClosed f ↔ ∀ sq : ValuativeCommSq f, sq.commSq.HasLift :=
  sorry

/-- Every valuative square of a quasi-compact, separated, universally closed
morphism of algebraic spaces admits a dotted arrow. -/
theorem hasLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [QuasiCompact f] [Separated f] [UniversallyClosed f] (sq : ValuativeCommSq f) :
    sq.commSq.HasLift :=
  sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicSpace
