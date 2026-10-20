module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion

/-!
# Valuative criterion for properness

A finite type quasi-separated morphism of algebraic spaces is proper if and
only if it satisfies the valuative criterion, if and only if every solid
valuative square admits a unique dotted lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion

/-- For a finite type quasi-separated morphism of algebraic spaces, properness,
the valuative criterion, and unique lifting of every solid valuative square
over its original valuation ring are equivalent. -/
theorem proper_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] :
    List.TFAE [Proper f, ValuativeCriterion f,
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct] :=
  sorry

/-- A finite type quasi-separated morphism of algebraic spaces is proper if and
only if it satisfies the valuative criterion. -/
theorem iff_proper {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] :
    Proper f ↔ ValuativeCriterion f :=
  (proper_tfae f).out 0 1

end ValuativeCriterion

namespace Proper

/-- A finite type quasi-separated morphism of algebraic spaces that satisfies
the valuative criterion is proper. -/
instance of_valuativeCriterion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [QuasiSeparated f] [ValuativeCriterion f] :
    Proper f :=
  (ValuativeCriterion.iff_proper f).mpr inferInstance

end Proper

end AlgebraicGeometry.AlgebraicSpace
