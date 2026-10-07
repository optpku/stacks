module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# DVR-valuative criteria for scheme morphisms

This leaf refines mathlib's `ValuativeCommSq` and `ValuativeCriterion` by
restricting the valuation ring to a discrete valuation ring. It exposes the
existence, uniqueness, and exists-unique forms as morphism properties.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A mathlib valuative commutative square whose valuation ring is discrete. -/
@[stacks 0CM2 "DVR-valuative commutative square"]
abbrev DvrValuativeCommSq {X S : Scheme.{u}} (f : X ⟶ S) : Type (u + 1) :=
  { sq : ValuativeCommSq f // IsDiscreteValuationRing sq.R }

namespace DvrValuativeCommSq

/-- The underlying unrestricted valuative commutative square. -/
@[stacks 0CM2 "underlying DVR-valuative square"]
abbrev toValuativeCommSq {X S : Scheme.{u}} {f : X ⟶ S}
    (sq : DvrValuativeCommSq f) : ValuativeCommSq f :=
  sq.val

/-- The underlying commutative square of a DVR-valuative square. -/
@[stacks 0CM2 "DVR-valuative commutative square proof"]
abbrev commSq {X S : Scheme.{u}} {f : X ⟶ S}
    (sq : DvrValuativeCommSq f) :=
  sq.toValuativeCommSq.commSq

/-- The valuation ring of a DVR-valuative square is canonically a discrete valuation ring. -/
instance instIsDiscreteValuationRing {X S : Scheme.{u}} {f : X ⟶ S}
    (sq : DvrValuativeCommSq f) :
    IsDiscreteValuationRing sq.toValuativeCommSq.R := sorry

end DvrValuativeCommSq

namespace ValuativeCriterion

/-- The DVR-valuative criterion: every DVR-valuative square for a morphism has a unique lift. -/
@[stacks 0208 "DVR valuative criterion"]
def DVR : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ sq : DvrValuativeCommSq f, Nonempty (Unique sq.commSq.LiftStruct)

namespace DVR

/-- The existence part of the DVR-valuative criterion. -/
@[stacks 05JY "DVR valuative existence criterion"]
def Existence : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ sq : DvrValuativeCommSq f, sq.commSq.HasLift

/-- The uniqueness part of the DVR-valuative criterion. -/
@[stacks 0207 "DVR valuative uniqueness criterion"]
def Uniqueness : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ sq : DvrValuativeCommSq f, Subsingleton sq.commSq.LiftStruct

/-- The DVR-valuative criterion is equivalent to its existence and uniqueness parts. -/
@[stacks 0208 "DVR valuative criterion decomposition"]
theorem iff {X S : Scheme.{u}} {f : X ⟶ S} :
    ValuativeCriterion.DVR f ↔
      ValuativeCriterion.DVR.Existence f ∧ ValuativeCriterion.DVR.Uniqueness f := sorry

/-- A morphism satisfying the DVR-valuative criterion has the DVR existence property. -/
@[stacks 05JY "DVR valuative existence projection"]
theorem existence {X S : Scheme.{u}} {f : X ⟶ S}
    (h : ValuativeCriterion.DVR f) :
    ValuativeCriterion.DVR.Existence f := sorry

/-- A morphism satisfying the DVR-valuative criterion has the DVR uniqueness property. -/
@[stacks 0207 "DVR valuative uniqueness projection"]
theorem uniqueness {X S : Scheme.{u}} {f : X ⟶ S}
    (h : ValuativeCriterion.DVR f) :
    ValuativeCriterion.DVR.Uniqueness f := sorry

end DVR

end ValuativeCriterion

end AlgebraicGeometry
