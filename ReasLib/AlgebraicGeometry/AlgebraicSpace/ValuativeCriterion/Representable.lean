/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace ValuativeCriterion.Existence

/-- For a representable morphism of algebraic spaces, the existence criterion
allowing dominating extensions is equivalent to the existence of lifts over
every original valuative square. -/
theorem iff_hasLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    Existence f ↔ ∀ sq : ValuativeCommSq f, sq.commSq.HasLift :=
  sorry

/-- Lifts in every valuative square imply the existence criterion allowing
dominating extensions. -/
theorem of_hasLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ sq : ValuativeCommSq f, sq.commSq.HasLift) : Existence f :=
  sorry

/-- For a representable morphism satisfying the existence criterion, every
valuative square admits a lift over its original valuation ring. -/
theorem hasLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) [Existence f]
    (sq : ValuativeCommSq f) : sq.commSq.HasLift :=
  sorry

end ValuativeCriterion.Existence
end AlgebraicGeometry.AlgebraicSpace
