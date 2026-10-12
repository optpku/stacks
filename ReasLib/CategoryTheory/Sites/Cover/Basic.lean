/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic API for Grothendieck covers

This leaf contains facts about the canonical arrow family of a bundled Grothendieck cover.  It is
independent of descent, stacks, and sheafification, so those constructions can share the same
owner without importing one another.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology.Cover

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- The arrows indexed by a cover generate its underlying sieve. -/
theorem ofArrows_eq (S : J.Cover U) :
    Sieve.ofArrows Arrow.Y (fun I : S.Arrow ↦ I.f) = (S : Sieve U) := sorry

end CategoryTheory.GrothendieckTopology.Cover
