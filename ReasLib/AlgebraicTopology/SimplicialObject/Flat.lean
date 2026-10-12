/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.Algebra.Category.ModuleCat.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise-flat simplicial objects

Flatness of a simplicial object is a degreewise property of its values.  The categorical owner is
independent of modules; the `ModuleCat` API below identifies it with ordinary module flatness.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A simplicial object is termwise flat when each of its values is a flat object. -/
@[stacks 08QD "termwise-flat simplicial object"]
def IsTermwiseFlat (X : SimplicialObject C) : Prop :=
  ∀ n : ℕ, IsFlat (X _⦋n⦌)

namespace IsTermwiseFlat

/-- Every value of a termwise-flat simplicial object is flat. -/
@[stacks 08QD "termwise-flat simplicial object evaluation"]
theorem isFlat {X : SimplicialObject C} (hX : X.IsTermwiseFlat) (n : ℕ) :
    IsFlat (X _⦋n⦌) := sorry

end IsTermwiseFlat

variable {R : Type u} [CommRing R]

/-- Categorical termwise flatness of a simplicial module is equivalent to algebraic flatness in
every simplicial degree. -/
@[stacks 08QD "termwise-flat simplicial module bridge"]
theorem isTermwiseFlat_iff_moduleFlat (X : SimplicialObject (ModuleCat.{u} R)) :
    X.IsTermwiseFlat ↔ ∀ n : ℕ, Module.Flat R (X _⦋n⦌) := sorry

/-- Degreewise algebraic flatness makes a simplicial module termwise flat. -/
@[stacks 08QD "termwise-flat simplicial module constructor"]
theorem isTermwiseFlat_of_forall_moduleFlat (X : SimplicialObject (ModuleCat.{u} R))
    (hX : ∀ n : ℕ, Module.Flat R (X _⦋n⦌)) : X.IsTermwiseFlat := sorry

end CategoryTheory.SimplicialObject
