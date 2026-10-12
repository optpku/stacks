/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Left and right modules over monoid objects

One-sided modules in a monoidal category are bimodule objects whose other acting monoid is the
tensor unit.  This file provides that minimal interface independently of balanced tensor products
and categorical flatness.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Right modules over a monoid object, modeled as bimodules from the tensor-unit monoid. -/
@[stacks 0FSA "right modules over monoid objects"]
abbrev RightModule (A : Mon C) := Bimod (Mon.trivial C) A

/-- Left modules over a monoid object, modeled as bimodules to the tensor-unit monoid. -/
@[stacks 0FSA "left modules over monoid objects"]
abbrev LeftModule (A : Mon C) := Bimod A (Mon.trivial C)

namespace RightModule

variable {A : Mon C}

/-- The action of the trivial monoid on the left of a right module is the left unitor. -/
@[stacks 0FSA "trivial left action on a right module", simp]
theorem actLeft_eq (M : RightModule A) :
    M.actLeft = (MonoidalCategory.leftUnitor M.X).hom := sorry

end RightModule

namespace LeftModule

variable {A : Mon C}

/-- The action of the trivial monoid on the right of a left module is the right unitor. -/
@[stacks 0FSA "trivial right action on a left module", simp]
theorem actRight_eq (M : LeftModule A) :
    M.actRight = (MonoidalCategory.rightUnitor M.X).hom := sorry

end LeftModule

end CategoryTheory.Bimod

end
