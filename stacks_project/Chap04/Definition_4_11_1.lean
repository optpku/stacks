/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C} {a b : X ⟶ Y} {c : Y ⟶ Z} {h : a ≫ c = b ≫ c}

/- Canonical-selection rationale:
The source asks whether the supplied `c : Y ⟶ Z`, together with its compatibility
`h : a ≫ c = b ≫ c`, is a coequalizer. `Cofork.ofπ` packages exactly these data,
`IsColimit` is the canonical owner, and `Cofork.IsColimit.existsUnique` and
`Cofork.IsColimit.ofExistsUnique` expose the two universal-property directions. By contrast,
`HasCoequalizer` and `coequalizer.existsUnique` concern existence and mathlib's chosen
coequalizer, so they do not classify the supplied `c`. No generalization is introduced:
`a ≫ t = b ≫ t` translates `t ∘ a = t ∘ b`, while `c ≫ s = t` translates
`t = s ∘ c`. Reusing the colimiting-cofork owner gives downstream code the standard colimit and
cofork API without a local wrapper. -/

/- Definition 4.11.1: for parallel morphisms `a b : X ⟶ Y`, the textbook notion that
`c : Y ⟶ Z` is a coequalizer of `(a, b)` is exactly the canonical mathlib notion that the
cofork `Cofork.ofπ c h` is colimiting. -/
@[stacks 002A "coequalizer as a colimiting cofork"]
#check (IsColimit (Cofork.ofπ c h) : Type (max u v))

/- Companion recall: the unique-factorization clause in the textbook coequalizer universal
property is the canonical theorem `Cofork.IsColimit.existsUnique`. -/
#check Cofork.IsColimit.existsUnique

/- Companion recall: the converse direction from the textbook universal property to a colimiting
cofork is the canonical constructor `Cofork.IsColimit.ofExistsUnique`. -/
#check Cofork.IsColimit.ofExistsUnique

end CategoryTheory.Limits
