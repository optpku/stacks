/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom-categories with groupoidal target

Natural transformations into a groupoid are invertible, so the corresponding hom-category in
`Cat` is itself a groupoid.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace Cat

/-- If the target category is a groupoid, the hom-category in `Cat` is a groupoid. This applies
to every category-valued target with an `IsGroupoid` instance, not only to bundled `Grpd`
objects. -/
@[stacks 003J "groupoidal target hom-category"]
instance homIsGroupoid (C D : Cat.{v, u}) [IsGroupoid D] : IsGroupoid (C ⟶ D) := sorry
/- Proof strategy: for a `2`-morphism `η`, every component of `η.toNatTrans` is invertible
because `D` is a groupoid. Use `NatIso.isIso_of_isIso_app`, form `asIso η.toNatTrans`, and lift
that natural isomorphism with `Cat.Hom.isoMk`; `Cat.Hom₂.ext` identifies its forward cell with
`η`. -/

end Cat

end CategoryTheory
