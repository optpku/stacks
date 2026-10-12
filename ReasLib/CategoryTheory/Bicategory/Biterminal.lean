/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.PUnit
public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty

@[expose] public section

universe w v u

namespace CategoryTheory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-
The invariant bicategorical formulation is that every hom-category into the biterminal object is
equivalent to the terminal category. Merely asking that such a hom-category have a terminal
object would be too weak in an arbitrary bicategory: it would not rule out other objects or
noninvertible `2`-morphisms. The equivalence-to-`PUnit` owner is the standard bicategorical
notion and, by `CategoryTheory.equiv_punit_iff_unique`, is exactly contractibility.

Some presentations state the definition only for a strict `(2,1)`-category. Neither strictness nor
local groupoidality is needed by the invariant owner below. On a `(2,1)`-category it specializes
to that formulation, since its unique comparison `2`-morphism is automatically invertible.
-/

/-- Definition 4.31.1 (Stacks 003P): an object `x` is biterminal if every hom-category `y ⟶ x`
is equivalent to the terminal category `Discrete PUnit`. -/
@[stacks 003P "biterminal object via contractible hom-categories"]
class Bicategory.IsBiterminal (x : B) : Prop where
  /-- The hom-category from any object to `x` is equivalent to the terminal category. -/
  homEquiv (y : B) : Nonempty ((y ⟶ x) ≌ Discrete PUnit.{v + 1})

/-- Biterminal objects as an object property on an arbitrary bicategory. -/
abbrev Bicategory.isBiterminal : ObjectProperty B :=
  fun x ↦ Bicategory.IsBiterminal x

/-- Biterminality is invariant under bicategorical equivalence. -/
instance Bicategory.isBiterminal.isClosedUnderEquivalences :
    (Bicategory.isBiterminal (B := B)).IsClosedUnderEquivalences := sorry

namespace Bicategory.IsBiterminal

/-- Transport biterminality across a bicategorical equivalence. -/
theorem of_equivalence {x y : B} (e : x ≌ y) (hx : IsBiterminal x) :
    IsBiterminal y := sorry

/-- Equivalent objects are biterminal simultaneously. -/
theorem iff_of_equivalence {x y : B} (e : x ≌ y) :
    IsBiterminal x ↔ IsBiterminal y := sorry

/-- There exists a `1`-morphism from every object to a biterminal object. -/
instance nonemptyHom {x y : B} [IsBiterminal x] : Nonempty (y ⟶ x) :=
  ((equiv_punit_iff_unique (C := y ⟶ x)).mp (IsBiterminal.homEquiv y)).1

/-- Between two `1`-morphisms into a biterminal object there is a unique
`2`-morphism. -/
noncomputable instance homUnique {x y : B} [IsBiterminal x] (f g : y ⟶ x) : Unique (f ⟶ g) :=
  Classical.choice (((equiv_punit_iff_unique (C := y ⟶ x)).mp
    (IsBiterminal.homEquiv y)).2 f g)

/-- Any two biterminal objects are equivalent. The equivalence remains noncanonical, so the API
exposes only its nonemptiness. -/
theorem nonemptyEquivalence (x y : B) [IsBiterminal x] [IsBiterminal y] :
    Nonempty (x ≌ y) := sorry

end Bicategory.IsBiterminal

namespace Bicategory

/-- An object `x` is biterminal precisely when every object has a `1`-morphism to `x` and every
pair of such morphisms admits a unique `2`-morphism. -/
theorem isBiterminal_iff_existsUnique_hom₂ (x : B) :
    IsBiterminal x ↔
      ∀ y : B, Nonempty (y ⟶ x) ∧
        ∀ f g : y ⟶ x, Nonempty (f ⟶ g) ∧ Subsingleton (f ⟶ g) := sorry
/- Proof strategy: apply `CategoryTheory.equiv_punit_iff_unique` pointwise, then use
`unique_iff_subsingleton_and_nonempty` to express each unique `2`-morphism as the source
existence-and-uniqueness pair. -/

end Bicategory

end CategoryTheory
