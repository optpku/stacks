/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- Import decisions:
-- * `Endomorphism` is public because the bridge theorem exposes `Aut X`.
-- * `Groupoid.Basic` is public because `IsGroupoid`, `Quiver.IsThin`, and their canonical
--   groupoid bridge are the exported mathematical owners.
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Thin groupoids

A thin groupoid has only identity automorphisms, and conversely objectwise trivial
automorphism groups force a groupoid to be thin.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
A setoid is canonically presented by a thin groupoid:
`IsGroupoid C` says every arrow is invertible, while `Quiver.IsThin C` says every hom-type is a
subsingleton. Equivalently, the relation `X ~ Y :↔ Nonempty (X ⟶ Y)` is an equivalence relation
and an existing arrow is its unique witness.

This is weaker than `IsDiscrete C`: distinct but isomorphic objects may remain distinct. It is
also invariant under categorical equivalence, which is the property needed by the replete
fibred-in-setoids owner downstream. Introducing an alias such as `IsSetoidCategory C` would only
hide these two standard typeclass assumptions and reduce reuse, so the canonical owners are
used directly.
-/

/-- Definition 4.39.1 (Stacks 02XZ): for a groupoid, thinness is equivalent to every object
having a subsingleton automorphism type. -/
@[stacks 02XZ "groupoids with only identity automorphisms"]
theorem isThin_iff_subsingleton_aut [IsGroupoid C] :
    Quiver.IsThin C ↔ ∀ X : C, Subsingleton (Aut X) := sorry
/- Proof strategy: install `Groupoid.ofIsGroupoid`, apply `Groupoid.isThin_iff`, and transport
`Subsingleton` between `X ⟶ X` and `Aut X` along `Groupoid.isoEquivHom X X`. -/

end CategoryTheory
