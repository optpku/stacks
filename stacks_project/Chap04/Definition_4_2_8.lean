/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Basic
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]

/-
`Functor` is the single canonical owner of the object map, morphism map, and the two functoriality
laws. Recalling its individual fields would split one source definition into redundant surfaces;
keeping the owner intact gives downstream items the standard `obj`, `map`, `map_id`, and
`map_comp` API without a parallel wrapper.
-/

/- Definition 4.2.8: the canonical owner notion of a functor from `C` to `D` is the structure
`CategoryTheory.Functor`, written `C ⥤ D`. Its primitive data are the object map, morphism map,
and the identity- and composition-preservation laws. -/
@[stacks 001B "functor structure"]
#check (Functor C D : Type max v₁ v₂ u₁ u₂)

end CategoryTheory
