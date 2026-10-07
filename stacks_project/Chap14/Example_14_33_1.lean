module

public import ReasLib.CategoryTheory.Endofunctor.Iteration.Simplicial
import StacksCheckRecall

@[expose] public section

/-!
@stack 0G5M

# Example 14.33.1

The reusable zero-based iterate API and the source-facing positive-iterate, factor-splitting, face,
and degeneracy API are owned by `ReasLib.CategoryTheory.Endofunctor.Iteration.Simplicial`.
-/

open CategoryTheory
open scoped CategoryTheory.IteratedEndofunctor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (n : ℕ)

/- Example 14.33.1 (1): an endofunctor has left-associated positive iterates. -/
@[stacks 0G5M "Example 14.33.1 (1)"]
#check (IteratedEndofunctor.obj : (C ⥤ C) → ℕ → C ⥤ C)

#check (Endofunctor.iterate : (C ⥤ C) → ℕ → C ⥤ C)
#check Endofunctor.iterate.functor
#check Endofunctor.iterate.oneNatIso

/- Example 14.33.1 (2): a positive iterate splits canonically into two consecutive blocks. -/
@[stacks 0G5M "Example 14.33.1 (2)"]
#check (IteratedEndofunctor.compIso :
  (Y : C ⥤ C) → (n m : ℕ) → Y ⁺⦋n + m + 1⦌ ≅ ((Y ⁺⦋n⦌) ⋙ Y ⁺⦋m⦌))

#check Endofunctor.iterate.addIso
#check Endofunctor.iterate.addNatIso
#check Endofunctor.iterate.addIso.assoc
#check Endofunctor.iterate.addIso.hom.naturality
#check Endofunctor.iterate.addIso.inv.naturality

/- Example 14.33.1 (3): inserting a counit-like transformation defines the face maps. -/
@[stacks 0G5M "Example 14.33.1 (3)"]
#check (IteratedEndofunctor.face d n :
  Fin (n + 2) → (Y ⁺⦋n + 1⦌ ⟶ Y ⁺⦋n⦌))

/- Example 14.33.1 (4): inserting a comultiplication-like transformation defines the degeneracy
maps. -/
@[stacks 0G5M "Example 14.33.1 (4)"]
#check (IteratedEndofunctor.degeneracy s n :
  Fin (n + 1) → (Y ⁺⦋n⦌ ⟶ Y ⁺⦋n + 1⦌))

end CategoryTheory
