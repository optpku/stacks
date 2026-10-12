/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.Iteration.Positive
public import ReasLib.CategoryTheory.Center.Whiskering

/-!
# Central actions on positive endofunctor iterates

This leaf inserts a categorical central endomorphism at a chosen position of a positive
endofunctor iterate and bundles the resulting action as a monoid homomorphism.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.IteratedEndofunctor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IteratedEndofunctor

/-- Insert a central endomorphism between the two positive-iterate blocks selected by `j`.  This
is the formal version of the horizontal composite `1 ⋆ z ⋆ 1`. -/
@[stacks 0G5S "a central endomorphism inserted in a positive iterate"]
def centerAt (Y : C ⥤ C) (z : CatCenter C) (n : ℕ) (j : Fin (n + 1)) :
    Y ⁺⦋n + 1⦌ ⟶ Y ⁺⦋n + 1⦌ :=
  (splitIso Y n j).hom ≫
    Functor.whiskerLeft (Y ⁺⦋n - j.1⦌) (Functor.whiskerRight z (Y ⁺⦋j.1⦌)) ≫
    (splitIso Y n j).inv

/-- Inserting the identity central endomorphism gives the identity of the positive iterate. -/
@[simp, stacks 0G5M "identity central insertion"]
theorem centerAt.one (Y : C ⥤ C) (n : ℕ) (j : Fin (n + 1)) :
    centerAt Y (1 : CatCenter C) n j = 𝟙 (Y ⁺⦋n + 1⦌) := sorry

/-- Insertion of a product of central endomorphisms is multiplication of their insertions. -/
@[simp, stacks 0G5M "multiplicativity of central insertion"]
theorem centerAt.mul (Y : C ⥤ C) (z w : CatCenter C) (n : ℕ) (j : Fin (n + 1)) :
    centerAt Y (z * w) n j =
      End.of (centerAt Y z n j) * End.of (centerAt Y w n j) := sorry

/-- Insertion at a fixed position, bundled as a monoid homomorphism from the category center. -/
@[stacks 0G5S "central insertion action on a positive iterate"]
def centerAt.hom (Y : C ⥤ C) (n : ℕ) (j : Fin (n + 1)) :
    CatCenter C →* End (Y ⁺⦋n + 1⦌) where
  toFun z := centerAt Y z n j
  map_one' := centerAt.one Y n j
  map_mul' z w := centerAt.mul Y z w n j

end IteratedEndofunctor

end CategoryTheory
