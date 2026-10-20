module

public import ReasLib.CategoryTheory.Sites.Cover.Basic
public import ReasLib.CategoryTheory.Sites.Family
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-target family of a Grothendieck cover

A bundled Grothendieck cover already contains concrete arrows into one target.
This leaf exposes that data as `SemiRepresentableFamily.Over`, so descent and
family APIs can use a cover without rebuilding its index presentation.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology.Cover

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- The fixed-target family indexed by all arrows of a bundled Grothendieck cover. -/
def family (T : J.Cover U) : SemiRepresentableFamily.Over U where
  index := T.Arrow
  obj := fun I ↦ Over.mk I.f

/-- A member of `T.family` is the corresponding cover arrow, viewed in the slice over `U`. -/
@[simp]
theorem family_obj (T : J.Cover U) (I : T.Arrow) :
    (T.family.obj I).hom = I.f := sorry

/-- The presieve of the family associated to a cover is its explicit arrow presieve. -/
@[simp]
theorem family_toPresieve (T : J.Cover U) :
    T.family.toPresieve = Presieve.ofArrows (fun I : T.Arrow ↦ I.Y) fun I ↦ I.f := sorry

/-- The family associated to a cover generates exactly the cover's underlying sieve. -/
theorem family_toSieve (T : J.Cover U) :
    T.family.toSieve = (T : Sieve U) := sorry

end CategoryTheory.GrothendieckTopology.Cover
