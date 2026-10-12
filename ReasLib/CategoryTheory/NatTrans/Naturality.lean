/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Functor.Category

namespace CategoryTheory.NatTrans

/-- A natural transformation commutes with the action of each morphism. -/
public theorem naturality_square {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (c : F ⟶ G) {X X' : C} (f : X ⟶ X') :
    F.map f ≫ c.app X' = c.app X ≫ G.map f := sorry

end CategoryTheory.NatTrans
