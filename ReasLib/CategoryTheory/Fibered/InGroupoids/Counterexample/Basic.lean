module

public import ReasLib.CategoryTheory.Fibered.InGroupoids

/-!
# Small base category for fibred-in-groupoids counterexamples

The walking composable pair is kept as explicit finite data because the two counterexamples in
this directory expose its named arrows and their lifts.  It is a neutral support object rather
than a chapter-specific presentation.
-/

@[expose] public section

namespace CategoryTheory

namespace Functor.IsFibered.InGroupoids.Counterexample

/-- The three objects of the walking composable pair `A ⟶ B ⟶ T`. -/
inductive WalkingComposablePair where
  | A | B | T

namespace WalkingComposablePair

/-- The arrows of the walking composable pair: identities, `f : A ⟶ B`, `g : B ⟶ T`, and
`h = f ≫ g : A ⟶ T`. -/
inductive Hom : WalkingComposablePair → WalkingComposablePair → Type where
  | id (X : WalkingComposablePair) : Hom X X
  | f : Hom .A .B
  | g : Hom .B .T
  | h : Hom .A .T

namespace Hom

/-- Explicit composition in the walking composable pair. -/
def comp : {X Y Z : WalkingComposablePair} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, k => k
  | _, _, _, k, id _ => k
  | _, _, _, f, g => h

/-- Left identity for the explicit composition. -/
theorem id_comp {X Y : WalkingComposablePair} (k : Hom X Y) : comp (id X) k = k := sorry

/-- Right identity for the explicit composition. -/
theorem comp_id {X Y : WalkingComposablePair} (k : Hom X Y) : comp k (id Y) = k := sorry

/-- Associativity for the explicit composition. -/
theorem assoc {W X Y Z : WalkingComposablePair} (k : Hom W X) (l : Hom X Y) (m : Hom Y Z) :
    comp (comp k l) m = comp k (comp l m) := sorry

end Hom

/-- The category structure on the walking composable pair. -/
instance : Category WalkingComposablePair where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

end WalkingComposablePair

end Functor.IsFibered.InGroupoids.Counterexample

end CategoryTheory
