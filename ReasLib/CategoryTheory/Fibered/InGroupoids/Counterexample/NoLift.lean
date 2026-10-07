module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Counterexample.Basic

/-!
# Counterexample with groupoid fibres and a missing lift

This finite projection has groupoid standard fibres, while the named base arrow has no lift with
the prescribed endpoints.  It is a reusable witness that fibrewise groupoid data alone does not
provide fibredness.
-/

@[expose] public section

namespace CategoryTheory

open Functor

namespace Functor.IsFibered.InGroupoids.Counterexample

namespace NoLift

/-- Objects of the source category in which `WalkingComposablePair.Hom.f` has no lift. -/
inductive Obj where
  | A' | B' | T'

/-- Arrows of the source category; deliberately, there is no arrow `A' ⟶ B'`. -/
inductive Hom : Obj → Obj → Type where
  | id (X : Obj) : Hom X X
  | g : Hom .B' .T'
  | h : Hom .A' .T'

namespace Hom

/-- Explicit composition in the source category with the missing lift. -/
def comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, k => k
  | _, _, _, k, id _ => k

/-- Left identity for the explicit source composition. -/
theorem id_comp {X Y : Obj} (k : Hom X Y) : comp (id X) k = k := sorry

/-- Right identity for the explicit source composition. -/
theorem comp_id {X Y : Obj} (k : Hom X Y) : comp k (id Y) = k := sorry

/-- Associativity for the explicit source composition. -/
theorem assoc {W X Y Z : Obj} (k : Hom W X) (l : Hom X Y) (m : Hom Y Z) :
    comp (comp k l) m = comp k (comp l m) := sorry

end Hom

/-- The category structure on the source with the missing lift. -/
instance : Category Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The object map of the missing-lift projection. -/
def objMap : Obj → WalkingComposablePair
  | .A' => .A
  | .B' => .B
  | .T' => .T

/-- The arrow map of the missing-lift projection. -/
def homMap : {X Y : Obj} → Hom X Y → (objMap X ⟶ objMap Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.g => WalkingComposablePair.Hom.g
  | _, _, Hom.h => WalkingComposablePair.Hom.h

/-- The missing-lift projection preserves identities. -/
theorem projectionMapId (X : Obj) : homMap (𝟙 X) = 𝟙 (objMap X) := sorry

/-- The missing-lift projection preserves composition. -/
theorem projectionMapComp {X Y Z : Obj} (k : X ⟶ Y) (l : Y ⟶ Z) :
    homMap (k ≫ l) = homMap k ≫ homMap l := sorry

/-- The explicit projection with a missing lift of `WalkingComposablePair.Hom.f`. -/
def projection : Obj ⥤ WalkingComposablePair where
  obj := objMap
  map := homMap
  map_id := projectionMapId
  map_comp := projectionMapComp

/- `objMap` is explicit data.  The full `homMap` and `projection` declarations inherit
`sorryAx` only through the Prop-valued category and functor law fields; their object and arrow
data are the displayed finite pattern matches, with no chosen witness. -/

/-- Every standard fibre of the missing-lift projection is a groupoid. -/
instance fiberIsGroupoid (U : WalkingComposablePair) : IsGroupoid (projection.Fiber U) := sorry

/-- The base arrow `WalkingComposablePair.Hom.f` has no lift from `Obj.A'` to `Obj.B'`. -/
theorem noLiftOfF :
    ¬ ∃ φ : Hom .A' .B', projection.IsHomLift WalkingComposablePair.Hom.f φ := sorry

/-- The missing-lift projection is not fibred in groupoids. -/
theorem notInGroupoids : ¬ Functor.IsFibered.InGroupoids projection := sorry

end NoLift

end Functor.IsFibered.InGroupoids.Counterexample

end CategoryTheory
