/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Counterexample.Basic

/-!
# Counterexample with groupoid fibres and competing lifts

This finite projection has groupoid standard fibres and two distinct named lifts of one base
arrow.  The resulting failure of cartesianness witnesses that fibrewise groupoid data does not
make arbitrary lift data into a category fibred in groupoids.
-/

@[expose] public section

namespace CategoryTheory

open Functor

namespace Functor.IsFibered.InGroupoids.Counterexample

namespace TwoLifts

/-- Objects of the source category with two distinct lifts of `WalkingComposablePair.Hom.f`. -/
inductive Obj where
  | A' | B' | T'

/-- Arrows of the source category, including two named arrows `f₁` and `f₂`. -/
inductive Hom : Obj → Obj → Type where
  | id (X : Obj) : Hom X X
  | f₁ : Hom .A' .B'
  | f₂ : Hom .A' .B'
  | g : Hom .B' .T'
  | h : Hom .A' .T'

namespace Hom

/-- Explicit composition in the source category; both `f₁ ≫ g` and `f₂ ≫ g` are `h`. -/
def comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, k => k
  | _, _, _, k, id _ => k
  | _, _, _, f₁, g => h
  | _, _, _, f₂, g => h

/-- Left identity for the explicit source composition. -/
theorem id_comp {X Y : Obj} (k : Hom X Y) : comp (id X) k = k := by
  rfl

/-- Right identity for the explicit source composition. -/
theorem comp_id {X Y : Obj} (k : Hom X Y) : comp k (id Y) = k := by
  cases k <;> rfl

/-- Associativity for the explicit source composition. -/
theorem assoc {W X Y Z : Obj} (k : Hom W X) (l : Hom X Y) (m : Hom Y Z) :
    comp (comp k l) m = comp k (comp l m) := by
  cases k <;> cases l <;> cases m <;> rfl

end Hom

/-- The category structure on the source with competing lifts. -/
instance : Category Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The object map of the competing-lifts projection. -/
def objMap : Obj → WalkingComposablePair
  | .A' => .A
  | .B' => .B
  | .T' => .T

/-- The arrow map of the competing-lifts projection. -/
def homMap : {X Y : Obj} → Hom X Y → (objMap X ⟶ objMap Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, Hom.f₁ => WalkingComposablePair.Hom.f
  | _, _, Hom.f₂ => WalkingComposablePair.Hom.f
  | _, _, Hom.g => WalkingComposablePair.Hom.g
  | _, _, Hom.h => WalkingComposablePair.Hom.h

/-- The competing-lifts projection preserves identities. -/
theorem projectionMapId (X : Obj) : homMap (𝟙 X) = 𝟙 (objMap X) := by
  rfl

/-- The competing-lifts projection preserves composition. -/
theorem projectionMapComp {X Y Z : Obj} (k : X ⟶ Y) (l : Y ⟶ Z) :
    homMap (k ≫ l) = homMap k ≫ homMap l := by
  cases k <;> cases l <;> rfl

/-- The explicit projection with two competing lifts of `WalkingComposablePair.Hom.f`. -/
def projection : Obj ⥤ WalkingComposablePair where
  obj := objMap
  map := homMap
  map_id := projectionMapId
  map_comp := projectionMapComp

/- `objMap` is explicit data.  The full `homMap` and `projection` declarations inherit
`sorryAx` only through the Prop-valued category and functor law fields; their object and arrow
data are the displayed finite pattern matches, with no chosen witness. -/

/-- Every standard fibre of the competing-lifts projection is a groupoid. -/
instance fiberIsGroupoid (U : WalkingComposablePair) : IsGroupoid (projection.Fiber U) where
  all_isIso := by
    intro X Y k
    have hinj : Function.Injective objMap := by
      intro X Y h
      cases X <;> cases Y <;> cases h <;> rfl
    have hXY : X = Y := by
      exact Subtype.ext (hinj (X.property.trans Y.property.symm))
    subst Y
    have h : ∀ {Z : Obj} (l : Hom Z Z), l = Hom.id Z := by
      intro Z l
      cases Z <;> cases l <;> rfl
    have hk : k = 𝟙 X := Subtype.ext (h (Z := X.val) k.val)
    rw [hk]
    infer_instance

/-- The first named arrow is a lift of `WalkingComposablePair.Hom.f`. -/
theorem f₁IsHomLift : projection.IsHomLift WalkingComposablePair.Hom.f Hom.f₁ := by
  exact Functor.IsHomLift.map (p := projection) (a := Obj.A') (b := Obj.B') Hom.f₁

/-- The second named arrow is a lift of `WalkingComposablePair.Hom.f`. -/
theorem f₂IsHomLift : projection.IsHomLift WalkingComposablePair.Hom.f Hom.f₂ := by
  exact Functor.IsHomLift.map (p := projection) (a := Obj.A') (b := Obj.B') Hom.f₂

/-- The two named lifts of `WalkingComposablePair.Hom.f` are distinct. -/
theorem f₁_ne_f₂ : (Hom.f₁ : Hom .A' .B') ≠ Hom.f₂ := by
  intro h
  cases h

/-- The competing-lifts projection is not fibred in groupoids. -/
theorem notInGroupoids : ¬ Functor.IsFibered.InGroupoids projection := by
  intro hp
  letI : projection.IsHomLift WalkingComposablePair.Hom.f Hom.f₂ := f₂IsHomLift
  letI : projection.IsCartesian WalkingComposablePair.Hom.f Hom.f₁ :=
    hp.all_isCartesian Hom.f₁
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ :=
    IsCartesian.universal_property (p := projection)
      (f := WalkingComposablePair.Hom.f) (φ := Hom.f₁) Hom.f₂
  cases χ
  exact f₁_ne_f₂ hχ

end TwoLifts

end Functor.IsFibered.InGroupoids.Counterexample

end CategoryTheory
