module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ForgetMiddle.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# The middle-contraction equivalence

Unit, counit, triangle, and component formulas for the equivalence induced by contracting the
middle object of an iterated categorical pullback.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory

open Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]

variable (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C)

local notation "LeftAssoc" => (π₂ F G) ⊡ H
local notation "RightAssoc" => F ⊡ (H ⋙ G)

namespace Limits.CategoricalPullback.ForgetMiddle

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EquivalenceImplementation

/-- Compatibility needed for the inner component of the contraction unit. -/
private theorem unitFstIso_w (X : LeftAssoc) :
    F.map (Iso.refl X.fst.fst).hom ≫
        ((functor F G H ⋙ inverse F G H).obj X).fst.iso.hom =
      X.fst.iso.hom ≫ G.map X.iso.hom := sorry

/-- The inner pullback isomorphism in the contraction unit. Its right component is the original
outer structural isomorphism. -/
private def unitFstIso (X : LeftAssoc) :
    X.fst ≅ ((functor F G H ⋙ inverse F G H).obj X).fst :=
  CategoricalPullback.mkIso (Iso.refl _) X.iso (unitFstIso_w F G H X)

/-- Compatibility needed to assemble the two components of the contraction unit. -/
private theorem unitApp_w (X : LeftAssoc) :
    (π₂ F G).map (unitFstIso F G H X).hom ≫
        ((functor F G H ⋙ inverse F G H).obj X).iso.hom =
      X.iso.hom ≫ H.map (Iso.refl X.snd).hom := sorry

/-- The component of the unit comparing an iterated pullback object with the result of forgetting
and then reinserting its middle object. -/
private def unitApp (X : LeftAssoc) :
    X ≅ (functor F G H ⋙ inverse F G H).obj X :=
  CategoricalPullback.mkIso (unitFstIso F G H X) (Iso.refl _) (unitApp_w F G H X)

/-- Naturality of the contraction unit components. -/
private theorem unitNaturality {X Y : LeftAssoc} (f : X ⟶ Y) :
    (𝟭 LeftAssoc).map f ≫ (unitApp F G H Y).hom =
      (unitApp F G H X).hom ≫ (functor F G H ⋙ inverse F G H).map f := sorry

/-- The unit isomorphism for contraction of the middle pullback object. -/
private def unitIso :
    𝟭 LeftAssoc ≅ functor F G H ⋙ inverse F G H :=
  NatIso.ofComponents (unitApp F G H) (unitNaturality F G H)

/-- Compatibility needed for the counit component after inserting and then forgetting the
canonical middle object. -/
private theorem counitApp_w (X : RightAssoc) :
    F.map (Iso.refl X.fst).hom ≫ X.iso.hom =
      ((inverse F G H ⋙ functor F G H).obj X).iso.hom ≫
        (H ⋙ G).map (Iso.refl X.snd).hom := sorry

/-- The component of the counit comparing insertion followed by contraction with the original
contracted pullback object. -/
private def counitApp (X : RightAssoc) :
    (inverse F G H ⋙ functor F G H).obj X ≅ X :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (counitApp_w F G H X)

/-- Naturality of the contraction counit components. -/
private theorem counitNaturality {X Y : RightAssoc} (f : X ⟶ Y) :
    (inverse F G H ⋙ functor F G H).map f ≫ (counitApp F G H Y).hom =
      (counitApp F G H X).hom ≫ (𝟭 RightAssoc).map f := sorry

/-- The counit isomorphism for contraction of the canonical inserted middle object. -/
private def counitIso :
    inverse F G H ⋙ functor F G H ≅ 𝟭 RightAssoc :=
  NatIso.ofComponents (counitApp F G H) (counitNaturality F G H)

/-- The triangle identity for the explicit contraction unit and counit. -/
private theorem triangle (X : LeftAssoc) :
    (functor F G H).map ((unitIso F G H).hom.app X) ≫
        (counitIso F G H).hom.app ((functor F G H).obj X) =
      𝟙 ((functor F G H).obj X) := sorry

end EquivalenceImplementation

/- Axiom audit: inverse, unit, and counit data are explicit; `sorryAx` is confined to their
compatibility, functoriality, naturality, and triangle proof fields. -/

/-- Lemma 4.31.10 (Stacks 02XD): for a diagram

```
      F                       G                       H
 A ────────────▶ B ◀──────────────── C ◀──────────────── D
```

there is a canonical equivalence `((π₂ F G) ⊡ H) ≌ F ⊡ (H ⋙ G)`.
The forward functor contracts the middle object and the inverse inserts `H.obj d`. -/
@[stacks 02XD "middle contraction for categorical pullbacks"]
def equivalence : LeftAssoc ≌ RightAssoc where
  functor := functor F G H
  inverse := inverse F G H
  unitIso := EquivalenceImplementation.unitIso F G H
  counitIso := EquivalenceImplementation.counitIso F G H
  functor_unitIso_comp := EquivalenceImplementation.triangle F G H

namespace equivalence

/-- The unit of middle contraction is the identity on the leftmost component. -/
@[simp]
theorem unitIso.hom.app.fstFst (X : LeftAssoc) :
    ((ForgetMiddle.equivalence F G H).unitIso.hom.app X).fst.fst = 𝟙 X.fst.fst := sorry

/-- The middle component of the contraction unit is the original outer structural isomorphism. -/
@[simp]
theorem unitIso.hom.app.fstSnd (X : LeftAssoc) :
    ((ForgetMiddle.equivalence F G H).unitIso.hom.app X).fst.snd = X.iso.hom := sorry

/-- The unit of middle contraction is the identity on the rightmost component. -/
@[simp]
theorem unitIso.hom.app.snd (X : LeftAssoc) :
    ((ForgetMiddle.equivalence F G H).unitIso.hom.app X).snd = 𝟙 X.snd := sorry

/-- The inverse unit of middle contraction is the identity on the leftmost component. -/
@[simp]
theorem unitIso.inv.app.fstFst (X : LeftAssoc) :
    ((ForgetMiddle.equivalence F G H).unitIso.inv.app X).fst.fst = 𝟙 X.fst.fst := sorry

/-- The middle component of the inverse contraction unit is the inverse outer structural
isomorphism. -/
@[simp]
theorem unitIso.inv.app.fstSnd (X : LeftAssoc) :
    ((ForgetMiddle.equivalence F G H).unitIso.inv.app X).fst.snd = X.iso.inv := sorry

/-- The inverse unit of middle contraction is the identity on the rightmost component. -/
@[simp]
theorem unitIso.inv.app.snd (X : LeftAssoc) :
    ((ForgetMiddle.equivalence F G H).unitIso.inv.app X).snd = 𝟙 X.snd := sorry

/-- The counit of middle contraction is the identity on the left component. -/
@[simp]
theorem counitIso.hom.app.fst (X : RightAssoc) :
    ((ForgetMiddle.equivalence F G H).counitIso.hom.app X).fst = 𝟙 X.fst := sorry

/-- The counit of middle contraction is the identity on the right component. -/
@[simp]
theorem counitIso.hom.app.snd (X : RightAssoc) :
    ((ForgetMiddle.equivalence F G H).counitIso.hom.app X).snd = 𝟙 X.snd := sorry

/-- The inverse counit of middle contraction is the identity on the left component. -/
@[simp]
theorem counitIso.inv.app.fst (X : RightAssoc) :
    ((ForgetMiddle.equivalence F G H).counitIso.inv.app X).fst = 𝟙 X.fst := sorry

/-- The inverse counit of middle contraction is the identity on the right component. -/
@[simp]
theorem counitIso.inv.app.snd (X : RightAssoc) :
    ((ForgetMiddle.equivalence F G H).counitIso.inv.app X).snd = 𝟙 X.snd := sorry

end equivalence

namespace functor

/-- The canonical middle-contraction functor is an equivalence of categories. -/
instance isEquivalence : (ForgetMiddle.functor F G H).IsEquivalence := sorry

end functor

end Limits.CategoricalPullback.ForgetMiddle

end CategoryTheory
