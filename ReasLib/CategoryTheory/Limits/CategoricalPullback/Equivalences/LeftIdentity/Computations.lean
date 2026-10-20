module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftIdentity.Equivalence

/-!
# Computations for the left-identity categorical-pullback equivalence

Object, morphism, and unit/counit formulas for `LeftIdentity.equivalence`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory.Limits.CategoricalPullback.LeftIdentity

universe vB vC uB uC

variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable (G : B ⥤ C)

namespace inverse

/-- The first coordinate inserted by the left-identity inverse is the image under `G`. -/
@[simp]
theorem obj.fst (x : B) :
    ((LeftIdentity.inverse G).obj x).fst = G.obj x := sorry

/-- The left-identity inverse retains its source object as the second coordinate. -/
@[simp]
theorem obj.snd (x : B) :
    ((LeftIdentity.inverse G).obj x).snd = x := sorry

/-- The structural isomorphism inserted by the left-identity inverse is the identity. -/
@[simp]
theorem obj.iso (x : B) :
    ((LeftIdentity.inverse G).obj x).iso = Iso.refl (G.obj x) := sorry

/-- On first morphism components, the left-identity inverse applies `G`. -/
@[simp]
theorem map.fst {x y : B} (f : x ⟶ y) :
    ((LeftIdentity.inverse G).map f).fst = G.map f := sorry

/-- On second morphism components, the left-identity inverse retains the supplied morphism. -/
@[simp]
theorem map.snd {x y : B} (f : x ⟶ y) :
    ((LeftIdentity.inverse G).map f).snd = f := sorry

end inverse

namespace equivalence

/-- The forward functor of the left-identity equivalence is the second projection. -/
@[simp]
theorem functor :
    (LeftIdentity.equivalence G).functor = π₂ (Functor.id C) G := sorry

/-- The inverse functor of the left-identity equivalence is the explicit insertion functor. -/
@[simp]
theorem inverse :
    (LeftIdentity.equivalence G).inverse = LeftIdentity.inverse G := sorry

/-- The first component of the left-identity unit is the pullback structural isomorphism. -/
@[simp]
theorem unitIso.hom.app.fst (x : (Functor.id C) ⊡ G) :
    ((LeftIdentity.equivalence G).unitIso.hom.app x).fst = x.iso.hom := sorry

/-- The second component of the left-identity unit is the identity. -/
@[simp]
theorem unitIso.hom.app.snd (x : (Functor.id C) ⊡ G) :
    ((LeftIdentity.equivalence G).unitIso.hom.app x).snd = 𝟙 x.snd := sorry

/-- The first component of the inverse left-identity unit is the inverse structural
isomorphism. -/
@[simp]
theorem unitIso.inv.app.fst (x : (Functor.id C) ⊡ G) :
    ((LeftIdentity.equivalence G).unitIso.inv.app x).fst = x.iso.inv := sorry

/-- The second component of the inverse left-identity unit is the identity. -/
@[simp]
theorem unitIso.inv.app.snd (x : (Functor.id C) ⊡ G) :
    ((LeftIdentity.equivalence G).unitIso.inv.app x).snd = 𝟙 x.snd := sorry

/-- The counit of the left-identity equivalence is objectwise the identity. -/
@[simp]
theorem counitIso.hom.app (x : B) :
    (LeftIdentity.equivalence G).counitIso.hom.app x = 𝟙 x := sorry

/-- The inverse counit of the left-identity equivalence is objectwise the identity. -/
@[simp]
theorem counitIso.inv.app (x : B) :
    (LeftIdentity.equivalence G).counitIso.inv.app x = 𝟙 x := sorry

end equivalence

end CategoryTheory.Limits.CategoricalPullback.LeftIdentity
