module

public import Mathlib.CategoryTheory.Functor.Hom

/-!
# Transporting a Hom bifunctor across pointwise equivalences

A family of types pointwise equivalent to the Hom-sets of a functor inherits the canonical
`Cᵒᵖ × C` action.  The construction uses mathlib's uncurried Hom-bifunctor convention and is
suited to quotient, colimit, and localization presentations of Hom-sets.
-/

@[expose] public section

universe uC vC uD vD uP

namespace CategoryTheory.Functor.HomBifunctor

open Opposite

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (F : C ⥤ D)
variable (P : C → C → Type uP)
variable (e : ∀ X Y, P X Y ≃ (F.obj X ⟶ F.obj Y))

/-- The action on a presented Hom-set, transported from precomposition and postcomposition in
the target category. -/
noncomputable def ofEquivMap {p q : Cᵒᵖ × C} (f : p ⟶ q) :
    P p.1.unop p.2 ⟶ P q.1.unop q.2 :=
  ↾fun x ↦ (e q.1.unop q.2).symm
    (F.map f.1.unop ≫ e p.1.unop p.2 x ≫ F.map f.2)

/-- The transported Hom action preserves identity morphisms. -/
theorem ofEquivMap.id (p : Cᵒᵖ × C) :
    ofEquivMap F P e (𝟙 p) = 𝟙 (P p.1.unop p.2) := sorry

/-- The transported Hom action preserves composition. -/
theorem ofEquivMap.comp {p q r : Cᵒᵖ × C} (f : p ⟶ q) (g : q ⟶ r) :
    ofEquivMap F P e (f ≫ g) = ofEquivMap F P e f ≫ ofEquivMap F P e g := sorry

/-- The Hom bifunctor carried by a pointwise Hom-set presentation. -/
noncomputable def ofEquiv : Cᵒᵖ × C ⥤ Type uP where
  obj p := P p.1.unop p.2
  map f := ofEquivMap F P e f
  map_id := ofEquivMap.id F P e
  map_comp := ofEquivMap.comp F P e

/-- The value of the transported Hom bifunctor is the original type family. -/
@[simp]
theorem ofEquiv.obj (p : Cᵒᵖ × C) :
    (ofEquiv F P e).obj p = P p.1.unop p.2 := sorry

/-- The action of the transported Hom bifunctor is conjugation by the pointwise
equivalences. -/
@[simp]
theorem ofEquiv.map {p q : Cᵒᵖ × C} (f : p ⟶ q) (x : P p.1.unop p.2) :
    (ofEquiv F P e).map f x =
      (e q.1.unop q.2).symm
        (F.map f.1.unop ≫ e p.1.unop p.2 x ≫ F.map f.2) := sorry

/-- In the source variable, the transported Hom bifunctor acts by precomposition. -/
@[simp]
theorem ofEquiv.map_left {X X' Y : C} (f : X' ⟶ X) (x : P X Y) :
    (ofEquiv F P e).map
        ((f.op, 𝟙 Y) : (Opposite.op X, Y) ⟶ (Opposite.op X', Y)) x =
      (e X' Y).symm (F.map f ≫ e X Y x) := sorry

/-- In the target variable, the transported Hom bifunctor acts by postcomposition. -/
@[simp]
theorem ofEquiv.map_right {X Y Y' : C} (g : Y ⟶ Y') (x : P X Y) :
    (ofEquiv F P e).map
        ((𝟙 (Opposite.op X), g) : (Opposite.op X, Y) ⟶ (Opposite.op X, Y')) x =
      (e X Y').symm (e X Y x ≫ F.map g) := sorry

/-- The presenting equivalences intertwine the transported action with precomposition and
postcomposition in the target category.  This elementwise form remains available when the
presentation and target Hom-sets live in different universes. -/
theorem ofEquiv.naturality {p q : Cᵒᵖ × C} (f : p ⟶ q)
    (x : P p.1.unop p.2) :
    e q.1.unop q.2 ((ofEquiv F P e).map f x) =
      F.map f.1.unop ≫ e p.1.unop p.2 x ≫ F.map f.2 := sorry

/-- The presenting equivalences intertwine the source action with precomposition. -/
theorem ofEquiv.naturality_left {X X' Y : C} (f : X' ⟶ X) (x : P X Y) :
    e X' Y
        ((ofEquiv F P e).map
          ((f.op, 𝟙 Y) : (Opposite.op X, Y) ⟶ (Opposite.op X', Y)) x) =
      F.map f ≫ e X Y x := sorry

/-- The presenting equivalences intertwine the target action with postcomposition. -/
theorem ofEquiv.naturality_right {X Y Y' : C} (g : Y ⟶ Y') (x : P X Y) :
    e X Y'
        ((ofEquiv F P e).map
          ((𝟙 (Opposite.op X), g) : (Opposite.op X, Y) ⟶ (Opposite.op X, Y')) x) =
      e X Y x ≫ F.map g := sorry

section Comparison

variable (P : C → C → Type vD)
variable (e : ∀ X Y, P X Y ≃ (F.obj X ⟶ F.obj Y))

/-- The pointwise isomorphism from the transported presentation to the Hom bifunctor of `F`. -/
noncomputable def ofEquivIsoApp (p : Cᵒᵖ × C) :
    (ofEquiv F P e).obj p ≅
      ((Functor.prod F.op F ⋙ Functor.hom D).obj p) :=
  (e p.1.unop p.2).toIso

/-- The pointwise presentation isomorphisms are natural in both Hom variables. -/
theorem ofEquivIsoApp.naturality {p q : Cᵒᵖ × C} (f : p ⟶ q) :
    (ofEquiv F P e).map f ≫ (ofEquivIsoApp F P e q).hom =
      (ofEquivIsoApp F P e p).hom ≫
        (Functor.prod F.op F ⋙ Functor.hom D).map f := sorry

/-- The transported presentation is naturally isomorphic to the Hom bifunctor obtained by
applying `F` in both variables. -/
noncomputable def ofEquivIso :
    ofEquiv F P e ≅ Functor.prod F.op F ⋙ Functor.hom D :=
  NatIso.ofComponents (ofEquivIsoApp F P e) (ofEquivIsoApp.naturality F P e)

/-- The forward component of `ofEquivIso` is the supplied pointwise equivalence. -/
@[simp]
theorem ofEquivIso.hom.app_apply (p : Cᵒᵖ × C) (x : P p.1.unop p.2) :
    (ofEquivIso F P e).hom.app p x = e p.1.unop p.2 x := sorry

/-- The inverse component of `ofEquivIso` is the inverse supplied pointwise equivalence. -/
@[simp]
theorem ofEquivIso.inv.app_apply (p : Cᵒᵖ × C)
    (f : F.obj p.1.unop ⟶ F.obj p.2) :
    (ofEquivIso F P e).inv.app p f = (e p.1.unop p.2).symm f := sorry

end Comparison

end CategoryTheory.Functor.HomBifunctor
