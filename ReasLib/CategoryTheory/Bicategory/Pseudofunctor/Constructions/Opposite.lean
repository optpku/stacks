module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
# Opposite pseudofunctors

The pseudofunctor obtained by reversing `1`-morphisms in both source and
target bicategories.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

universe wC vC uC

variable {B : Type u} [Bicategory.{w, v} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

section OppositeImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The implementation-level prelax core obtained by reversing the `1`-morphisms in both
the source and target of a pseudofunctor. -/
private def opPrelax (F : B ⥤ᵖ C) : PrelaxFunctor Bᵒᵖ Cᵒᵖ :=
  PrelaxFunctor.mkOfHomFunctors
    (fun X ↦ Opposite.op (F.obj (Opposite.unop X)))
    (fun X Y ↦
      Bicategory.Opposite.unopFunctor X Y ⋙
        F.mapFunctor (Opposite.unop Y) (Opposite.unop X) ⋙
          Bicategory.Opposite.opFunctor
            (F.obj (Opposite.unop Y)) (F.obj (Opposite.unop X)))

/-- The identity comparison for the opposite pseudofunctor. -/
private def opMapIdIso (F : B ⥤ᵖ C) (X : Bᵒᵖ) :
    (opPrelax F).map (𝟙 X) ≅ 𝟙 ((opPrelax F).obj X) :=
  (F.mapId (Opposite.unop X)).op2

/-- The composition comparison for the opposite pseudofunctor. -/
private def opMapCompIso (F : B ⥤ᵖ C) {X Y Z : Bᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (opPrelax F).map (f ≫ g) ≅ (opPrelax F).map f ≫ (opPrelax F).map g :=
  (F.mapComp g.unop f.unop).op2

/-- The opposite pseudofunctor preserves left whiskering. -/
private theorem opMap₂WhiskerLeft (F : B ⥤ᵖ C) :
    ∀ {X Y Z : Bᵒᵖ} (f : X ⟶ Y) {g h : Y ⟶ Z} (η : g ⟶ h),
      (opPrelax F).map₂ (f ◁ η) =
        (opMapCompIso F f g).hom ≫
          (opPrelax F).map f ◁ (opPrelax F).map₂ η ≫
          (opMapCompIso F f h).inv := sorry
/- Proof strategy: apply `unop2`, use `F.map₂_whisker_right` on `η.unop2` and
`f.unop`, and translate opposite whiskering and composition definitionally. -/

/-- The opposite pseudofunctor preserves right whiskering. -/
private theorem opMap₂WhiskerRight (F : B ⥤ᵖ C) :
    ∀ {X Y Z : Bᵒᵖ} {f g : X ⟶ Y} (η : f ⟶ g) (h : Y ⟶ Z),
      (opPrelax F).map₂ (η ▷ h) =
        (opMapCompIso F f h).hom ≫
          (opPrelax F).map₂ η ▷ (opPrelax F).map h ≫
          (opMapCompIso F g h).inv := sorry
/- Proof strategy: apply `unop2`, use `F.map₂_whisker_left` on `h.unop` and
`η.unop2`, and translate opposite whiskering and composition definitionally. -/

/-- The opposite pseudofunctor preserves the associator. -/
private theorem opMap₂Associator (F : B ⥤ᵖ C) :
    ∀ {W X Y Z : Bᵒᵖ} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
      (opPrelax F).map₂ (α_ f g h).hom =
        (opMapCompIso F (f ≫ g) h).hom ≫
          (opMapCompIso F f g).hom ▷ (opPrelax F).map h ≫
          (α_ ((opPrelax F).map f) ((opPrelax F).map g)
            ((opPrelax F).map h)).hom ≫
          (opPrelax F).map f ◁ (opMapCompIso F g h).inv ≫
          (opMapCompIso F f (g ≫ h)).inv := sorry
/- Proof strategy: apply `unop2` and reduce to `F.map₂_associator` with the order
`h.unop`, `g.unop`, `f.unop`; the opposite associator reverses this order. -/

/-- The opposite pseudofunctor preserves the left unitor. -/
private theorem opMap₂LeftUnitor (F : B ⥤ᵖ C) :
    ∀ {X Y : Bᵒᵖ} (f : X ⟶ Y),
      (opPrelax F).map₂ (λ_ f).hom =
        (opMapCompIso F (𝟙 X) f).hom ≫
          (opMapIdIso F X).hom ▷ (opPrelax F).map f ≫
          (λ_ ((opPrelax F).map f)).hom := sorry
/- Proof strategy: apply `unop2` and use `F.map₂_right_unitor` on `f.unop`; left and
right unitors are interchanged by the `1`-cell opposite. -/

/-- The opposite pseudofunctor preserves the right unitor. -/
private theorem opMap₂RightUnitor (F : B ⥤ᵖ C) :
    ∀ {X Y : Bᵒᵖ} (f : X ⟶ Y),
      (opPrelax F).map₂ (ρ_ f).hom =
        (opMapCompIso F f (𝟙 Y)).hom ≫
          (opPrelax F).map f ◁ (opMapIdIso F Y).hom ≫
          (ρ_ ((opPrelax F).map f)).hom := sorry
/- Proof strategy: apply `unop2` and use `F.map₂_left_unitor` on `f.unop`; right and
left unitors are interchanged by the `1`-cell opposite. -/

end Implementation

/-- The pseudofunctor obtained by reversing the `1`-morphisms in both source and target.
This is the reusable contravariance bridge for representable Cat-valued pseudofunctors. -/
def op (F : B ⥤ᵖ C) : Bᵒᵖ ⥤ᵖ Cᵒᵖ where
  toPrelaxFunctor := Implementation.opPrelax F
  mapId := Implementation.opMapIdIso F
  mapComp := Implementation.opMapCompIso F
  map₂_whisker_left := Implementation.opMap₂WhiskerLeft F
  map₂_whisker_right := Implementation.opMap₂WhiskerRight F
  map₂_associator := Implementation.opMap₂Associator F
  map₂_left_unitor := Implementation.opMap₂LeftUnitor F
  map₂_right_unitor := Implementation.opMap₂RightUnitor F

end OppositeImplementation

end Pseudofunctor

end CategoryTheory
