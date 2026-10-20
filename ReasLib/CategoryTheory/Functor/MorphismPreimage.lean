module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise fullness of functors

This file isolates the property that one specified morphism lies in the image of a functor on
morphisms.  It is the pointwise form of `Functor.Full` and is useful when fullness holds only
locally or for a distinguished family of morphisms.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D} {X Y Z : C}

/-- A morphism between objects in the image of `F` has a preimage under `F.map`. -/
@[stacks 01BL "pointwise fullness"]
def HasPreimage (F : C ⥤ D) {X Y : C} (f : F.obj X ⟶ F.obj Y) : Prop :=
  ∃ g : X ⟶ Y, F.map g = f

namespace HasPreimage

/-- Every morphism obtained by applying `F.map` has a preimage. -/
@[stacks 01BL "mapped morphism"]
theorem map (F : C ⥤ D) (f : X ⟶ Y) :
    F.HasPreimage (F.map f) := sorry

/-- Identity morphisms have preimages. -/
theorem id (F : C ⥤ D) (X : C) : F.HasPreimage (𝟙 (F.obj X)) := sorry

/-- Pointwise preimages are closed under composition. -/
theorem comp {f : F.obj X ⟶ F.obj Y} {g : F.obj Y ⟶ F.obj Z}
    (hf : F.HasPreimage f) (hg : F.HasPreimage g) :
    F.HasPreimage (f ≫ g) := sorry

/-- A full functor has a preimage for every morphism between objects in its image. -/
theorem of_full (F : C ⥤ D) [F.Full] (f : F.obj X ⟶ F.obj Y) :
    F.HasPreimage f := sorry

/-- Pointwise existence of a preimage is invariant under conjugation by a natural isomorphism. -/
theorem natIso_iff (e : F ≅ G) (f : F.obj X ⟶ F.obj Y) :
    F.HasPreimage f ↔
      G.HasPreimage (e.inv.app X ≫ f ≫ e.hom.app Y) := sorry

/-- Fullness is equivalent to pointwise existence of preimages for all morphisms. -/
theorem full_iff (F : C ⥤ D) :
    F.Full ↔ ∀ {X Y : C} (f : F.obj X ⟶ F.obj Y), F.HasPreimage f := sorry

end HasPreimage

end CategoryTheory.Functor
