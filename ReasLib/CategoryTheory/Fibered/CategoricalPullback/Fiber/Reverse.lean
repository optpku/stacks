module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Choice-free reverse comparison of categorical-pullback fibers

This module embeds the strict fiber of the right leg into the fiber of the
first categorical-pullback projection.  It has no cleavage parameter and is
therefore the choice-free half of the fiber comparison.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor

namespace Limits.CategoricalPullback

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- A strict right-fiber object determines an object in the corresponding fiber of the first
categorical-pullback projection. -/
noncomputable def Fiber.reverse.obj
    (u : C ⥤ D) (p : S ⥤ D) {U : C} (X : p.Fiber (u.obj U)) :
    (π₁ u p).Fiber U :=
  ⟨{ fst := U
     snd := X.1
     iso := eqToIso X.2.symm },
    rfl⟩

/-- Compatibility of the categorical-pullback morphism induced by a right-fiber morphism. -/
theorem Fiber.reverse.hom.compatibility
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    u.map (𝟙 U) ≫ (Fiber.reverse.obj u p Y).1.iso.hom =
      (Fiber.reverse.obj u p X).1.iso.hom ≫ p.map φ.1 := sorry

/-- The ambient categorical-pullback morphism induced by a morphism in the right fiber. -/
def Fiber.reverse.hom
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    (Fiber.reverse.obj u p X).1 ⟶
      (Fiber.reverse.obj u p Y).1 where
  fst := 𝟙 U
  snd := φ.1
  w := Fiber.reverse.hom.compatibility u p φ

/-- The first component of the ambient pullback map induced from a right-fiber map is the
identity of the fixed base object. -/
@[simp]
theorem Fiber.reverse.hom.fst
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    (Fiber.reverse.hom u p φ).fst = 𝟙 U := sorry

/-- The second component of the ambient pullback map induced from a right-fiber map is the
original fiber map. -/
@[simp]
theorem Fiber.reverse.hom.snd
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    (Fiber.reverse.hom u p φ).snd = φ.1 := sorry

/-- The ambient morphism induced by a right-fiber morphism lies over the identity of the
pullback base. -/
theorem Fiber.reverse.hom.isHomLift
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    (π₁ u p).IsHomLift (𝟙 U)
      (Fiber.reverse.hom u p φ) := sorry

/-- A morphism in the right fiber induces a morphism in the fiber of the first pullback
projection. -/
def Fiber.reverse.map
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    Fiber.reverse.obj u p X ⟶
      Fiber.reverse.obj u p Y :=
  ⟨Fiber.reverse.hom u p φ,
    Fiber.reverse.hom.isHomLift u p φ⟩

/-- The right-fiber construction preserves identity morphisms. -/
theorem Fiber.reverse.map.id
    (u : C ⥤ D) (p : S ⥤ D) {U : C} (X : p.Fiber (u.obj U)) :
    Fiber.reverse.map u p (𝟙 X) =
      𝟙 (Fiber.reverse.obj u p X) := sorry

/-- The right-fiber construction preserves composition. -/
theorem Fiber.reverse.map.comp
    (u : C ⥤ D) (p : S ⥤ D) {U : C}
    {X Y Z : p.Fiber (u.obj U)} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    Fiber.reverse.map u p (φ ≫ ψ) =
      Fiber.reverse.map u p φ ≫
        Fiber.reverse.map u p ψ := sorry

/-- The canonical functor from the right fiber to the corresponding fiber of the first
categorical-pullback projection. -/
noncomputable def Fiber.reverse.functor
    (u : C ⥤ D) (p : S ⥤ D) (U : C) :
    p.Fiber (u.obj U) ⥤ (π₁ u p).Fiber U where
  obj X := Fiber.reverse.obj u p X
  map φ := Fiber.reverse.map u p φ
  map_id X := Fiber.reverse.map.id u p X
  map_comp φ ψ := Fiber.reverse.map.comp u p φ ψ

/-- Objectwise computation for `Fiber.reverse.functor`. -/
@[simp]
theorem Fiber.reverse.functor.obj
    (u : C ⥤ D) (p : S ⥤ D) (U : C) (X : p.Fiber (u.obj U)) :
    (Fiber.reverse.functor u p U).obj X =
      Fiber.reverse.obj u p X := sorry

/-- Morphismwise computation for `Fiber.reverse.functor`. -/
@[simp]
theorem Fiber.reverse.functor.map
    (u : C ⥤ D) (p : S ⥤ D) (U : C)
    {X Y : p.Fiber (u.obj U)} (φ : X ⟶ Y) :
    (Fiber.reverse.functor u p U).map φ =
      Fiber.reverse.map u p φ := sorry

end Limits.CategoricalPullback

end CategoryTheory

/- Data audit: the reverse object and both morphism components are explicit. The only deferred
axioms in `reverse.hom` and `reverse.functor` occur in the pullback compatibility equation and
functor laws; no object, map, or inverse is selected from proposition-valued evidence. -/
