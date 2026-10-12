/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber actions of based functors and transformations

This module records the canonical action of based functors and based natural transformations on
standard fibers, including the hom-category-level fiber functor.
-/

@[expose] public section

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open BasedNatTrans
open Functor.IsHomLift
open scoped Bicategory

universe u v uS uX uY vS vX vY

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- Regard a total source object as an object of the fiber over the base of its image under a
based functor. -/
def sourceFiberObj (F : X ⥤ᵇ Y) (x : X.obj) :
    X.p.Fiber (Y.p.obj (F.toFunctor.obj x)) :=
  Functor.Fiber.mk (congrFun (congrArg Functor.obj F.w) x).symm

/-- On the source fiber over `U`, a based functor followed by the target projection is the
constant functor at `U`. This equation is the input to `Functor.Fiber.inducedFunctor`. -/
theorem fiberFunctor.comp_eq_const
    (F : X ⥤ᵇ Y) (U : C) :
    (Functor.Fiber.fiberInclusion : Functor.Fiber X.p U ⥤ X.obj) ⋙ F.toFunctor ⋙ Y.p =
      (Functor.const (Functor.Fiber X.p U)).obj U := sorry
/- Proof strategy: whisker the strict equation `F.w` on the left by the source fiber inclusion,
then compose it with `Functor.Fiber.fiberInclusion_comp_eq_const`. This isolates the only
transport needed by `Functor.Fiber.inducedFunctor`. -/

/-- The canonical functor on the fibre over `U` induced by a morphism in `Cat/C`.

This is deliberately a `def`, not an `abbrev`: it is the reusable data owner for the induced
fiber map, while `fiberFunctor.comp_eq_const` exposes the proof input used by the canonical
mathlib constructor. No public theorem should rely on unfolding the chosen construction. -/
def fiberFunctor (F : X ⥤ᵇ Y) (U : C) : Functor.Fiber X.p U ⥤ Functor.Fiber Y.p U :=
  let G : Functor.Fiber X.p U ⥤ Y.obj :=
    (Functor.Fiber.fiberInclusion : Functor.Fiber X.p U ⥤ X.obj) ⋙ F.toFunctor
  let hG : G ⋙ Y.p = (Functor.const (Functor.Fiber X.p U)).obj U :=
    fiberFunctor.comp_eq_const F U
  Functor.Fiber.inducedFunctor hG

/-- The underlying total-category object of the image under an induced fiber functor is the
image under the underlying based functor. -/
@[simp]
theorem fiberFunctor.obj.val (F : X ⥤ᵇ Y) (U : C) (x : X.p.Fiber U) :
    ((F.fiberFunctor U).obj x).1 = F.toFunctor.obj x.1 := sorry

/-- Applying the induced fiber functor to `sourceFiberObj F x` gives the canonical target fiber
object carried by `F.obj x`. -/
theorem fiberFunctor.obj.sourceFiberObj (F : X ⥤ᵇ Y) (x : X.obj) :
    (F.fiberFunctor (Y.p.obj (F.toFunctor.obj x))).obj (F.sourceFiberObj x) =
      Functor.Fiber.mk (p := Y.p) (a := F.toFunctor.obj x) rfl := sorry

/-- The underlying total-category morphism of the image under an induced fiber functor is the
image under the underlying based functor. -/
@[simp]
theorem fiberFunctor.map.val (F : X ⥤ᵇ Y) (U : C)
    {x y : X.p.Fiber U} (φ : x ⟶ y) :
    ((F.fiberFunctor U).map φ).1 = F.toFunctor.map φ.1 := sorry

/-- Restriction of the identity based functor to a standard fiber is the identity functor. -/
@[simp]
theorem fiberFunctor.id (X : BasedCategory.{vX, uX} C) (U : C) :
    ((𝟙 X : X ⥤ᵇ X).fiberFunctor U) = 𝟭 (X.p.Fiber U) := sorry

/-- Restriction of a composite of based functors to a standard fiber is the composite of their
fiber restrictions. -/
@[simp]
theorem fiberFunctor.comp
    {Z : BasedCategory.{vS, uS} C} (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) (U : C) :
    ((F ⋙ G).fiberFunctor U) = F.fiberFunctor U ⋙ G.fiberFunctor U := sorry

end BasedFunctor

namespace BasedNatTrans

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {F G H : X ⥤ᵇ Y}

/-- The component in the standard fiber over `U` of a based natural transformation. Its
underlying arrow is the original component; verticality supplies exactly the fiber-morphism
condition. -/
def fiberApp (η : F ⟶ G) (U : C) (x : X.p.Fiber U) :
    (F.fiberFunctor U).obj x ⟶ (G.fiberFunctor U).obj x :=
  ⟨η.toNatTrans.app x.1, η.isHomLift x.2⟩

/-- Naturality of the fiber components of a based natural transformation. -/
theorem fiberApp.naturality (η : F ⟶ G) (U : C) {x y : X.p.Fiber U} (φ : x ⟶ y) :
    (F.fiberFunctor U).map φ ≫ fiberApp η U y =
      fiberApp η U x ≫ (G.fiberFunctor U).map φ := sorry
-- Proof strategy: unfold fiberApp and use the naturality square of η in the total category.

/-- A based natural transformation restricts canonically to every standard fiber. -/
def fiber (η : F ⟶ G) (U : C) : F.fiberFunctor U ⟶ G.fiberFunctor U where
  app := fiberApp η U
  naturality := fun {_ _} φ ↦
    fiberApp.naturality (F := F) (G := G) η U φ

/-- Evaluation of the restricted natural transformation is the canonical bundled fiber
component. -/
@[simp]
theorem fiber.app (η : F ⟶ G) (U : C) (x : X.p.Fiber U) :
    (fiber η U).app x = fiberApp η U x := sorry

/-- Forgetting a restricted natural-transformation component to the total category recovers the
original component. -/
@[simp]
theorem fiber.app.val (η : F ⟶ G) (U : C) (x : X.p.Fiber U) :
    ((fiber η U).app x).1 = η.toNatTrans.app x.1 := sorry

/-- Naturality of a based natural transformation after restriction to a standard fiber. -/
@[reassoc]
theorem fiber.naturality (η : F ⟶ G) (U : C)
    {x y : X.p.Fiber U} (φ : x ⟶ y) :
    (F.fiberFunctor U).map φ ≫ (fiber η U).app y =
      (fiber η U).app x ≫ (G.fiberFunctor U).map φ := sorry

/-- A restricted based natural-transformation component transports by conjugation along an
isomorphism in the source fiber. -/
theorem fiber.app.transport (η : F ⟶ G) (U : C)
    {x y : X.p.Fiber U} (e : x ≅ y) :
    (fiber η U).app y =
      (F.fiberFunctor U).map e.inv ≫
        (fiber η U).app x ≫
        (G.fiberFunctor U).map e.hom := sorry

/-- Restriction to a fiber preserves identity based natural transformations. -/
theorem fiber.id (F : X ⥤ᵇ Y) (U : C) :
    fiber (𝟙 F) U = 𝟙 (F.fiberFunctor U) := sorry
-- Proof strategy: extensionality on components reduces the claim to identity components.

/-- Restriction to a fiber preserves vertical composition of based natural transformations. -/
theorem fiber.comp (η : F ⟶ G) (θ : G ⟶ H) (U : C) :
    fiber (η ≫ θ) U = fiber η U ≫ fiber θ U := sorry
-- Proof strategy: extensionality on components reduces the claim to componentwise composition.

end BasedNatTrans

namespace BasedCategory

/-- Evaluation on the standard fiber over `U`, functorial simultaneously in based functors and
based natural transformations. This is the hom-category-level owner behind fiberwise maps of
isomorphisms. -/
def fiberFunctor
    (X : BasedCategory.{vX, uX} C) (Y : BasedCategory.{vY, uY} C) (U : C) :
    (X ⥤ᵇ Y) ⥤ (X.p.Fiber U ⥤ Y.p.Fiber U) where
  obj F := F.fiberFunctor U
  map η := BasedNatTrans.fiber η U
  map_id F := BasedNatTrans.fiber.id F U
  map_comp η θ := BasedNatTrans.fiber.comp η θ U

end BasedCategory

end CategoryTheory
