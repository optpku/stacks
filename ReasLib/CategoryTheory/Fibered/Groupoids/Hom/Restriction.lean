/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Fiber.Restriction
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber

/-!
# Restriction compatibility of groupoid-fibred morphisms

The fibre functor induced by a morphism of categories fibred in groupoids commutes
with chosen restriction through the canonical comparison of cartesian lifts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

noncomputable section

universe u v w vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids

open Functor Functor.Fiber

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

/-- Applying the total functor of a 1-morphism to a chosen cartesian lift remains cartesian. -/
theorem map_restrict_isCartesian (F : X ⟶ Y) {U Z : C} (x : X.p.Fiber U) (f : Z ⟶ U) :
    Y.p.IsCartesian f ((toFunctor F).map (IsPreFibered.pullbackMap x.property f)) := sorry

/-- The fibre functor of a 1-morphism commutes with restriction, by uniqueness of cartesian
lifts. -/
def fiberFunctor_restrictObj (F : X ⟶ Y) {U Z : C} (x : X.p.Fiber U) (f : Z ⟶ U) :
    (fiberFunctor F Z).obj (restrictObj x f) ≅
      restrictObj ((fiberFunctor F U).obj x) f :=
  let φ := IsPreFibered.pullbackMap ((fiberFunctor F U).obj x).property f
  let φ' := (toFunctor F).map (IsPreFibered.pullbackMap x.property f)
  let hφ := IsPreFibered.pullbackMap.IsCartesian ((fiberFunctor F U).obj x).property f
  let hφ' := map_restrict_isCartesian F x f
  let e := @IsCartesian.domainUniqueUpToIso _ _ _ _ Y.p _ _ _ _ f φ hφ _ φ' hφ'
  Functor.Fiber.isoMk e
    (@IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ Y.p _ _ _ _ f φ hφ _ φ' hφ')

end CategoryTheory.FiberedCategoryOver.Groupoids
