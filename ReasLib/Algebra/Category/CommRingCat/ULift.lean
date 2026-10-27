/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Universe lifts of bundled commutative rings

This module packages universe lifting as a functor on bundled commutative rings.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace CommRingCat

/-- The universe lift of a morphism of bundled commutative rings. -/
def liftedMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    CommRingCat.of (ULift.{w, u} R) ⟶ CommRingCat.of (ULift.{w, u} S) :=
  CommRingCat.ofHom f.hom.ulift

/-- Universe lifting carries identity ring morphisms to identity morphisms. -/
theorem liftedMap_id (R : CommRingCat.{u}) :
    liftedMap.{u, w} (𝟙 R) = 𝟙 (CommRingCat.of (ULift.{w, u} R)) := sorry

/-- Universe lifting carries composites of ring morphisms to composites. -/
theorem liftedMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    liftedMap.{u, w} (f ≫ g) = liftedMap.{u, w} f ≫ liftedMap.{u, w} g := sorry

/-- Universe lifting as a functor on bundled commutative rings. -/
def universeLift : CommRingCat.{u} ⥤ CommRingCat.{max u w} where
  obj R := CommRingCat.of (ULift.{w, u} R)
  map f := liftedMap.{u, w} f
  map_id R := liftedMap_id.{u, w} R
  map_comp f g := liftedMap_comp.{u, w} f g

/-- The object action of `universeLift` is the ordinary `ULift` of the
underlying commutative ring. -/
theorem universeLift_obj (R : CommRingCat.{u}) :
    (universeLift.{u, w}).obj R = CommRingCat.of (ULift.{w, u} R) := sorry

/-- The morphism action of `universeLift` is induced by `RingHom.ulift`. -/
theorem universeLift_map {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (universeLift.{u, w}).map f = CommRingCat.ofHom f.hom.ulift := sorry

/-- Universe lifting of commutative rings commutes with forgetting to abelian
groups, by the identity on underlying `ULift` additive groups. -/
def universeLiftForgetAddIso :
    CommRingCat.universeLift.{u, w} ⋙
        forget₂ CommRingCat.{max u w} RingCat.{max u w} ⋙
          forget₂ RingCat.{max u w} AddCommGrpCat.{max u w} ≅
      forget₂ CommRingCat.{u} RingCat.{u} ⋙
        forget₂ RingCat.{u} AddCommGrpCat.{u} ⋙
          AddCommGrpCat.uliftFunctor.{w, u} where
  hom := { app := fun R => 𝟙 _, naturality := sorry }
  inv := { app := fun R => 𝟙 _, naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

end CommRingCat
