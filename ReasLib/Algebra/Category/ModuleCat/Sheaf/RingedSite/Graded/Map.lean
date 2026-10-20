/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Total

/-!
# Total maps of graded algebra sheaves

This file promotes a morphism of naturally graded commutative algebra sheaves to a morphism
of their total algebra sheaves.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedAlgebraSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})
variable {A B : GradedAlgebraSheaf O ℕ} [A.IsCommutative] [B.IsCommutative]

/-- The underlying module map on total objects induced by a morphism of naturally graded
algebra sheaves. -/
noncomputable def totalMapLinear (f : Hom A B) :
    (CategoryTheory.GradedObject.Total.functor
        (I := ℕ) (C := ringedSiteModuleCategory J O)).obj A.toGradedObject ⟶
      (CategoryTheory.GradedObject.Total.functor
        (I := ℕ) (C := ringedSiteModuleCategory J O)).obj B.toGradedObject :=
  (CategoryTheory.GradedObject.Total.functor
    (I := ℕ) (C := ringedSiteModuleCategory J O)).map f.hom

/-- The sectionwise function underlying the total map, with its algebra carriers made
explicit. -/
noncomputable def totalMapFunction (f : Hom A B) (U : Cᵒᵖ) :
    (totalAlgebra O A).right.obj.obj U → (totalAlgebra O B).right.obj.obj U :=
  fun x ↦ ((totalMapLinear O f).val.app U).hom x

/-- The total map sends zero to zero on every object of the site. -/
theorem totalMapLinear_map_zero (f : Hom A B)
    (U : Cᵒᵖ) :
    totalMapFunction O f U 0 = 0 := sorry

/-- The total map sends the total-algebra unit to the total-algebra unit. -/
theorem totalMapLinear_map_one (f : Hom A B)
    (U : Cᵒᵖ) :
    totalMapFunction O f U 1 =
      (1 : (totalAlgebra O B).right.obj.obj U) := sorry

/-- The total map preserves addition on every object of the site. -/
theorem totalMapLinear_map_add (f : Hom A B)
    (U : Cᵒᵖ) (x y : (totalAlgebra O A).right.obj.obj U) :
    totalMapFunction O f U (x + y) =
      totalMapFunction O f U x + totalMapFunction O f U y := sorry

/-- The total map preserves multiplication on every object of the site. -/
theorem totalMapLinear_map_mul (f : Hom A B)
    (U : Cᵒᵖ) (x y : (totalAlgebra O A).right.obj.obj U) :
    totalMapFunction O f U (x * y) =
      totalMapFunction O f U x * totalMapFunction O f U y := sorry

/-- The ring homomorphism on total sections induced by a graded-algebra morphism. -/
noncomputable def totalMapRingHom (f : Hom A B) (U : Cᵒᵖ) :
    ((totalAlgebra O A).right.obj.obj U : Type (max u v)) →+*
      ((totalAlgebra O B).right.obj.obj U : Type (max u v)) :=
    { toFun := totalMapFunction O f U
      map_zero' := totalMapLinear_map_zero O f U
      map_one' := totalMapLinear_map_one O f U
      map_add' := totalMapLinear_map_add O f U
      map_mul' := totalMapLinear_map_mul O f U }

/-- Evaluation of `totalMapRingHom` is the underlying total module map. -/
theorem totalMapRingHom_apply (f : Hom A B) (U : Cᵒᵖ)
    (x : (totalAlgebra O A).right.obj.obj U) :
    totalMapRingHom O f U x = totalMapFunction O f U x := sorry

/-- The ring maps on total sections induced by a graded-algebra morphism. -/
noncomputable def totalMapApp (f : Hom A B)
    (U : Cᵒᵖ) :
    (totalAlgebra O A).right.obj.obj U ⟶ (totalAlgebra O B).right.obj.obj U :=
  ConcreteCategory.ofHom (C := CommRingCat) (totalMapRingHom O f U)

/-- Evaluation of `totalMapApp` is the underlying total module map. -/
theorem totalMapApp_apply (f : Hom A B)
    (U : Cᵒᵖ) (x : (totalAlgebra O A).right.obj.obj U) :
    totalMapApp O f U x = totalMapFunction O f U x := sorry

/-- The sectionwise total-algebra maps commute with restriction. -/
theorem totalMapApp_naturality (f : Hom A B)
    {U V : Cᵒᵖ} (g : U ⟶ V) :
    (totalAlgebra O A).right.obj.map g ≫ totalMapApp O f V =
      totalMapApp O f U ≫ (totalAlgebra O B).right.obj.map g := sorry

/-- A graded-algebra morphism induces a morphism between the corresponding total algebra
sheaves. -/
noncomputable def totalMapSheaf (f : Hom A B) :
    (totalAlgebra O A).right ⟶ (totalAlgebra O B).right :=
  ObjectProperty.homMk
    { app := totalMapApp O f
      naturality := fun _ _ g ↦ totalMapApp_naturality O f g }

/-- The total-algebra sheaf map commutes with the structure maps from `O`. -/
theorem totalMapSheaf_structure (f : Hom A B) :
    (totalAlgebra O A).hom ≫ totalMapSheaf O f = (totalAlgebra O B).hom := sorry

/-- Functoriality of totalization on naturally graded algebra sheaves, as a morphism of
algebras under `O`. -/
noncomputable def totalMap (f : Hom A B) :
    totalAlgebra O A ⟶ totalAlgebra O B :=
  Under.homMk (totalMapSheaf O f) (totalMapSheaf_structure O f)

/-- The underlying sheaf morphism of `totalMap` is `totalMapSheaf`. -/
theorem totalMap_right (f : Hom A B) :
    (totalMap O f).right = totalMapSheaf O f := sorry

end SheafOfModules.RingedSite.GradedAlgebraSheaf
