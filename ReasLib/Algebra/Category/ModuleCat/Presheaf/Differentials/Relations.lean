/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free

@[expose] public section
open CategoryTheory
noncomputable section
universe u v w

namespace PresheafOfModules.DifferentialRelations
variable {C : Type u} [Category.{v} C]

/-- The presheaf of pairs of local ring sections. -/
def pairs (R : Cᵒᵖ ⥤ RingCat.{w}) : Cᵒᵖ ⥤ Type w where
  obj U := R.obj U × R.obj U
  map f := ↾fun p ↦ (R.map f p.1, R.map f p.2)
  map_id U := by ext p <;> simp
  map_comp f g := by ext p <;> simp

/-- The free module presheaf on the local sections of the coefficient ring. -/
abbrev generators (R : Cᵒᵖ ⥤ RingCat.{w}) : PresheafOfModules.{w} R :=
  freeObj (R ⋙ forget RingCat)

/-- The free module presheaf on pairs of local coefficient-ring sections. -/
abbrev pairGenerators (R : Cᵒᵖ ⥤ RingCat.{w}) : PresheafOfModules.{w} R :=
  freeObj (pairs R)

variable (R : Cᵒᵖ ⥤ RingCat.{w})

/-- The basis element in the actual free presheaf's section module. -/
def generator (U : Cᵒᵖ) (x : R.obj U) : (generators R).obj U := ModuleCat.freeMk x

@[simp] theorem restrict_generator {U V : Cᵒᵖ} (f : U ⟶ V) (x : R.obj U) :
    (generators R).restrictₛₗ f (generator R U x) = generator R V (R.map f x) :=
  ModuleCat.freeDesc_apply _ _

@[simp] theorem freeObj_map_generator (F : Cᵒᵖ ⥤ Type w) {U V : Cᵒᵖ}
    (f : U ⟶ V) (x : F.obj U) :
    (freeObj (R := R) F).map f (ModuleCat.freeMk x) = ModuleCat.freeMk (F.map f x) :=
  ModuleCat.freeDesc_apply _ _

@[simp] theorem generators_map_generator {U V : Cᵒᵖ} (f : U ⟶ V) (x : R.obj U) :
    (generators R).map f (ModuleCat.freeMk x) = ModuleCat.freeMk (R.map f x) :=
  freeObj_map_generator R (R ⋙ forget RingCat) f x

set_option backward.isDefEq.respectTransparency false in
/-- The additivity relation, assigned to each local pair before linear extension. -/
def addSeed : pairs R ⟶ (generators R).presheaf ⋙ forget _ where
  app U := ↾fun p ↦ generator R U (p.1 + p.2) - generator R U p.1 - generator R U p.2
  naturality U V f := by
    ext p
    change generator R V (R.map f p.1 + R.map f p.2) -
      generator R V (R.map f p.1) - generator R V (R.map f p.2) =
      (generators R).restrictₛₗ f (generator R U (p.1+p.2) -
        generator R U p.1 - generator R U p.2)
    simp only [map_sub, restrict_generator]
    rw [map_add]

set_option backward.isDefEq.respectTransparency false in
/-- The Leibniz relation with the exact scalar order of the source display. -/
def mulSeed : pairs R ⟶ (generators R).presheaf ⋙ forget _ where
  app U := ↾fun p ↦ generator R U (p.1 * p.2) -
    p.2 • generator R U p.1 - p.1 • generator R U p.2
  naturality U V f := by
    ext p
    change generator R V (R.map f p.1 * R.map f p.2) -
      R.map f p.2 • generator R V (R.map f p.1) -
      R.map f p.1 • generator R V (R.map f p.2) =
      (generators R).restrictₛₗ f (generator R U (p.1*p.2) -
        p.2 • generator R U p.1 - p.1 • generator R U p.2)
    simp only [map_sub, map_smulₛₗ, restrict_generator]
    rw [map_mul]

/-- The linear additivity-relation map. -/
def addMap : pairGenerators R ⟶ generators R := freeObjDesc (addSeed R)

/-- The linear Leibniz-relation map. -/
def mulMap : pairGenerators R ⟶ generators R := freeObjDesc (mulSeed R)

variable {R} {S : Cᵒᵖ ⥤ RingCat.{w}} (φ : S ⟶ R)

set_option backward.isDefEq.respectTransparency false in
/-- The relative relation sends a section of the source ring to its image generator. -/
def baseSeed : S ⋙ forget RingCat ⟶ (generators R).presheaf ⋙ forget _ where
  app U := ↾fun h ↦ ModuleCat.freeMk (φ.app U h)
  naturality U V f := by
    ext h
    change ModuleCat.freeMk (φ.app V (S.map f h)) =
      (generators R).map f (ModuleCat.freeMk (φ.app U h))
    rw [freeObj_map_generator]
    exact congrArg (ModuleCat.freeMk (R := R.obj V)) (NatTrans.naturality_apply φ f h)

/-- The linear relative-relation map. -/
def baseMap : freeObj (R := R) (S ⋙ forget RingCat) ⟶ generators R :=
  freeObjDesc (baseSeed φ)

@[simp] theorem addMap_generator (U : Cᵒᵖ) (a b : R.obj U) :
    (addMap R).app U (ModuleCat.freeMk (a,b)) =
      ModuleCat.freeMk (a+b) - ModuleCat.freeMk a - ModuleCat.freeMk b := by
  exact ModuleCat.freeDesc_apply _ _

@[simp] theorem mulMap_generator (U : Cᵒᵖ) (f g : R.obj U) :
    (mulMap R).app U (ModuleCat.freeMk (f,g)) =
      ModuleCat.freeMk (f*g) - g • ModuleCat.freeMk f - f • ModuleCat.freeMk g := by
  exact ModuleCat.freeDesc_apply _ _

@[simp] theorem baseMap_generator (U : Cᵒᵖ) (h : S.obj U) :
    (baseMap φ).app U (ModuleCat.freeMk h) = ModuleCat.freeMk (φ.app U h) := by
  exact ModuleCat.freeDesc_apply _ _

end PresheafOfModules.DifferentialRelations
