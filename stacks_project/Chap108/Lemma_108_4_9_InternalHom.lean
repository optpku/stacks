/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_LocalHomCarrier
public import Mathlib.Algebra.Module.Shrink
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-! A small-universe realization of the canonical slice-morphism internal Hom.
Only algebraic/naturality/sheaf laws are deferred; the size certificate is proved. -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

abbrev Raw (F G : commModules X) (U : (smallEtaleSite X)ᵒᵖ) :=
  F.over U.unop ⟶ G.over U.unop

instance rawSmall (F G : commModules X) (U : (smallEtaleSite X)ᵒᵖ) : Small.{u} (Raw F G U) :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site.spaceLocalHomSmall X (commRingSheaf X) F G U.unop

instance rawModule (F G : commModules X) (U : (smallEtaleSite X)ᵒᵖ) :
    Module ((commStructureSheaf X).obj.obj U) (Raw F G U) :=
  Module.compHom _ (SheafOfModules.sectionAction (commStructureSheaf X) G U.unop)

abbrev Carrier (F G : commModules X) (U : (smallEtaleSite X)ᵒᵖ) := Shrink.{u} (Raw F G U)

def decode (F G : commModules X) (U : (smallEtaleSite X)ᵒᵖ) :
    Carrier F G U ≃ₗ[(commStructureSheaf X).obj.obj U] Raw F G U :=
  Shrink.linearEquiv _ _

def restrictRaw (F G : commModules X) {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V)
    (f : Raw F G U) : Raw F G V :=
  (SheafOfModules.overFunctorMap (commRingSheaf X) i.unop).inv.app F ≫
    (SheafOfModules.overMap (commRingSheaf X) i.unop).map f ≫
      (SheafOfModules.overFunctorMap (commRingSheaf X) i.unop).hom.app G

def sectionModule (F G : commModules X) (U : (smallEtaleSite X)ᵒᵖ) :
    ModuleCat.{u} ((commStructureSheaf X).obj.obj U) := ModuleCat.of _ (Carrier F G U)

def restrict (F G : commModules X) {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    sectionModule F G U ⟶
      (ModuleCat.restrictScalars ((commStructureSheaf X).obj.map i).hom).obj (sectionModule F G V) :=
  ModuleCat.ofHom
    (X := sectionModule F G U)
    (Y := (ModuleCat.restrictScalars ((commStructureSheaf X).obj.map i).hom).obj (sectionModule F G V)) {
    toFun := fun f ↦ (decode F G V).symm (restrictRaw F G i (decode F G U f))
    map_add' := by sorry
    map_smul' := by sorry }

def presheaf (F G : commModules X) : PresheafOfModules.{u} (commRingSheaf X).obj where
  obj := sectionModule F G
  map := restrict F G
  map_id := by sorry
  map_comp := by sorry

def obj (F G : commModules X) : commModules X where
  val := presheaf F G
  isSheaf := by sorry

def post (F : commModules X) {G H : commModules X} (f : G ⟶ H) (U : (smallEtaleSite X)ᵒᵖ) :
    sectionModule F G U ⟶ sectionModule F H U :=
  ModuleCat.ofHom {
    toFun := fun a ↦ (decode F H U).symm (decode F G U a ≫ f.over U.unop)
    map_add' := by sorry
    map_smul' := by sorry }

def map (F : commModules X) {G H : commModules X} (f : G ⟶ H) : obj F G ⟶ obj F H where
  val := { app := post F f, naturality := by sorry }

def functor (F : commModules X) : commModules X ⥤ commModules X where
  obj := obj F
  map := map F
  map_id := by sorry
  map_comp := by sorry

/-- Decoding restriction yields the genuine slice restriction, not a zero map. -/
theorem restrict_decode (F G : commModules X) {U V : (smallEtaleSite X)ᵒᵖ}
    (i : U ⟶ V) (a : Carrier F G U) :
    decode F G V ((restrict F G i).hom a) = restrictRaw F G i (decode F G U a) :=
  (decode F G V).apply_symm_apply _

/-- Decoding postcomposition yields the actual composite of local morphisms. -/
theorem post_decode (F : commModules X) {G H : commModules X} (f : G ⟶ H)
    (U : (smallEtaleSite X)ᵒᵖ) (a : Carrier F G U) :
    decode F H U ((post F f U).hom a) = decode F G U a ≫ f.over U.unop :=
  (decode F H U).apply_symm_apply _

private theorem transport_identity {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ D) (A : C) {B : D} (e : T.obj A ≅ B) :
    e.inv ≫ T.map (𝟙 A) ≫ e.hom = 𝟙 B := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp, e.inv_hom_id]

/-- Actual local identities survive restriction along every site arrow. -/
theorem restrict_identity (F : commModules X) {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    (restrict F F i).hom ((decode F F U).symm (𝟙 _)) = (decode F F V).symm (𝟙 _) := by
  apply (decode F F V).injective
  rw [restrict_decode, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact transport_identity (SheafOfModules.overMap (commRingSheaf X) i.unop) (F.over U.unop)
    ((SheafOfModules.overFunctorMap (commRingSheaf X) i.unop).app F)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.InternalHom
