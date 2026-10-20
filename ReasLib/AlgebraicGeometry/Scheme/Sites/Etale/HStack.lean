/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPseudofunctor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

@[expose] public section

open CategoryTheory
open CategoryTheory.Pseudofunctor
open scoped CategoryTheory.Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.EtaleSheaf

variable (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)

/-- The small étale sheaf pseudofunctor restricted to schemes over a represented base. -/
def overPseudofunctor : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat :=
  (ChosenBigSite.sliceToScheme Schh S).op.toPseudofunctor.comp pseudofunctor

/-- The value over a slice object is its category of Type-valued small étale sheaves. -/
theorem overPseudofunctor_obj (U : Over S) :
    (overPseudofunctor Schh S).obj (.mk (.op U)) =
      Cat.of
        (Sheaf ((ChosenBigSite.sliceToScheme Schh S).obj U).smallEtaleTopology
          (Type (u + 1))) := rfl

/-- Reindexing along a slice morphism is pullback of small étale sheaves. -/
theorem overPseudofunctor_map {U V : Over S} (f : U ⟶ V) :
    ((overPseudofunctor Schh S).map f.op.toLoc).toFunctor =
      pullback ((ChosenBigSite.sliceToScheme Schh S).map f) := rfl

/-- The selected fibre of the sheaf projection is the small étale sheaf category. -/
theorem overFiber_eq (U : Over S) :
    HasFibers.Fib (CoGrothendieck.forget (overPseudofunctor Schh S)) U =
      (overPseudofunctor Schh S).obj ⟨.op U⟩ := rfl

/-- Small étale sheaf categories satisfy descent for the slice h topology. -/
instance overPseudofunctor_isStack :
    Pseudofunctor.IsStack (overPseudofunctor Schh S)
      (ChosenBigHSite.bigTopology Schh S) := sorry

/-- Pullback along an identity induces the identity functor on the sheaf core. -/
def overCoreMapId (U : (Over S)ᵒᵖ) :
    (pullback ((ChosenBigSite.sliceToScheme Schh S).map (𝟙 U.unop))).core.toCatHom ≅
      𝟙 (Cat.of (Core
        (Sheaf ((ChosenBigSite.sliceToScheme Schh S).obj U.unop).smallEtaleTopology
          (Type (u + 1))))) :=
  Cat.Hom.isoMk
    ((eqToIso (congrArg pullback ((ChosenBigSite.sliceToScheme Schh S).map_id U.unop)) ≪≫
        pullbackId ((ChosenBigSite.sliceToScheme Schh S).obj U.unop)).core ≪≫
      Functor.coreId _)

/-- Pullback along a composite induces successive pullback on the sheaf cores. -/
def overCoreMapComp {U V W : (Over S)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    (pullback ((ChosenBigSite.sliceToScheme Schh S).map (f ≫ g).unop)).core.toCatHom ≅
      (pullback ((ChosenBigSite.sliceToScheme Schh S).map f.unop)).core.toCatHom ≫
        (pullback ((ChosenBigSite.sliceToScheme Schh S).map g.unop)).core.toCatHom :=
  Cat.Hom.isoMk
    ((eqToIso (congrArg pullback
          ((ChosenBigSite.sliceToScheme Schh S).map_comp g.unop f.unop)) ≪≫
        (pullbackComp ((ChosenBigSite.sliceToScheme Schh S).map f.unop)
          ((ChosenBigSite.sliceToScheme Schh S).map g.unop)).symm).core ≪≫
      Functor.coreComp _ _)

/-- The pullback comparisons on sheaf cores satisfy associativity coherence. -/
theorem overCore_associator {U V W Z : (Over S)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ Z) :
    (overCoreMapComp Schh S (f ≫ g) h).hom ≫
        (overCoreMapComp Schh S f g).hom ▷
          (pullback ((ChosenBigSite.sliceToScheme Schh S).map h.unop)).core.toCatHom ≫
      (α_ (pullback ((ChosenBigSite.sliceToScheme Schh S).map f.unop)).core.toCatHom
        (pullback ((ChosenBigSite.sliceToScheme Schh S).map g.unop)).core.toCatHom
        (pullback ((ChosenBigSite.sliceToScheme Schh S).map h.unop)).core.toCatHom).hom ≫
      (pullback ((ChosenBigSite.sliceToScheme Schh S).map f.unop)).core.toCatHom ◁
        (overCoreMapComp Schh S g h).inv ≫
      (overCoreMapComp Schh S f (g ≫ h)).inv = eqToHom (by simp) := sorry

/-- The identity comparison on sheaf cores satisfies left-unit coherence. -/
theorem overCore_left_unitor {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (overCoreMapComp Schh S (𝟙 U) f).hom ≫
        (overCoreMapId Schh S U).hom ▷
          (pullback ((ChosenBigSite.sliceToScheme Schh S).map f.unop)).core.toCatHom ≫
      (λ_ (pullback ((ChosenBigSite.sliceToScheme Schh S).map f.unop)).core.toCatHom).hom =
        eqToHom (by simp) := sorry

/-- The identity comparison on sheaf cores satisfies right-unit coherence. -/
theorem overCore_right_unitor {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (overCoreMapComp Schh S f (𝟙 V)).hom ≫
        (pullback ((ChosenBigSite.sliceToScheme Schh S).map f.unop)).core.toCatHom ◁
          (overCoreMapId Schh S V).hom ≫
      (ρ_ (pullback ((ChosenBigSite.sliceToScheme Schh S).map f.unop)).core.toCatHom).hom =
        eqToHom (by simp) := sorry

/-- The pseudofunctor of small étale sheaves and their isomorphisms over a represented base. -/
def overCorePseudofunctor : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat where
  obj U := Cat.of (Core
    (Sheaf ((ChosenBigSite.sliceToScheme Schh S).obj U.as.unop).smallEtaleTopology
      (Type (u + 1))))
  map f := (pullback ((ChosenBigSite.sliceToScheme Schh S).map f.as.unop)).core.toCatHom
  map₂ η := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete η
    rfl)
  map₂_id f := by simp
  map₂_comp η θ := by
    obtain rfl := obj_ext_of_isDiscrete η
    obtain rfl := obj_ext_of_isDiscrete θ
    simp
  mapId U := overCoreMapId Schh S U.as
  mapComp f g := overCoreMapComp Schh S f.as g.as
  map₂_whisker_left f g h η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  map₂_whisker_right η h := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  map₂_associator f g h := (overCore_associator Schh S f.as g.as h.as).symm
  map₂_left_unitor f := (overCore_left_unitor Schh S f.as).symm
  map₂_right_unitor f := (overCore_right_unitor Schh S f.as).symm

/-- The value of the sheaf-core pseudofunctor is the core of the small étale sheaf category. -/
theorem overCorePseudofunctor_obj (U : Over S) :
    (overCorePseudofunctor Schh S).obj (.mk (.op U)) =
      Cat.of
        (Core (Sheaf ((ChosenBigSite.sliceToScheme Schh S).obj U).smallEtaleTopology
          (Type (u + 1)))) := rfl

/-- Reindexing sheaves and their isomorphisms is the core of small étale pullback. -/
theorem overCorePseudofunctor_map {U V : Over S} (f : U ⟶ V) :
    ((overCorePseudofunctor Schh S).map f.op.toLoc).toFunctor =
      (pullback ((ChosenBigSite.sliceToScheme Schh S).map f)).core := rfl

/-- Each category of small étale sheaves and their isomorphisms is a groupoid. -/
instance overCorePseudofunctor_isGroupoid (U : LocallyDiscrete (Over S)ᵒᵖ) :
    IsGroupoid ((overCorePseudofunctor Schh S).obj U) where
  all_isIso f := ⟨⟨CoreHom.mk f.iso.symm,
    CoreHom.ext (Iso.self_symm_id f.iso),
    CoreHom.ext (Iso.symm_self_id f.iso)⟩⟩

/-- The selected fibre of the sheaf-core projection is the core of the sheaf category. -/
theorem overCoreFiber_eq (U : Over S) :
    HasFibers.Fib (CoGrothendieck.forget (overCorePseudofunctor Schh S)) U =
      Core (Sheaf ((ChosenBigSite.sliceToScheme Schh S).obj U).smallEtaleTopology
        (Type (u + 1))) := rfl

/-- Small étale sheaves and their isomorphisms form a stack in groupoids for the h topology. -/
instance overCoreForget_isStack :
    CategoryTheory.IsStack.InGroupoids (ChosenBigHSite.bigTopology Schh S)
      (CoGrothendieck.forget (overCorePseudofunctor Schh S)) := sorry

end AlgebraicGeometry.Scheme.EtaleSheaf
