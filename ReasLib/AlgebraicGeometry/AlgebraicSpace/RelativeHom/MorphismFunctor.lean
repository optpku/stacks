/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver

/-!
# Relative morphisms on schemes over `B`

The functor `Mor_B(Z, X)` on `(Sch/B)^op`, sending a scheme `T` over `B` to
the type of morphisms `Z_T ⟶ X_T` over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Z B X : AlgebraicSpace S}

/-- The comparison `T' ×_B Z ⟶ T ×_B Z` induced by a morphism of schemes over `B`. -/
def baseChangeMap (z : Z ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    pullback τ.hom z ⟶ pullback σ.hom z :=
  pullback.map τ.hom z σ.hom z ((ofOverFunctor S).map h.left) (𝟙 Z) (𝟙 B)
    ((Category.comp_id τ.hom).trans (CostructuredArrow.w h).symm)
    ((Category.comp_id z).trans (Category.id_comp z).symm)

/-- `baseChangeMap` commutes with the projections to the varying test object. -/
theorem baseChangeMap_fst (z : Z ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    baseChangeMap z h ≫ pullback.fst σ.hom z =
      pullback.fst τ.hom z ≫ (ofOverFunctor S).map h.left := by
  exact pullback.lift_fst _ _ _

/-- `baseChangeMap` commutes with the projections to `Z`. -/
theorem baseChangeMap_snd (z : Z ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ) :
    baseChangeMap z h ≫ pullback.snd σ.hom z = pullback.snd τ.hom z := by
  simp only [baseChangeMap, pullback.lift_snd, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a morphism `Z_T ⟶ X_T` over `T` along `T' ⟶ T` over `B`. -/
def restrict (z : Z ⟶ B) (x : X ⟶ B) {σ τ : SchemeOver B} (h : τ ⟶ σ)
    (b : BaseChangeMorphism z x σ.hom) : BaseChangeMorphism z x τ.hom :=
  BaseChangeMorphism.ofMap (baseChangeMap z h ≫ BaseChangeMorphism.toMap b) (by
    rw [Category.assoc, BaseChangeMorphism.toMap_comm, ← Category.assoc,
      baseChangeMap_fst, Category.assoc, CostructuredArrow.w h])

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along the identity morphism of a scheme over `B` is the identity. -/
theorem mor_map_id (z : Z ⟶ B) (x : X ⟶ B) (σ : (SchemeOver B)ᵒᵖ) :
    TypeCat.ofHom (restrict z x (𝟙 σ).unop) =
      𝟙 (BaseChangeMorphism z x σ.unop.hom) := by
  have hid : baseChangeMap z (𝟙 σ.unop) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [baseChangeMap_fst, CostructuredArrow.id_left,
        (ofOverFunctor S).map_id, Category.comp_id, Category.id_comp]
    · simp only [baseChangeMap_snd, Category.id_comp]
  apply ConcreteCategory.hom_ext
  intro b
  change restrict z x (𝟙 σ.unop) b = b
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (BaseChangeMorphism.over_fst _).trans (BaseChangeMorphism.over_fst b).symm
  · change BaseChangeMorphism.toMap (restrict z x (𝟙 σ.unop) b) =
      BaseChangeMorphism.toMap b
    simp only [restrict, BaseChangeMorphism.toMap_ofMap, hid, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along a composite morphism of schemes over `B` is the composite
restriction. -/
theorem mor_map_comp (z : Z ⟶ B) (x : X ⟶ B) {σ τ ρ : (SchemeOver B)ᵒᵖ}
    (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    TypeCat.ofHom (restrict z x (h ≫ k).unop) =
      TypeCat.ofHom (restrict z x h.unop) ≫ TypeCat.ofHom (restrict z x k.unop) := by
  have hcomp : baseChangeMap z (h ≫ k).unop =
      baseChangeMap z k.unop ≫ baseChangeMap z h.unop := by
    apply pullback.hom_ext
    · rw [baseChangeMap_fst, Category.assoc, baseChangeMap_fst,
        ← Category.assoc, baseChangeMap_fst, Category.assoc, ← Functor.map_comp]
      rfl
    · rw [baseChangeMap_snd, Category.assoc, baseChangeMap_snd, baseChangeMap_snd]
  apply ConcreteCategory.hom_ext
  intro b
  change restrict z x (h ≫ k).unop b =
    restrict z x k.unop (restrict z x h.unop b)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (BaseChangeMorphism.over_fst _).trans (BaseChangeMorphism.over_fst _).symm
  · change BaseChangeMorphism.toMap (restrict z x (h ≫ k).unop b) =
      BaseChangeMorphism.toMap (restrict z x k.unop (restrict z x h.unop b))
    simp only [restrict, BaseChangeMorphism.toMap_ofMap]
    rw [hcomp, Category.assoc]

/-- The relative-Hom functor `Mor_B(Z, X)` on schemes over `B`. -/
def mor (z : Z ⟶ B) (x : X ⟶ B) : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := BaseChangeMorphism z x σ.unop.hom
  map h := TypeCat.ofHom (restrict z x h.unop)
  map_id := mor_map_id z x
  map_comp := mor_map_comp z x

/-- Evaluating `Mor_B(Z, X)` at a scheme over `B` recovers morphisms `Z_T ⟶ X_T`
over `T`. -/
theorem mor_obj (z : Z ⟶ B) (x : X ⟶ B) (σ : SchemeOver B) :
    (mor z x).obj (op σ) = BaseChangeMorphism z x σ.hom := rfl

/-- The relative-Hom functor acts on a morphism of schemes over `B` by restriction. -/
theorem mor_map (z : Z ⟶ B) (x : X ⟶ B) {σ τ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (mor z x).map h = TypeCat.ofHom (restrict z x h.unop) := rfl

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
