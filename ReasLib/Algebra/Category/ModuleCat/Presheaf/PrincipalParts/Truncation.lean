/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.Truncation

import all ReasLib.Algebra.Module.PrincipalParts.Basic
import all ReasLib.Algebra.Module.PrincipalParts.RingHom

/-!
# Truncation of principal-parts presheaves

The algebraic transition `PrincipalParts.RingHom.truncate σ M h` for `h : k ≤ l` is compatible
with restriction maps and with morphisms of module presheaves. It therefore defines both a
morphism of principal-parts presheaves and a natural transformation between the corresponding
endofunctors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace PresheafOfModules.PrincipalParts

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : O₁ ⟶ O₂)
variable (F : PresheafOfModules (ringPresheaf O₂))

private theorem truncate_hom_ext_universalClass (k : ℕ) (X : Cᵒᵖ)
    {N : ModuleCat (O₂.obj X)} {f g : module φ F k X ⟶ N}
    (h : ∀ m : F.obj X,
      f.hom (universalClass φ F k X m) = g.hom (universalClass φ F k X m)) : f = g := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (φ.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  letI : Module (O₁.obj X) N :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom N
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) N := IsScalarTower.of_compHom _ _ _
  apply ModuleCat.hom_ext
  exact _root_.PrincipalParts.linearMap_ext k h

/-- The objectwise truncation from principal parts of order `l` to order `k`. -/
noncomputable abbrev truncateApp {k l : ℕ} (h : k ≤ l) (X : Cᵒᵖ) :
    module φ F l X ⟶ module φ F k X :=
  _root_.PrincipalParts.RingHom.truncate (φ.app X).hom (F.obj X) h

/-- Objectwise truncation preserves the universal class of every section. -/
@[simp]
theorem truncateApp_universalClass {k l : ℕ} (h : k ≤ l)
    (X : Cᵒᵖ) (m : F.obj X) :
    (truncateApp φ F h X).hom (universalClass φ F l X m) =
      universalClass φ F k X m := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (φ.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  unfold truncateApp _root_.PrincipalParts.RingHom.truncate
  rw [ModuleCat.hom_ofHom]
  unfold _root_.PrincipalParts.truncate
  erw [_root_.PrincipalParts.representingEquiv_symm_apply_universalDifferential]

/-- Every objectwise principal-parts truncation is surjective. -/
theorem truncateApp_surjective {k l : ℕ} (h : k ≤ l) (X : Cᵒᵖ) :
    Function.Surjective (truncateApp φ F h X) := by
  letI : Algebra (O₁.obj X) (O₂.obj X) :=
    _root_.PrincipalParts.RingHom.algebra (φ.app X).hom
  letI : Module (O₁.obj X) (F.obj X) :=
    _root_.PrincipalParts.RingHom.sourceModule (φ.app X).hom (F.obj X)
  letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
    IsScalarTower.of_compHom _ _ _
  let qk := (_root_.PrincipalParts.relationSubmodule (O₁.obj X) (O₂.obj X) (F.obj X) k).mkQ
  let ql := (_root_.PrincipalParts.relationSubmodule (O₁.obj X) (O₂.obj X) (F.obj X) l).mkQ
  have hq : (truncateApp φ F h X).hom.comp ql = qk := by
    apply Finsupp.lhom_ext
    intro m s
    rw [← Finsupp.smul_single_one m s, map_smul, map_smul]
    congr 1
    exact truncateApp_universalClass φ F h X m
  intro y
  obtain ⟨x, rfl⟩ :=
    (_root_.PrincipalParts.relationSubmodule (O₁.obj X) (O₂.obj X) (F.obj X) k).mkQ_surjective y
  exact ⟨ql x, LinearMap.congr_fun hq x⟩

/-- Objectwise truncation commutes with restriction along every morphism of the site. -/
theorem truncateApp_naturality {k l : ℕ} (h : k ≤ l)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    restrictionMap φ F l f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (truncateApp φ F h Y) =
      truncateApp φ F h X ≫ restrictionMap φ F k f := by
  apply truncate_hom_ext_universalClass φ F l X
  intro m
  change (truncateApp φ F h Y).hom
      ((restrictionMap φ F l f).hom (universalClass φ F l X m)) =
    (restrictionMap φ F k f).hom
      ((truncateApp φ F h X).hom (universalClass φ F l X m))
  rw [restrictionMap_universalClass, truncateApp_universalClass,
    truncateApp_universalClass, restrictionMap_universalClass]

/-- Tag 09CL: the truncation morphism between principal-parts presheaves of orders `l` and `k`. -/
@[stacks 09CL "presheaf order truncation"]
noncomputable def truncate {k l : ℕ} (h : k ≤ l) :
    presheaf φ F l ⟶ presheaf φ F k where
  app X := truncateApp φ F h X
  naturality f := truncateApp_naturality φ F h f

/-- Every truncation morphism of principal-parts presheaves is an epimorphism. -/
instance truncate_epi {k l : ℕ} (h : k ≤ l) : Epi (truncate φ F h) := by
  constructor
  intro G α β hαβ
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply DFunLike.ext
  intro y
  obtain ⟨x, rfl⟩ := truncateApp_surjective φ F h X y
  exact congrArg (fun γ => (γ.app X).hom x) hαβ

/-- Presheaf truncation along a reflexive order comparison is the identity. -/
@[simp]
theorem truncate_refl (k : ℕ) :
    truncate φ F (le_refl k) = 𝟙 (presheaf φ F k) := by
  apply PresheafOfModules.hom_ext
  intro X
  apply truncate_hom_ext_universalClass φ F k X
  intro m
  change (truncateApp φ F (le_refl k) X).hom (universalClass φ F k X m) =
    universalClass φ F k X m
  exact truncateApp_universalClass φ F (le_refl k) X m

/-- Successive presheaf truncations equal truncation along the composite order comparison. -/
@[simp]
theorem truncate_trans {k l n : ℕ} (hkl : k ≤ l) (hln : l ≤ n) :
    truncate φ F hln ≫ truncate φ F hkl = truncate φ F (hkl.trans hln) := by
  apply PresheafOfModules.hom_ext
  intro X
  apply truncate_hom_ext_universalClass φ F n X
  intro m
  change (truncateApp φ F hkl X).hom
      ((truncateApp φ F hln X).hom (universalClass φ F n X m)) =
    (truncateApp φ F (hkl.trans hln) X).hom (universalClass φ F n X m)
  rw [truncateApp_universalClass, truncateApp_universalClass, truncateApp_universalClass]

section Naturality

variable {G : PresheafOfModules (ringPresheaf O₂)}

/-- Presheaf truncation is natural with respect to morphisms of module presheaves. -/
theorem truncate_naturality {k l : ℕ} (h : k ≤ l) (α : F ⟶ G) :
    map φ F l α ≫ truncate φ G h = truncate φ F h ≫ map φ F k α := by
  apply PresheafOfModules.hom_ext
  intro X
  apply truncate_hom_ext_universalClass φ F l X
  intro m
  change (truncateApp φ G h X).hom
      ((mapApp φ F l α X).hom (universalClass φ F l X m)) =
    (mapApp φ F k α X).hom
      ((truncateApp φ F h X).hom (universalClass φ F l X m))
  rw [mapApp_universalClass, truncateApp_universalClass,
    truncateApp_universalClass, mapApp_universalClass]

end Naturality

/-- Truncation in the order bound is a natural transformation between principal-parts
endofunctors. -/
noncomputable def truncateNatTrans {k l : ℕ} (h : k ≤ l) :
    functor φ l ⟶ functor φ k where
  app F := truncate φ F h
  naturality {F G} α := truncate_naturality φ F (G := G) h α

end PresheafOfModules.PrincipalParts
