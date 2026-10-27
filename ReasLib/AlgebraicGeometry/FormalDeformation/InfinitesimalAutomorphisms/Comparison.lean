/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism

/-!
# Comparison of infinitesimal automorphism groups

Canonical comparisons identify infinitesimal automorphism groups attached to different
dual-number pushforwards and to isomorphic residue-fibre objects.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open Functor Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [IsFibered.InGroupoids p.op]

namespace CategoryTheory.Functor

/-- The canonical vertical isomorphism between two cocartesian dual-number pushforwards
of one residue-fibre object. -/
noncomputable def fiberIso_of_pushforward
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    x0' ≅ y0' :=
  isoMk
    (@IsCocartesian.codomainUniqueUpToIso _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) φ
      (IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian p
        (residueToDualNumber Λ k) φ)
      _ ψ
      (IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian p
        (residueToDualNumber Λ k) ψ))
    (@IsCocartesian.map_isHomLift _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) φ
      (IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian p
        (residueToDualNumber Λ k) φ)
      _ ψ inferInstance)

/-- The underlying total-category map of `fiberIso_of_pushforward` is the canonical
cocartesian comparison map. -/
theorem fiberIso_of_pushforward_hom
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    fiberInclusion.map (fiberIso_of_pushforward p φ ψ).hom =
      IsCocartesian.map p (residueToDualNumber Λ k) φ ψ := rfl

/-- The canonical vertical isomorphism between pushforward targets induced by a residue-fibre
isomorphism. -/
noncomputable def fiberIso_of_fiberIso
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    x0' ≅ y0' := by
  let hα : p.IsHomLift (𝟙 (residue Λ k)) (fiberInclusion.mapIso α).hom :=
    α.hom.property
  let hψ : p.IsCocartesian (residueToDualNumber Λ k)
      (fiberInclusion.map α.hom ≫ ψ) :=
    @IsCocartesian.of_iso_comp _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) ψ
      inferInstance _ (fiberInclusion.mapIso α) hα
  let hpre : p.IsHomLift (residueToDualNumber Λ k)
      (fiberInclusion.map α.hom ≫ ψ) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ p _ _ _ _ _ (residueToDualNumber Λ k) ψ
      inferInstance (fiberInclusion.map α.hom) inferInstance
  exact
    isoMk
      (@IsCocartesian.codomainUniqueUpToIso _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) φ
        (IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian p
          (residueToDualNumber Λ k) φ)
        _ (fiberInclusion.map α.hom ≫ ψ) hψ)
      (@IsCocartesian.map_isHomLift _ _ _ _ p _ _ _ _ (residueToDualNumber Λ k) φ
        (IsStronglyCocartesian.isCocartesian_of_isStronglyCocartesian p
          (residueToDualNumber Λ k) φ)
        _ (fiberInclusion.map α.hom ≫ ψ) hpre)

/-- The underlying total-category map of `fiberIso_of_fiberIso` is the cocartesian
factorization of the precomposed pushforward. -/
theorem fiberIso_of_fiberIso_hom
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    fiberInclusion.map (fiberIso_of_fiberIso p α φ ψ).hom =
      IsCocartesian.map p (residueToDualNumber Λ k) φ
        (fiberInclusion.map α.hom ≫ ψ) := rfl

private theorem fiberIso_of_pushforward_fac
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    φ ≫ fiberInclusion.map (fiberIso_of_pushforward p φ ψ).hom = ψ := by
  rw [fiberIso_of_pushforward_hom]
  exact IsCocartesian.fac p (residueToDualNumber Λ k) φ ψ

private theorem fiberIso_of_fiberIso_fac
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    φ ≫ fiberInclusion.map (fiberIso_of_fiberIso p α φ ψ).hom =
      fiberInclusion.map α.hom ≫ ψ := by
  rw [fiberIso_of_fiberIso_hom]
  exact IsCocartesian.fac p (residueToDualNumber Λ k) φ
    (fiberInclusion.map α.hom ≫ ψ)

/-- A square of pushforwards induces the corresponding square of their retractions. -/
private theorem comparison_retraction
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (e : x0' ≅ y0')
    (he : φ ≫ fiberInclusion.map e.hom = fiberInclusion.map α.hom ≫ ψ) :
    fiberInclusion.map e.hom ≫ retraction p ψ =
      retraction p φ ≫ fiberInclusion.map α.hom := by
  apply IsStronglyCocartesian.ext p (residueToDualNumber Λ k) φ
    (dualNumberToResidue Λ k)
  calc
    φ ≫ (fiberInclusion.map e.hom ≫ retraction p ψ) =
        (fiberInclusion.map α.hom ≫ ψ) ≫ retraction p ψ := by
      rw [← Category.assoc, he]
    _ = fiberInclusion.map α.hom := by
      rw [Category.assoc, retraction_comp, Category.comp_id]
    _ = φ ≫ (retraction p φ ≫ fiberInclusion.map α.hom) := by
      rw [← Category.assoc, retraction_comp, Category.id_comp]

private theorem comparison_conj_mem_iff
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (e : x0' ≅ y0')
    (he : φ ≫ fiberInclusion.map e.hom = fiberInclusion.map α.hom ≫ ψ)
    (a : Aut x0') :
    e.conjAut a ∈ infinitesimalAutomorphismsAt p y0 y0' ψ ↔
      a ∈ infinitesimalAutomorphismsAt p x0 x0' φ := by
  have hcomp := comparison_retraction p α φ ψ e he
  rw [mem_infinitesimalAutomorphismsAt_iff, mem_infinitesimalAutomorphismsAt_iff]
  change
    ((fiberInclusion.mapIso e).inv ≫ fiberInclusion.map a.hom ≫
        (fiberInclusion.mapIso e).hom) ≫ retraction p ψ = retraction p ψ ↔ _
  simp only [Category.assoc]
  rw [(fiberInclusion.mapIso e).inv_comp_eq]
  simp only [Functor.mapIso_hom]
  rw [hcomp, ← Category.assoc, cancel_mono]

private theorem map_infinitesimalAutomorphismsAt_of_comparison
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (e : x0' ≅ y0')
    (he : φ ≫ fiberInclusion.map e.hom = fiberInclusion.map α.hom ≫ ψ) :
    (infinitesimalAutomorphismsAt p x0 x0' φ).map e.conjAut =
      infinitesimalAutomorphismsAt p y0 y0' ψ := by
  apply SetLike.ext
  intro b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (comparison_conj_mem_iff p α φ ψ e he a).mpr ha
  · intro hb
    refine ⟨e.conjAut.symm b, ?_, e.conjAut.apply_symm_apply b⟩
    apply (comparison_conj_mem_iff p α φ ψ e he (e.conjAut.symm b)).mp
    simpa only [MulEquiv.apply_symm_apply] using hb

/-- Conjugation by the pushforward comparison maps the first infinitesimal automorphism
subgroup onto the second one. -/
theorem map_infinitesimalAutomorphismsAt_of_pushforward
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    (infinitesimalAutomorphismsAt p x0 x0' φ).map
        (fiberIso_of_pushforward p φ ψ).conjAut =
      infinitesimalAutomorphismsAt p x0 y0' ψ := by
  apply map_infinitesimalAutomorphismsAt_of_comparison p (Iso.refl x0) φ ψ
    (fiberIso_of_pushforward p φ ψ)
  simpa only [Iso.refl_hom, Functor.map_id, Category.id_comp] using
    fiberIso_of_pushforward_fac p φ ψ

/-- Conjugation by the comparison induced by a residue-fibre isomorphism maps the first
infinitesimal automorphism subgroup onto the second one. -/
theorem map_infinitesimalAutomorphismsAt_of_fiberIso
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    (infinitesimalAutomorphismsAt p x0 x0' φ).map
        (fiberIso_of_fiberIso p α φ ψ).conjAut =
      infinitesimalAutomorphismsAt p y0 y0' ψ := by
  exact map_infinitesimalAutomorphismsAt_of_comparison p α φ ψ
    (fiberIso_of_fiberIso p α φ ψ) (fiberIso_of_fiberIso_fac p α φ ψ)

/-- Conjugation by the canonical pushforward comparison gives the canonical group equivalence
between the corresponding infinitesimal automorphism subgroups. -/
noncomputable def infAutAtIso_of_pushforward
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      infinitesimalAutomorphismsAt p x0 y0' ψ :=
  (MulEquiv.subgroupMap (fiberIso_of_pushforward p φ ψ).conjAut
      (infinitesimalAutomorphismsAt p x0 x0' φ)).trans
    (MulEquiv.subgroupCongr (map_infinitesimalAutomorphismsAt_of_pushforward p φ ψ))

/-- The canonical pushforward comparison equivalence acts by conjugation on elements. -/
theorem infAutAtIso_of_pushforward_apply
    {x0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (infAutAtIso_of_pushforward p φ ψ a).val =
      (fiberIso_of_pushforward p φ ψ).conjAut a.val := rfl

/-- Conjugation by the comparison induced by a residue-fibre isomorphism gives the canonical
group equivalence between the corresponding infinitesimal automorphism subgroups. -/
noncomputable def infAutAtIso_of_fiberIso
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      infinitesimalAutomorphismsAt p y0 y0' ψ :=
  (MulEquiv.subgroupMap (fiberIso_of_fiberIso p α φ ψ).conjAut
      (infinitesimalAutomorphismsAt p x0 x0' φ)).trans
    (MulEquiv.subgroupCongr (map_infinitesimalAutomorphismsAt_of_fiberIso p α φ ψ))

/-- The residue-fibre comparison equivalence acts by conjugation on elements. -/
theorem infAutAtIso_of_fiberIso_apply
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (infAutAtIso_of_fiberIso p α φ ψ a).val =
      (fiberIso_of_fiberIso p α φ ψ).conjAut a.val := rfl

/-- The residue-fibre comparison is compatible with changing both chosen pushforwards. -/
theorem infAutAtIso_of_fiberIso_independent_of_pushforward
    {x0 y0 : p.Fiber (residue Λ k)}
    {x0' x0'' y0' y0'' : p.Fiber (dualNumber Λ k)}
    (α : x0 ≅ y0)
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (φ' : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0'')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    (ψ' : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0'')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ']
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ'] :
    (infAutAtIso_of_pushforward p φ φ').trans
        (infAutAtIso_of_fiberIso p α φ' ψ') =
      (infAutAtIso_of_fiberIso p α φ ψ).trans
        (infAutAtIso_of_pushforward p ψ ψ') := by
  have h :
      fiberIso_of_pushforward p φ φ' ≪≫ fiberIso_of_fiberIso p α φ' ψ' =
        fiberIso_of_fiberIso p α φ ψ ≪≫ fiberIso_of_pushforward p ψ ψ' := by
    apply Iso.ext
    apply Fiber.hom_ext
    simp only [Iso.trans_hom, Functor.map_comp]
    apply IsCocartesian.ext p (residueToDualNumber Λ k) φ
    calc
      φ ≫ (fiberInclusion.map (fiberIso_of_pushforward p φ φ').hom ≫
          fiberInclusion.map (fiberIso_of_fiberIso p α φ' ψ').hom) =
          fiberInclusion.map α.hom ≫ ψ' := by
        rw [← Category.assoc, fiberIso_of_pushforward_fac, fiberIso_of_fiberIso_fac]
      _ = φ ≫ (fiberInclusion.map (fiberIso_of_fiberIso p α φ ψ).hom ≫
          fiberInclusion.map (fiberIso_of_pushforward p ψ ψ').hom) := by
        rw [← Category.assoc, fiberIso_of_fiberIso_fac, Category.assoc,
          fiberIso_of_pushforward_fac]
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  simpa only [MulEquiv.trans_apply, infAutAtIso_of_fiberIso_apply,
    infAutAtIso_of_pushforward_apply, ← Iso.trans_conjAut] using
    congrArg (fun e => e.conjAut a.val) h

/-- The comparison induced by a residue automorphism is its cocartesian pushforward. -/
private theorem fiberIso_of_fiberIso_aut
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (β : Aut x0) :
    fiberIso_of_fiberIso p β φ φ = fiberAutHom p (residueToDualNumber Λ k) φ β := by
  apply Iso.ext
  apply Fiber.hom_ext
  rfl

/-- Transport by the identity residue-fibre automorphism fixes every infinitesimal
automorphism. -/
theorem infAutAtIso_of_fiberIso_one_apply
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    infAutAtIso_of_fiberIso p (1 : Aut x0) φ φ a = a := by
  apply Subtype.ext
  rw [infAutAtIso_of_fiberIso_apply, fiberIso_of_fiberIso_aut, map_one]
  change (Iso.refl x0').conjAut a.val = a.val
  simp [Iso.conjAut_apply]

/-- Transport by a product of residue-fibre automorphisms is successive transport by
the right factor and then the left factor. -/
theorem infAutAtIso_of_fiberIso_mul_apply
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (β γ : Aut x0) (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    infAutAtIso_of_fiberIso p (β * γ) φ φ a =
      infAutAtIso_of_fiberIso p β φ φ
        (infAutAtIso_of_fiberIso p γ φ φ a) := by
  apply Subtype.ext
  simp only [infAutAtIso_of_fiberIso_apply, fiberIso_of_fiberIso_aut, map_mul]
  rw [Aut.Aut_mul_def, Iso.trans_conjAut]

/-- The canonical action of residue-fibre automorphisms on infinitesimal automorphisms. -/
noncomputable instance instMulDistribMulAction_aut_infAutAt
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    MulDistribMulAction (Aut x0) (infinitesimalAutomorphismsAt p x0 x0' φ) where
  smul β a := infAutAtIso_of_fiberIso p β φ φ a
  one_smul := infAutAtIso_of_fiberIso_one_apply p φ
  mul_smul := infAutAtIso_of_fiberIso_mul_apply p φ
  smul_one β := (infAutAtIso_of_fiberIso p β φ φ).map_one
  smul_mul β a b := (infAutAtIso_of_fiberIso p β φ φ).map_mul a b

/-- The action is conjugation by the automorphism induced on the dual-number pushforward. -/
theorem infAutAt_smul_eq_fiberAutHom_conj
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (β : Aut x0) (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (β • a).val =
      fiberAutHom p (residueToDualNumber Λ k) φ β * a.val *
        (fiberAutHom p (residueToDualNumber Λ k) φ β)⁻¹ := by
  change (infAutAtIso_of_fiberIso p β φ φ a).val = _
  rw [infAutAtIso_of_fiberIso_apply, fiberIso_of_fiberIso_aut]
  simp [Iso.conjAut_apply, Aut.Aut_mul_def, Aut.Aut_inv_def]

end CategoryTheory.Functor
