/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
      IsCocartesian.map p (residueToDualNumber Λ k) φ ψ := sorry

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
        (fiberInclusion.map α.hom ≫ ψ) := sorry

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
      infinitesimalAutomorphismsAt p x0 y0' ψ := sorry

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
      infinitesimalAutomorphismsAt p y0 y0' ψ := sorry

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
      (fiberIso_of_pushforward p φ ψ).conjAut a.val := sorry

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
      (fiberIso_of_fiberIso p α φ ψ).conjAut a.val := sorry

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
        (infAutAtIso_of_pushforward p ψ ψ') := sorry

/-- Transport by the identity residue-fibre automorphism fixes every infinitesimal
automorphism. -/
theorem infAutAtIso_of_fiberIso_one_apply
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    infAutAtIso_of_fiberIso p (1 : Aut x0) φ φ a = a := sorry

/-- Transport by a product of residue-fibre automorphisms is successive transport by
the right factor and then the left factor. -/
theorem infAutAtIso_of_fiberIso_mul_apply
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (β γ : Aut x0) (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    infAutAtIso_of_fiberIso p (β * γ) φ φ a =
      infAutAtIso_of_fiberIso p β φ φ
        (infAutAtIso_of_fiberIso p γ φ φ a) := sorry

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
        (fiberAutHom p (residueToDualNumber Λ k) φ β)⁻¹ := sorry

end CategoryTheory.Functor
