/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.Category
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GlobalSections

/-! # The dual-number thickening and its ε-coefficient ideal -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor Limits
open ArtinianLocalAlgCat
open AlgebraicGeometry.AlgebraicSpace.Hom
open TrivSqZeroExt
open scoped DualNumber

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraicSpaceCat

/-- The dual-number closed immersion is a first-order thickening. -/
instance instIsFirstOrderThickening_dualNumberToResidue :
    IsFirstOrderThickening (specMap (dualNumberToResidue Λ k)) :=
  sorry

/-- The compatible family of sections of `𝒪_{Spec k[ε]}` obtained by restricting `ε`. -/
def dualNumberEpsSection :
    (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k)))).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦
      (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k)))).val.map
        (smallEtaleSite.homToId (Over.mk (specHom (dualNumber Λ k))) U.unop).op
        ((Scheme.ΓSpecIso (CommRingCat.of (dualNumber Λ k).carrier)).inv (inr (1 : k))))
    sorry

/-- Multiplication by `ε` as an endomorphism of `𝒪_{Spec k[ε]}`. -/
def mulByEps :
    SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k))) ⟶
      SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k))) :=
  (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k)))).unitHomEquiv.symm
    (dualNumberEpsSection Λ k)

/-- `mulByEps` sends the unit section to `ε`. -/
theorem mulByEps_apply :
    (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k)))).unitHomEquiv
        (mulByEps Λ k) =
      dualNumberEpsSection Λ k :=
  sorry

/-- The sheaf morphism `𝒪_{Spec k[ε]} ⟶ ℐ` sending `1` to `ε`. -/
def epsToIdeal :
    SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k))) ⟶
      Hom.idealSheaf (specMap (dualNumberToResidue Λ k)) :=
  kernel.lift (Hom.idealSheafMap (specMap (dualNumberToResidue Λ k))) (mulByEps Λ k) sorry ≫
    (Hom.idealSheaf_spec (specMap (dualNumberToResidue Λ k))).inv

/-- `epsToIdeal` is the kernel lift of multiplication by `ε`. -/
theorem epsToIdeal_comp_ι :
    epsToIdeal Λ k ≫ Hom.idealSheafι (specMap (dualNumberToResidue Λ k)) = mulByEps Λ k :=
  sorry

/-- The structure-module morphism to the direct image along the residue immersion,
obtained by adjunction from the canonical pullback identification. -/
def residueUnitToPushforward :
    SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k))) ⟶
      (Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
        (SheafOfModules.unit (structureSheaf (specObj (residue Λ k)))) :=
  (Modules.pullbackPushforwardAdjunction (specMap (dualNumberToResidue Λ k))).homEquiv
    (SheafOfModules.unit (structureSheaf (specObj (dualNumber Λ k))))
    (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))
    (Modules.structureModulePullbackIso (specMap (dualNumberToResidue Λ k))).inv

/-- Multiplication by `ε` is an epimorphism onto the kernel ideal. -/
instance instEpi_epsToIdeal : Epi (epsToIdeal Λ k) :=
  sorry

/-- ε-coefficient sheaf map `ℐ_{Spec k / Spec k[ε]} ⟶ t_* 𝒪_{Spec k}`, the unique
`𝒪_{Spec k[ε]}`-linear factorization of `residueUnitToPushforward` through
`epsToIdeal`. Its component on every étale chart is the projection `a·ε ↦ a`
sending the homToId-restriction of `ε` to the homToId-restriction of `1`. -/
def residueKernelToPushforward :
    Hom.idealSheaf (specMap (dualNumberToResidue Λ k)) ⟶
      (Modules.pushforward (specMap (dualNumberToResidue Λ k))).obj
        (SheafOfModules.unit (structureSheaf (specObj (residue Λ k)))) :=
  CategoryTheory.Abelian.epiDesc (epsToIdeal Λ k) (residueUnitToPushforward Λ k) sorry

/-- `residueKernelToPushforward` is characterized by sending `ε` to `1`. -/
theorem residueKernelToPushforward_comp_eps :
    epsToIdeal Λ k ≫ residueKernelToPushforward Λ k =
      residueUnitToPushforward Λ k :=
  sorry

/-- ε-coefficient projection `t^* ℐ_{Spec k / Spec k[ε]} ⟶ 𝒪_{Spec k}`, the adjunct
of `residueKernelToPushforward`. -/
def residueKernelToUnit :
    (Modules.pullback (specMap (dualNumberToResidue Λ k))).obj
        (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) ⟶
      SheafOfModules.unit (structureSheaf (specObj (residue Λ k))) :=
  ((Modules.pullbackPushforwardAdjunction
      (specMap (dualNumberToResidue Λ k))).homEquiv
      (Hom.idealSheaf (specMap (dualNumberToResidue Λ k)))
      (SheafOfModules.unit (structureSheaf (specObj (residue Λ k))))).symm
    (residueKernelToPushforward Λ k)

/-- Inverse ε-coefficient map `𝒪_{Spec k} ⟶ t^* ℐ`, sending `a` to `a·ε`. -/
def residueUnitToKernel :
    SheafOfModules.unit (structureSheaf (specObj (residue Λ k))) ⟶
      (Modules.pullback (specMap (dualNumberToResidue Λ k))).obj
        (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) :=
  Modules.structureModulePullbackInv (specMap (dualNumberToResidue Λ k)) ≫
    (Modules.pullback (specMap (dualNumberToResidue Λ k))).map (epsToIdeal Λ k)

/-- ε-coefficient isomorphism `t^* ℐ_{Spec k / Spec k[ε]} ≅ 𝒪_{Spec k}`. -/
def residueKernelIsoUnit :
    (Modules.pullback (specMap (dualNumberToResidue Λ k))).obj
        (Hom.idealSheaf (specMap (dualNumberToResidue Λ k))) ≅
      SheafOfModules.unit (structureSheaf (specObj (residue Λ k))) :=
  let laws :
      (residueKernelToUnit Λ k ≫ residueUnitToKernel Λ k = 𝟙 _) ∧
      (residueUnitToKernel Λ k ≫ residueKernelToUnit Λ k = 𝟙 _) := sorry
  { hom := residueKernelToUnit Λ k
    inv := residueUnitToKernel Λ k
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

end FlatAlgebraicSpaceCat
