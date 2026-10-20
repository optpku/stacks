/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.Morphisms
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.QuasiCoherent

/-!
# Morphisms of basis-indexed quasi-coherent gluings

This module provides compatibility and realization predicates for local scheme and module maps,
together with the canonical local module map obtained from global realization maps.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing

/-- Families of local scheme maps and pullback-linear module maps are compatible when the scheme
maps commute with the basis transitions and the module maps commute with both module transition
systems. -/
def IsMorphismCompatible {S : Scheme.{u}}
    (D E : BasisQuasiCoherentGluing.{u, v} S) (indexEquiv : D.ι ≃ E.ι)
    (localSchemeMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
    (localModuleMap : ∀ i : D.ι,
      (pullback (localSchemeMap i)).obj (E.F (indexEquiv i)) ⟶ D.F i) : Prop :=
  D.toBasisSchemeGluing.IsMorphismCompatible E.toBasisSchemeGluing indexEquiv localSchemeMap ∧
    ∀ ⦃i j : D.ι⦄ (hij : D.U i ≤ D.U j)
      (hij' : E.U (indexEquiv i) ≤ E.U (indexEquiv j)),
      let P := pseudofunctor.comp (Bicategory.Adj.forget₁ (B := Cat))
      let dObj (k : D.ι) : Pseudofunctor.Grothendieck P :=
        { base := Opposite.op (D.X k)
          fiber := by
            change (D.X k).Modules
            exact D.F k }
      let eObj (k : E.ι) : Pseudofunctor.Grothendieck P :=
        { base := Opposite.op (E.X k)
          fiber := by
            change (E.X k).Modules
            exact E.F k }
      let dTransition : dObj j ⟶ dObj i :=
        { base := (D.rho hij).op
          fiber := by
            change (pullback (D.rho hij)).obj (D.F j) ⟶ D.F i
            exact (D.theta hij).hom }
      let eTransition : eObj (indexEquiv j) ⟶ eObj (indexEquiv i) :=
        { base := (E.rho hij').op
          fiber := by
            change (pullback (E.rho hij')).obj (E.F (indexEquiv j)) ⟶
              E.F (indexEquiv i)
            exact (E.theta hij').hom }
      let component (k : D.ι) : eObj (indexEquiv k) ⟶ dObj k :=
        { base := (localSchemeMap k).op
          fiber := by
            change (pullback (localSchemeMap k)).obj (E.F (indexEquiv k)) ⟶ D.F k
            exact localModuleMap k }
      eTransition ≫ component i = component j ≫ dTransition

/-- Restricting a global pullback-module map to a basis open and transporting it through the
equipped local identifications gives a canonical pullback-linear local module map. -/
noncomputable def restrictedModuleMap {S : Scheme.{u}}
    (D E : BasisQuasiCoherentGluing.{u, v} S) (indexEquiv : D.ι ≃ E.ι)
    (localSchemeMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
    (schemeCompatible : D.toBasisSchemeGluing.IsMorphismCompatible
      E.toBasisSchemeGluing indexEquiv localSchemeMap)
    (R : D.Realization) (R' : E.Realization) (globalMap : R.Y ⟶ R'.Y)
    (overBase : globalMap ≫ R'.toBase = R.toBase)
    (localSchemeAgreement : ∀ i : D.ι,
      (R.localSchemeIso i).hom ≫ localSchemeMap i =
        D.toBasisSchemeGluing.restrictedMap E.toBasisSchemeGluing indexEquiv localSchemeMap
            schemeCompatible R.toSchemeRealization R'.toSchemeRealization globalMap overBase i ≫
          (R'.localSchemeIso (indexEquiv i)).hom)
    (globalModuleMap : (pullback globalMap).obj R'.M ⟶ R.M) (i : D.ι) :
    (pullback (localSchemeMap i)).obj (E.F (indexEquiv i)) ⟶ D.F i := by
  let restrictionMap : ∀ i : D.ι,
      (R.toBase ⁻¹ᵁ D.U i).toScheme ⟶
        (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).toScheme :=
    D.toBasisSchemeGluing.restrictedMap E.toBasisSchemeGluing indexEquiv localSchemeMap
      schemeCompatible R.toSchemeRealization R'.toSchemeRealization globalMap overBase
  have restrictionMap_ι :
      restrictionMap i ≫ (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).ι =
        (R.toBase ⁻¹ᵁ D.U i).ι ≫ globalMap := by
    dsimp only [restrictionMap, Scheme.BasisSchemeGluing.restrictedMap,
      Realization.toSchemeRealization]
    apply Scheme.Hom.resLE_comp_ι
  let localGlobalMap :
      (pullback (restrictionMap i)).obj
          (@restrict _ _ R'.M (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).ι
            (Scheme.Opens.instIsOpenImmersionι _)) ⟶
        @restrict _ _ R.M (R.toBase ⁻¹ᵁ D.U i).ι
          (Scheme.Opens.instIsOpenImmersionι _) :=
    (pullback (restrictionMap i)).map
        ((@restrictFunctorIsoPullback _ _
          (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).ι
            (Scheme.Opens.instIsOpenImmersionι _)).hom.app R'.M) ≫
      (pullbackComp (restrictionMap i)
        (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).ι).hom.app R'.M ≫
      (pullbackCongr restrictionMap_ι).hom.app R'.M ≫
      (pullbackComp (R.toBase ⁻¹ᵁ D.U i).ι globalMap).inv.app R'.M ≫
      (pullback (R.toBase ⁻¹ᵁ D.U i).ι).map globalModuleMap ≫
      (@restrictFunctorIsoPullback _ _ (R.toBase ⁻¹ᵁ D.U i).ι
        (Scheme.Opens.instIsOpenImmersionι _)).inv.app R.M
  exact (pullback (localSchemeMap i)).map
      (Realization.inverseLocalModuleIso E R' (indexEquiv i)).hom ≫
    (pullbackComp (localSchemeMap i) (R'.localSchemeIso (indexEquiv i)).inv).hom.app
      (@restrict _ _ R'.M (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).ι
        (Scheme.Opens.instIsOpenImmersionι _)) ≫
    (pullbackCongr (by
      apply (cancel_mono (R'.localSchemeIso (indexEquiv i)).hom).1
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      dsimp only [restrictionMap]
      rw [← cancel_epi (R.localSchemeIso i).hom]
      simpa only [Realization.toSchemeRealization, Category.assoc, Iso.hom_inv_id_assoc] using
        localSchemeAgreement i)).hom.app
        (@restrict _ _ R'.M (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).ι
          (Scheme.Opens.instIsOpenImmersionι _)) ≫
    (pullbackComp (R.localSchemeIso i).inv (restrictionMap i)).inv.app
      (@restrict _ _ R'.M (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).ι
        (Scheme.Opens.instIsOpenImmersionι _)) ≫
    (pullback (R.localSchemeIso i).inv).map localGlobalMap ≫
    (Realization.inverseLocalModuleIso D R i).inv

/-- Global scheme and pullback-module maps realize compatible local maps when the global scheme
map lies over the base, its canonical restrictions recover the local scheme maps, and the
canonical restricted module maps recover the local module maps. -/
def IsRealizationMap {S : Scheme.{u}}
    (D E : BasisQuasiCoherentGluing.{u, v} S) (indexEquiv : D.ι ≃ E.ι)
    (localSchemeMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
    (localModuleMap : ∀ i : D.ι,
      (pullback (localSchemeMap i)).obj (E.F (indexEquiv i)) ⟶ D.F i)
    (compatible : D.IsMorphismCompatible E indexEquiv localSchemeMap localModuleMap)
    (R : D.Realization) (R' : E.Realization) (globalMap : R.Y ⟶ R'.Y)
    (globalModuleMap : (pullback globalMap).obj R'.M ⟶ R.M) : Prop :=
  ∃ overBase : globalMap ≫ R'.toBase = R.toBase,
    ∃ localSchemeAgreement : ∀ i : D.ι,
      (R.localSchemeIso i).hom ≫ localSchemeMap i =
        D.toBasisSchemeGluing.restrictedMap E.toBasisSchemeGluing indexEquiv localSchemeMap
            compatible.1 R.toSchemeRealization R'.toSchemeRealization globalMap overBase i ≫
          (R'.localSchemeIso (indexEquiv i)).hom,
      ∀ i : D.ι,
        D.restrictedModuleMap E indexEquiv localSchemeMap compatible.1 R R' globalMap overBase
            localSchemeAgreement globalModuleMap i =
          localModuleMap i

/-- Compatible local scheme and pullback-linear module maps between basis-indexed
quasi-coherent gluing data induce global maps between arbitrary equipped realizations that
recover all prescribed local maps. -/
theorem existsRealizationMap {S : Scheme.{u}}
    (D E : BasisQuasiCoherentGluing.{u, v} S) (indexEquiv : D.ι ≃ E.ι)
    (localSchemeMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
    (localModuleMap : ∀ i : D.ι,
      (pullback (localSchemeMap i)).obj (E.F (indexEquiv i)) ⟶ D.F i)
    (compatible : D.IsMorphismCompatible E indexEquiv localSchemeMap localModuleMap)
    (R : D.Realization) (R' : E.Realization) :
    ∃ (globalMap : R.Y ⟶ R'.Y) (globalModuleMap : (pullback globalMap).obj R'.M ⟶ R.M),
      D.IsRealizationMap E indexEquiv localSchemeMap localModuleMap compatible R R' globalMap
        globalModuleMap := sorry

end AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing
