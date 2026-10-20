/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.IdealMultiple
public import Mathlib.Algebra.Torsor.Defs

/-!
# Lifts of an 𝒪-linear map along a first-order thickening

On a same-site first-order thickening π : 𝒪' ⟶ 𝒪, an 𝒪'-linear lift of φ : i^* ℱ' ⟶ i^* 𝒢'
is an 𝒪'-module map ℱ' ⟶ 𝒢' making the extension-restriction unit square commute. Hom_𝒪(ℱ, ℐ 𝒢')
acts by adding a map into the kernel of the unit of 𝒢'.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
variable (φ : (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj G')

/-- An 𝒪'-linear lift of an 𝒪-linear map φ : i^* ℱ' ⟶ i^* 𝒢' to a map ℱ' ⟶ 𝒢'. -/
structure Lift where
  /-- The underlying 𝒪'-module morphism ℱ' ⟶ 𝒢'. -/
  hom : F' ⟶ G'
  /-- Compatibility with φ along the extension-restriction units. -/
  comm : hom ≫ extendRestrictUnit π G' =
    extendRestrictUnit π F' ≫ (restrictionAlong π).map φ

namespace Lift

/-- Assemble a lift of φ from an 𝒪'-module map and the commuting unit square. -/
def of (hom : F' ⟶ G')
    (h : CommSq hom (extendRestrictUnit π F') (extendRestrictUnit π G')
      ((restrictionAlong π).map φ)) :
    Lift F' G' φ where
  hom := hom
  comm := h.w

/-- A lift of φ is an 𝒪'-module map whose unit square with φ commutes. -/
theorem spec (f : Lift F' G' φ) :
    CommSq f.hom (extendRestrictUnit π F') (extendRestrictUnit π G')
      ((restrictionAlong π).map φ) := sorry

/-- The unit square for the Hom_{𝒪'}(ℱ', ℐ 𝒢')-translate of a lift. -/
theorem vadd_comm (β : F' ⟶ idealMulO' π G') (f : Lift F' G' φ) :
    (f.hom + β ≫ kernel.ι (extendRestrictUnit π G')) ≫ extendRestrictUnit π G' =
      extendRestrictUnit π F' ≫ (restrictionAlong π).map φ := sorry

/-- Translate a lift of φ by an 𝒪'-module morphism β : ℱ' ⟶ ℐ 𝒢'. -/
def vadd (β : F' ⟶ idealMulO' π G') (f : Lift F' G' φ) : Lift F' G' φ where
  hom := f.hom + β ≫ kernel.ι (extendRestrictUnit π G')
  comm := vadd_comm F' G' φ β f

/-- The underlying map of a Hom_{𝒪'}(ℱ', ℐ 𝒢')-translate. -/
theorem vadd_hom (β : F' ⟶ idealMulO' π G') (f : Lift F' G' φ) :
    (vadd F' G' φ β f).hom = f.hom + β ≫ kernel.ι (extendRestrictUnit π G') := sorry

/-- Any two lifts of φ differ by a unique 𝒪-module morphism ℱ ⟶ ℐ 𝒢'. -/
theorem existsUnique_vsub (f g : Lift F' G' φ) :
    ∃! α : (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
        idealMul π G',
      ∃ β : F' ⟶ idealMulO' π G',
        (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map β = α ∧
          vadd F' G' φ β g = f :=
  sorry

end Lift

/-- Lifts of a map between reductions are empty or form an additive torsor under maps
from the reduced source to the target's ideal multiple. Translation by the scalar extension
of a map into the reduction kernel adds that map followed by the kernel inclusion. -/
theorem lift_isEmpty_or_addTorsor :
    IsEmpty (Lift F' G' φ) ∨
      ∃ t : AddTorsor
          ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
            idealMul π G')
          (Lift F' G' φ),
        ∀ (β : F' ⟶ idealMulO' π G') (ℓ : Lift F' G' φ),
          t.toAddAction.toAddSemigroupAction.toVAdd.vadd
              ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map β) ℓ =
            Lift.vadd F' G' φ β ℓ :=
  sorry

end SheafOfModules.RingedSite.FirstOrderThickening
