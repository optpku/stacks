/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import StacksCheckRecall

/-!
# Lemma 18.11.3

The same-site extension/restriction-of-scalars adjunction and its Hom equivalence are owned by
`SheafOfModules.ChangeOfRings`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.ChangeOfRings

noncomputable section

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪₁ 𝒪₂ : Sheaf J RingCat.{u}}
variable (α : 𝒪₁ ⟶ 𝒪₂)
variable (𝒢 : SheafOfModules 𝒪₁) (ℱ : SheafOfModules 𝒪₂)

/- Lemma 18.11.3 (03CZ): restriction and extension of scalars along a morphism of ring sheaves
on one site induce the canonical Hom-set equivalence. -/
@[stacks 03CZ]
#check
  ((extendRestrictHomEquiv α 𝒢 ℱ).symm :
    (𝒢 ⟶ (SheafOfModules.restrictScalars α).obj ℱ) ≃
      ((extendScalars α).obj 𝒢 ⟶ ℱ))

/- The equivalence is the Hom equivalence of the reusable bundled adjunction. -/
#check (extendRestrictAdjunction α :
  extendScalars α ⊣ SheafOfModules.restrictScalars α)

/- The owner API exposes the forward-map formula through the adjunction unit. -/
#check extendRestrictHomEquiv_apply α 𝒢 ℱ
