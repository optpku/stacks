/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek.Basic
import StacksCheckRecall

/-!
# Lemma 18.16.4

For a fully faithful continuous and cocontinuous functor of sites, the unit for lower shriek and
the counit for direct image are invertible on abelian sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
variable (hu : u.FullyFaithful)

section Unit

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasPointwiseRightKanExtension P]
variable (ℱ : Sheaf J AddCommGrpCat.{w})
variable [u.op.HasPointwiseLeftKanExtension ℱ.obj]

/- Lemma 18.16.4 (1) (077I): the unit `ℱ ⟶ u⁻¹(uₗ ℱ)` is invertible. -/
@[stacks 077I "(1)"]
#check (Functor.FullyFaithful.sheafAdjunctionContinuous_unit_app_isIso
  J K u hu ℱ :
    IsIso ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app ℱ))

end Unit

section Counit

variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasPointwiseRightKanExtension P]
variable (ℱ : Sheaf J AddCommGrpCat.{w})

/- Lemma 18.16.4 (2) (077I): the counit `u⁻¹(u_* ℱ) ⟶ ℱ` is invertible. -/
@[stacks 077I "(2)"]
#check (Functor.FullyFaithful.sheafAdjunctionCocontinuous_counit_app_isIso
  J K u hu ℱ :
    IsIso ((u.sheafAdjunctionCocontinuous AddCommGrpCat.{w} J K).counit.app ℱ))

end Counit

end CategoryTheory
