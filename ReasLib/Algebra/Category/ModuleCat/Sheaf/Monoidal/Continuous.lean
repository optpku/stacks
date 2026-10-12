/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.Sites.Monoidal.Continuous

/-!
# Monoidal continuous inverse image for module sheaves

This file installs the coefficient-generic monoidal-localization construction for sheaves of
modules.  The resulting instance is canonical and reusable by projection formulas.
-/

@[expose] public section

noncomputable section

universe u₁ v₁ u₂ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {Λ : Type w} [CommRing Λ]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (G : C ⥤ D) [G.IsContinuous J K] [G.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ ModuleCat.{w} Λ, G.op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [HasWeakSheafify K (ModuleCat.{w} Λ)]
variable [(J.W (A := ModuleCat.{w} Λ)).IsMonoidal]
variable [(K.W (A := ModuleCat.{w} Λ)).IsMonoidal]

/-- Continuous inverse image of module sheaves is canonically strong monoidal. -/
@[implicit_reducible]
noncomputable instance moduleSheafPushforwardContinuousMonoidal :
    (G.sheafPushforwardContinuous (ModuleCat.{w} Λ) J K).Monoidal :=
  G.sheafPushforwardContinuousMonoidal

end CategoryTheory.Functor
