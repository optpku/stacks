/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Monoidal inverse image for continuous functors of sites

The continuous inverse-image functor is precomposition on underlying presheaves.  When the
monoidal structures on sheaves are the canonical structures induced by sheafification, its
strong monoidal structure follows from the universal property of monoidal localization.

This file owns that construction once, so geometric projection-formula APIs do not need an
extra, manually supplied lax-monoidal instance at every use site.
-/

@[expose] public section

noncomputable section

universe u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (G : C ⥤ D) [G.IsContinuous J K] [G.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- Sheafification followed by continuous inverse image is the monoidal-localization lift of
precomposition followed by sheafification. -/
@[implicit_reducible]
noncomputable def sheafPushforwardContinuousLifting :
    Localization.Lifting (presheafToSheaf K A) K.W
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op ⋙ presheafToSheaf J A)
      (G.sheafPushforwardContinuous A J K) where
  iso := (G.pushforwardContinuousSheafificationCompatibility A J K).symm

/-- The canonical strong monoidal structure on continuous inverse image, for the monoidal
structures on sheaves induced by monoidal sheafification. -/
@[implicit_reducible]
noncomputable def sheafPushforwardContinuousMonoidal
    [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal] :
    letI := Sheaf.monoidalCategory K A
    letI := Sheaf.monoidalCategory J A
    (G.sheafPushforwardContinuous A J K).Monoidal :=
  letI := Sheaf.monoidalCategory K A
  letI := Sheaf.monoidalCategory J A
  letI : Localization.Lifting (presheafToSheaf K A) K.W
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op ⋙ presheafToSheaf J A)
      (G.sheafPushforwardContinuous A J K) :=
    G.sheafPushforwardContinuousLifting
  Localization.Monoidal.functorMonoidalOfComp
    (presheafToSheaf K A) K.W (G.sheafPushforwardContinuous A J K)
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op ⋙ presheafToSheaf J A)

end CategoryTheory.Functor
