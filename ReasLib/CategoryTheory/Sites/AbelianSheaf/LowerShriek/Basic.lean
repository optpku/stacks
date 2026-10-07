module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf

/-!
# Lower shriek for sheaves of abelian groups

The basic construction is already canonical in mathlib: on presheaves it is left Kan extension,
and on sheaves it is left Kan extension followed by sheafification. This file is deliberately a
thin, reusable entry point for that API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor.AbelianLowerShriek

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)

section Presheaf

variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]

/- Definition 18.16.1 (04BF): lower shriek on abelian presheaves is left Kan extension. -/

/- Lemma 18.16.2 (04BG): presheaf lower shriek is the canonical left adjoint to restriction. -/

end Presheaf

section Pointwise

variable (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
variable [u.op.HasPointwiseLeftKanExtension P]

/- Definition 18.16.1 (04BF): pointwise lower shriek is computed by a comma-category colimit. -/

end Pointwise

section Sheaf

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K AddCommGrpCat.{w}]

/- Definition 18.16.1 (04BF): lower shriek on abelian sheaves is the sheafified left Kan
extension. -/

/- The chosen mathlib owner of sheaf lower shriek. -/

/- The canonical comparison between the chosen owner and the sheafified Kan-extension
construction. -/

end Sheaf

end CategoryTheory.Functor.AbelianLowerShriek
