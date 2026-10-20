/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.InverseImage
import StacksCheckRecall

/-!
# Lemma 18.33.5 compatibility entry point

The continuous-site inverse-image comparison for relative differentials is
owned by the neutral ReasLib differential API.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.RelativeDifferentials

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify K CommRingCat.{max u v}]
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}} (phi : O₁ ⟶ O₂)
variable [(SheafOfModules.pushforward
  (InverseImage.structureMap (J := J) (K := K) F O₂)).IsRightAdjoint]

/- Lemma 18.33.5 (08TQ): the canonical inverse-image comparison for
relative differentials is invertible. -/
@[stacks 08TQ]
#check (inferInstance : IsIso (comparison (J := J) (K := K) F phi))

/- The reusable owner exposes the comparison morphism itself. -/
#check comparison (J := J) (K := K) F phi

end SheafOfModules.RingedSite.RelativeDifferentials
