/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.Sheafification
import StacksCheckRecall

/-!
# Lemma 18.33.4 compatibility entry point

Compatibility of relative differentials with commutative-ring and module
sheafification is owned by the neutral ReasLib API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.RelativeDifferentials.Sheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}} (phi : O₁ ⟶ O₂)

/- Lemma 18.33.4 (08TP): the canonical comparison from the module
sheafification of sectionwise relative differentials to the relative
differentials of the sheafified ring map is invertible. -/
@[stacks 08TP]
#check (inferInstance : IsIso (comparison J phi))

/- The reusable owner exposes the canonical comparison morphism itself. -/
#check (comparison J phi : ofPresheaf J phi ⟶ afterSheafification J phi)

end SheafOfModules.RingedSite.RelativeDifferentials.Sheafification
