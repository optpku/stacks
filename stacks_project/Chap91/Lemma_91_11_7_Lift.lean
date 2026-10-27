/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatLift
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.ChangeOfRings
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
variable {OB' O' O : Sheaf J CommRingCat.{max u v}}

/- Flat lifts store a middle module, its reduction comparison, and relative flatness. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.FlatLift :
  (π : O' ⟶ O) → [IsFirstOrderThickening π] →
    [(restrictScalars (ringSheafMap π)).IsRightAdjoint] →
    (OB' ⟶ O') → ringedSiteModuleCategory.{u, v, max u v, max u v} J O →
      Type (max u v + 1))

end SheafOfModules.RingedSite.FirstOrderThickening
