/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatLift.IsoClass
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace FlatLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {OB' O' O : Sheaf J CommRingCat.{max u v}}
variable (π : O' ⟶ O)
variable [hπ : IsFirstOrderThickening π]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f' : OB' ⟶ O')
variable (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O)

/- Flat-lift isomorphism classes use compatible isomorphisms of middle modules. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.FlatLift.IsoClass π f' F :
  Type (max u v + 1))

end FlatLift
end SheafOfModules.RingedSite.FirstOrderThickening
