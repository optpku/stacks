/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.IdealPowerTorsion
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.23.7 (1): for a Noetherian scheme and an ideal sheaf, a coherent formal module
uniformly annihilated by a positive ideal power is in the essential image of completion. -/
@[stacks 0EHP] #check
  (Scheme.CoherentCompletion.mem_essImage_of_isAnnihilatedByIdealPowerOnAffineOpens :
    ∀ {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
      (E : Scheme.CoherentFormalModules X I),
      Scheme.CoherentFormalModules.IsAnnihilatedByIdealPowerOnAffineOpens I E →
        (Scheme.CoherentCompletion.functor I).essImage E)

/- Lemma 30.23.7 (2): completion preserves Hom when either coherent module is uniformly
annihilated by a positive ideal power. -/
@[stacks 0EHP] #check
  (Scheme.CoherentCompletion.homMap_bijective_of_isAnnihilatedByIdealPowerOnAffineOpens :
    ∀ {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
      (F G : RingedSpace.Coh X.toRingedSpace),
      (Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I F.obj ∨
        Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I G.obj) →
      Function.Bijective (fun f : F ⟶ G ↦ (Scheme.CoherentCompletion.functor I).map f))

/- Lemma 30.23.7 (3): completion preserves degree-one Ext when either coherent module is
uniformly annihilated by a positive ideal power. -/
@[stacks 0EHP] #check
  (Scheme.CoherentCompletion.extOneMap_bijective_of_isAnnihilatedByIdealPowerOnAffineOpens :
    ∀ {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
      [HasExt (RingedSpace.Coh X.toRingedSpace)]
      [HasExt (Scheme.CoherentFormalModules X I)]
      (F G : RingedSpace.Coh X.toRingedSpace),
      (Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I F.obj ∨
        Scheme.Modules.IsAnnihilatedByIdealPowerOnAffineOpens I G.obj) →
      Function.Bijective (Scheme.CoherentCompletion.extOneMap (I := I) F G))
