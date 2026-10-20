/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.MapObstruction
import StacksCheckRecall

/-!
# Obstruction to lifting a map along a strict first-order thickening

The canonical Ext class for a map between the reductions of two flat modules
detects lifts. Its coefficient `f^* J ⊗ i^* G'` is canonically identified with
the source's `i^* G' ⊗ f^* J` by the symmetry of the tensor product.
-/

@[expose] public section

open CategoryTheory
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
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable {π : O' ⟶ O} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)
variable (F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
variable (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
    (extendScalars (ringSheafMap π)).obj G')
variable [IsFlat OB' ((restrictionAlong f').obj F')]
variable [IsFlat OB' ((restrictionAlong f').obj G')]
variable [HasExt (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
variable (hstrict : IsStrict f f' hcomm)

/- Lemma 91.11.6: Let `(f, f')` be a strict morphism of first-order thickenings and let
`φ` be a map between the reductions of two modules flat over the thickened base. The canonical
class `obstruction π f f' hcomm hstrict φ` in `Ext (i^* F') (f^* J ⊗ i^* G') 1` vanishes
exactly when `φ` lifts to an `O'`-linear map `F' ⟶ G'`.
-/
@[stacks 08MT] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.obstruction_eq_zero_iff π f f' hcomm
      (F' := F') (G' := G') hstrict φ :
    obstruction π f f' hcomm hstrict φ = 0 ↔ Nonempty (Lift F' G' φ))

end SheafOfModules.RingedSite.FirstOrderThickening
