/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped RelativeDerivation RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf JC CommRingCat.{max u v}} {O' : Sheaf JD CommRingCat.{max u v}}
variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC O)
  (RingedSite.ofCommRingSheaf JD O'))
variable [(f.base.sheafPushforwardContinuous CommRingCat.{max u v} JD JC).IsRightAdjoint]

/- Definition 18.33.10 (04BQ): relative differentials of a ringed-site morphism are the generic
relative differentials of its inverse-image structure-sheaf map. -/
@[stacks 04BQ]
#check (relativeDifferentials f : ringedSiteModuleCategory JC O)

/- The globally scoped notation exposes the same canonical module and universal derivation. -/
#check (Ω[f] : ringedSiteModuleCategory JC O)
#check (d[f] : Der[inverseImageStructureSheafMap f ; Ω[f]])

end RingedSite.Hom
