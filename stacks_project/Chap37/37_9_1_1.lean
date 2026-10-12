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

variable {C₁ : Type u} [Category.{v} C₁] {C₂ : Type u} [Category.{v} C₂]
variable {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
variable [J₁.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [J₂.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify J₁ AddCommGrpCat.{max u v}]
variable [J₁.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ : Sheaf J₁ CommRingCat.{max u v}} {O₂ : Sheaf J₂ CommRingCat.{max u v}}
variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf J₁ O₁)
  (RingedSite.ofCommRingSheaf J₂ O₂))
variable [(f.base.sheafPushforwardContinuous CommRingCat.{max u v} J₂ J₁).IsRightAdjoint]
variable (F : ringedSiteModuleCategory J₁ O₁)
variable (D : Der[RingedSite.Hom.inverseImageStructureSheafMap f ; F])

/- 37.9.1.1: `D = d[f].postcomp θ.val` for the canonical descent morphism
`θ = relativeDifferentialDesc (RingedSite.Hom.inverseImageStructureSheafMap f) D`. -/
@[stacks 04BV] #check
  ((SheafOfModules.RingedSite.relativeDifferentialDesc_fac
      (RingedSite.Hom.inverseImageStructureSheafMap f) D).symm :
    D = (d[f]).postcomp
      (SheafOfModules.RingedSite.relativeDifferentialDesc
        (RingedSite.Hom.inverseImageStructureSheafMap f) D).val)
