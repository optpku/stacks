module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.CanonicalMap

/-!
# Canonical comparison maps for a strict first-order thickening square

The canonical constructions and their computation rules are publicly re-exported here.

For a commutative square of first-order thickenings of ring sheaves, the comparison
`f^* J ⊗_O F ⟶ I ⊗_O F ⟶ I F'` is the tensor of `kernelPullbackMap` followed by
`infMap` of the mixed-scalar extension `ofPullback π F'`.
-/

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
variable {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O)
variable [hπ : IsFirstOrderThickening π]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]

#check (SheafOfModules.RingedSite.FirstOrderThickening.instIsIso_extendRestrictUnit_idealMulO' π :
  ∀ {F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'},
    IsIso (extendRestrictUnit π (idealMulO' π F')))

#check (SheafOfModules.RingedSite.FirstOrderThickening.ofPullback π :
  (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') → Extension π)

#check (SheafOfModules.RingedSite.FirstOrderThickening.ofPullback_kernel π :
  ∀ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
    (ofPullback π F').kernel = idealMul π F')

#check (SheafOfModules.RingedSite.FirstOrderThickening.ofPullback_middle π :
  ∀ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
    (ofPullback π F').middle = F')

#check (SheafOfModules.RingedSite.FirstOrderThickening.ofPullback_quot π :
  ∀ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
    (ofPullback π F').quot = (extendScalars (ringSheafMap π)).obj F')

#check (SheafOfModules.RingedSite.FirstOrderThickening.idealMulInfMap π :
  ∀ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
    moduleTensor (ideal π) ((extendScalars (ringSheafMap π)).obj F') ⟶
      idealMul π F')

#check (SheafOfModules.RingedSite.FirstOrderThickening.idealMulInfMap_eq π :
  ∀ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
    idealMulInfMap π F' = infMap hπ.isSquareZero (ofPullback π F'))

variable {OB' OB : Sheaf J CommRingCat.{max u v}} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening τ]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)

#check (SheafOfModules.RingedSite.FirstOrderThickening.sourceIdealTensorMap π f f' hcomm :
  ∀ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
        ((extendScalars (ringSheafMap π)).obj F') ⟶
      moduleTensor (ideal π) ((extendScalars (ringSheafMap π)).obj F'))

#check (SheafOfModules.RingedSite.FirstOrderThickening.sourceIdealTensorMap_eq π f f' hcomm :
  ∀ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
    sourceIdealTensorMap π f f' hcomm F' =
      moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 _))

#check (SheafOfModules.RingedSite.FirstOrderThickening.canonicalMap π f f' hcomm :
  ∀ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
        ((extendScalars (ringSheafMap π)).obj F') ⟶
      idealMul π F')

#check (SheafOfModules.RingedSite.FirstOrderThickening.canonicalMap_eq π f f' hcomm :
  ∀ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
    canonicalMap π f f' hcomm F' =
      sourceIdealTensorMap π f f' hcomm F' ≫ idealMulInfMap π F')

end SheafOfModules.RingedSite.FirstOrderThickening
