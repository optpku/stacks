module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- Infer the existing canonical tensor model for this commutative presentation.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
  SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor

/-!
# Tor-amplitude under derived pullback

The canonical derived pullback between commutative ringed-site presentations preserves every
fixed Tor-amplitude interval.  Keeping the commutative presentations in the interface records
which ordinary tensor products are being derived; an arbitrary bundled `RingedSite` does not
retain that compatibility data.
-/

open CategoryTheory
open RingedSite.Hom (ModuleDerived ModuleQis modulePullbackDerived modulePullbackToDerived)

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

section

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(f.modulePushforward.{w}).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{w} f)
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]

/-- Lemma 21.46.5: canonical derived pullback between commutative ringed-site presentations
preserves Tor-amplitude in every fixed interval. -/
@[stacks 08H5]
theorem modulePullbackDerived_hasTorAmplitudeIn
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY)) {a b : ℤ}
    (hE : ModuleDerived.HasTorAmplitudeIn
      (X := RingedSite.ofCommRingSheaf JY OY) E a b) :
    ModuleDerived.HasTorAmplitudeIn (X := RingedSite.ofCommRingSheaf JX OX)
      ((modulePullbackDerived.{w} f).obj E) a b := sorry

/-- Canonical derived pullback between commutative ringed-site presentations preserves finite
Tor dimension. -/
theorem modulePullbackDerived_hasFiniteTorDimension
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY))
    (hE : ModuleDerived.HasFiniteTorDimension
      (X := RingedSite.ofCommRingSheaf JY OY) E) :
    ModuleDerived.HasFiniteTorDimension (X := RingedSite.ofCommRingSheaf JX OX)
      ((modulePullbackDerived.{w} f).obj E) := sorry

end

end RingedSite.Hom
