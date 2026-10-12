/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction.Complex
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Complex.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lax monoidal pushforward of complexes on ringed sites

The right adjoint of strong monoidal complex pullback carries the canonical lax monoidal structure.
This is the reusable source of multiplication and unit maps under direct image.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.modulePushforwardComplex

variable {CX : Type uX} [Category.{vX} CX]
variable {CY : Type uY} [Category.{vY} CY]
variable {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(PresheafOfModules.pushforward.{w} f.structureSheafMap.hom).IsRightAdjoint]

/-- Degreewise module pushforward on complexes is canonically lax monoidal as the right adjoint of
strong monoidal complex pullback. -/
@[stacks 0FRE "lax monoidal complex pushforward", implicit_reducible]
noncomputable instance laxMonoidal : f.modulePushforwardComplex.{w}.LaxMonoidal :=
  (RingedSite.Hom.modulePullbackPushforwardComplexAdjunction.{w} f).rightAdjointLaxMonoidal

/-- The canonical complex pullback-pushforward adjunction is compatible with its monoidal and lax
monoidal structures. -/
@[stacks 0FRE "monoidal complex adjunction", instance]
theorem adjunctionIsMonoidal :
    (RingedSite.Hom.modulePullbackPushforwardComplexAdjunction.{w} f).IsMonoidal := sorry

#synth f.modulePushforwardComplex.{w}.LaxMonoidal

end RingedSite.Hom.modulePushforwardComplex
