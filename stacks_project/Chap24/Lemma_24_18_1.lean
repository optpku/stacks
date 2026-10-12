/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.DifferentialGraded.Module.Adjunction
import StacksCheckRecall

/-!
# Lemma 24.18.1

The differential graded module pullback-pushforward adjunction is owned by
`ReasLib.AlgebraicGeometry.RingedSite.DifferentialGraded.Module.Adjunction`.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.DGModule

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
variable {A : DGA(OX)} {B : DGA(OY)}
variable (φ : f.pullbackDGA.obj B ⟶ A) (N : Mod(B, d)) (M : Mod(A, d))

/- Lemma 24.18.1 (0FRU): for `φ : f^*B ⟶ A`, morphisms `N ⟶ f_*M` of DG
`B`-modules correspond canonically to morphisms `f^*N ⟶ M` of DG `A`-modules. -/
@[stacks 0FRU]
#check
  (homEquiv f φ N M :
    (N ⟶ (pushforward f φ).obj M) ≃ ((pullback f φ).obj N ⟶ M))

end RingedSite.Hom.DGModule

end
