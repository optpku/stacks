/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.DifferentialGraded.Algebra.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Remark 24.12.2

Pullback and pushforward of differential graded algebras along an arbitrary morphism of ringed
topoi, together with the induced Hom equivalence.
-/

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

universe uX vX uY vY w

variable {CX : Type uX} [Category.{vX} CX]
variable {CY : Type uY} [Category.{vY} CY]
variable {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JX.HasSheafCompose (forget RingCat.{w})]
variable [JY.HasSheafCompose (forget RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable (f : RingedSite.ToposHom
  (RingedSite.ofCommRingSheaf JX OX) (RingedSite.ofCommRingSheaf JY OY))
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

/- Remark 24.12.2 (1): direct image sends a differential graded algebra to a differential graded
algebra on the target ringed topos. -/
@[stacks 0FRG]
#check (RingedSite.ToposHom.pushforwardDGA.{uX, vX, uY, vY, w} f : DGA(OX) ⥤ DGA(OY))

/- Remark 24.12.2 (2): inverse image sends a differential graded algebra to a differential graded
algebra on the source ringed topos. -/
@[stacks 0FRG]
#check (RingedSite.ToposHom.pullbackDGA.{uX, vX, uY, vY, w} f : DGA(OY) ⥤ DGA(OX))

/- Remark 24.12.2 (3): inverse image is left adjoint to direct image on differential graded
algebras, expressed by the induced Hom equivalence. -/
@[stacks 0FRG]
#check (RingedSite.ToposHom.pullbackDGAHomEquiv f :
  (B : DGA(OY)) → (A : DGA(OX)) →
    (f.pullbackDGA.obj B ⟶ A) ≃ (B ⟶ f.pushforwardDGA.obj A))
