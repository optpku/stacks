module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex.Transitivity
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.CotangentComplex

@[expose] public section

universe u

variable {C1 C2 C3 : Type u} [Category.{u} C1] [Category.{u} C2] [Category.{u} C3]
variable {JC1 : GrothendieckTopology C1} {JC2 : GrothendieckTopology C2}
variable {JC3 : GrothendieckTopology C3}
variable [JC1.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC2.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC3.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JC1.HasSheafCompose (forget RingCat.{u})]
variable [JC2.HasSheafCompose (forget RingCat.{u})]
variable [JC3.HasSheafCompose (forget RingCat.{u})]
variable [JC1.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [JC2.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify JC1 CommRingCat.{u}]
variable [HasWeakSheafify JC2 CommRingCat.{u}]
variable [HasWeakSheafify JC1 AddCommGrpCat.{u}]
variable [HasWeakSheafify JC2 AddCommGrpCat.{u}]
variable [JC1.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JC2.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]
variable {OC1 : Sheaf JC1 CommRingCat.{u}} {OC2 : Sheaf JC2 CommRingCat.{u}}
variable {OC3 : Sheaf JC3 CommRingCat.{u}}

/- Lemma 92.22.3. The canonical cotangent transitivity triangle of composable morphisms
of ringed topoi is distinguished. -/
@[stacks 08V1] #check (RingedSite.ToposHom.transitivityTriangle_distinguished :
  ∀ (f : RingedSite.ToposHom (RingedSite.ofCommRingSheaf JC1 OC1)
      (RingedSite.ofCommRingSheaf JC2 OC2))
    (g : RingedSite.ToposHom (RingedSite.ofCommRingSheaf JC2 OC2)
      (RingedSite.ofCommRingSheaf JC3 OC3)),
    RingedSite.ToposHom.transitivityTriangle f g ∈ distTriang (RingedSiteDerived JC1 OC1))
