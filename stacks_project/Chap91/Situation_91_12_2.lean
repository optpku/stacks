module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.FlatMorphismSquare
public import stacks_project.Chap91.Situation_91_12_2_Diagram
import StacksCheckRecall

open CategoryTheory RingedSite

universe uC vC uB vB uC1 vC1 uC2 vC2 uB1 vB1 uB2 vB2 w

variable {C : Type uC} [Category.{vC} C]
variable {B : Type uB} [Category.{vB} B]
variable {C1 : Type uC1} [Category.{vC1} C1]
variable {C2 : Type uC2} [Category.{vC2} C2]
variable {B1 : Type uB1} [Category.{vB1} B1]
variable {B2 : Type uB2} [Category.{vB2} B2]
variable {JC : GrothendieckTopology C}
variable {JB : GrothendieckTopology B}
variable {JC1 : GrothendieckTopology C1}
variable {JC2 : GrothendieckTopology C2}
variable {JB1 : GrothendieckTopology B1}
variable {JB2 : GrothendieckTopology B2}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC1.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC2.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB1.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB2.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC.HasSheafCompose (forget RingCat.{w})]
variable [JB.HasSheafCompose (forget RingCat.{w})]
variable [JC1.HasSheafCompose (forget RingCat.{w})]
variable [JC2.HasSheafCompose (forget RingCat.{w})]
variable [JB1.HasSheafCompose (forget RingCat.{w})]
variable [JB2.HasSheafCompose (forget RingCat.{w})]
variable [JC.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JB.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JC1.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JC2.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JB1.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JB2.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JC1 AddCommGrpCat.{w}]
variable [JC1.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify JC2 AddCommGrpCat.{w}]
variable [JC2.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify JB1 AddCommGrpCat.{w}]
variable [JB1.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify JB2 AddCommGrpCat.{w}]
variable [JB2.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf JC CommRingCat.{w}}
variable {O_B : Sheaf JB CommRingCat.{w}}
variable {O1' : Sheaf JC1 CommRingCat.{w}}
variable {O2' : Sheaf JC2 CommRingCat.{w}}
variable {OB1' : Sheaf JB1 CommRingCat.{w}}
variable {OB2' : Sheaf JB2 CommRingCat.{w}}

/- Situation 91.12.2: let `f : (Sh(C), O) ⟶ (Sh(B), O_B)` be a morphism of
ringed topoi. Consider a commutative square of first-order thickenings whose
top arrow `h` is a morphism of first-order thickenings of `(Sh(C), O)`, whose
bottom arrow is a morphism of first-order thickenings of `(Sh(B), O_B)`, each
`f'_i` restricts to `f`, both pairs `(f, f'_i)` are strict morphisms of
thickenings, both `f'_i` are flat, and `F` is an `O`-module flat over `O_B`.
-/
@[stacks 0CYD] #check (RingedSite.ToposHom.Thickening.FlatMorphismSquare :
  ∀
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JB O_B))
    (i1 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC1 O1'))
    (i2 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC2 O2'))
    (t1 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB1 OB1'))
    (t2 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB2 OB2'))
    (f1' : ToposHom (ofCommRingSheaf JC1 O1') (ofCommRingSheaf JB1 OB1'))
    (f2' : ToposHom (ofCommRingSheaf JC2 O2') (ofCommRingSheaf JB2 OB2'))
    [RingedSite.ToposHom.IsFirstOrderThickening i1] [RingedSite.ToposHom.IsFirstOrderThickening i2]
    [RingedSite.ToposHom.IsFirstOrderThickening t1] [RingedSite.ToposHom.IsFirstOrderThickening t2]
    [(SheafOfModules.restrictScalars.{w} f1'.structureMap).IsRightAdjoint]
    [(SheafOfModules.restrictScalars.{w} f2'.structureMap).IsRightAdjoint],
    Type (max uC vC uB vB uC1 vC1 uC2 vC2 uB1 vB1 uB2 vB2 (w + 1)))
