module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.RelativeDiagram
public import stacks_project.Chap91.Remark_91_10_10_Thickening

open CategoryTheory

universe u v

/- 91.13.1.2: the presentation of a relative first-order thickening diagram on a
single site, retained for statements using a common underlying topos. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.RelativeDiagram :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
    [HasWeakSheafify J CommRingCat.{max u v}]
    [J.WEqualsLocallyBijective CommRingCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{max u v}}
    (πO1 : O1' ⟶ O1) (πB1 : OB1' ⟶ OB1) (πO2 : O2' ⟶ O2) (πB2 : OB2' ⟶ OB2)
    [SheafOfModules.RingedSite.IsFirstOrderThickening πO1]
    [SheafOfModules.RingedSite.IsFirstOrderThickening πB1]
    [SheafOfModules.RingedSite.IsFirstOrderThickening πO2]
    [SheafOfModules.RingedSite.IsFirstOrderThickening πB2], Type (max u v))
