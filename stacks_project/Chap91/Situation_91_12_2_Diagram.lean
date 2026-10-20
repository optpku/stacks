module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatMorphismSquare

open CategoryTheory

universe u v

/- The explicit square of strict flat morphisms of first-order thickenings. -/
#check (@SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismSquare :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
    [HasWeakSheafify J CommRingCat.{max u v}]
    [J.WEqualsLocallyBijective CommRingCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {O O_B O1' O2' OB1' OB2' : Sheaf J CommRingCat.{max u v}}
    (f : O_B ⟶ O) (π1 : O1' ⟶ O) (π2 : O2' ⟶ O)
    (τ1 : OB1' ⟶ O_B) (τ2 : OB2' ⟶ O_B)
    [SheafOfModules.RingedSite.IsFirstOrderThickening π1]
    [SheafOfModules.RingedSite.IsFirstOrderThickening π2]
    [SheafOfModules.RingedSite.IsFirstOrderThickening τ1]
    [SheafOfModules.RingedSite.IsFirstOrderThickening τ2]
    [(SheafOfModules.restrictScalars (SheafOfModules.RingedSite.ringSheafMap f)).IsRightAdjoint],
    Type (max u v + 1))
