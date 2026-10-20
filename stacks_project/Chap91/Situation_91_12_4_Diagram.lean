module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatMorphismShortExact

open CategoryTheory

universe u v

/- The three-column flat short exact diagram of first-order thickenings. -/
#check (@SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
    [HasWeakSheafify J CommRingCat.{max u v}]
    [J.WEqualsLocallyBijective CommRingCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {O O_B O1' O2' O3' OB1' OB2' OB3' : Sheaf J CommRingCat.{max u v}}
    (f : O_B ⟶ O) (π1 : O1' ⟶ O) (π2 : O2' ⟶ O) (π3 : O3' ⟶ O)
    (τ1 : OB1' ⟶ O_B) (τ2 : OB2' ⟶ O_B) (τ3 : OB3' ⟶ O_B)
    [SheafOfModules.RingedSite.IsFirstOrderThickening π1]
    [SheafOfModules.RingedSite.IsFirstOrderThickening π2]
    [SheafOfModules.RingedSite.IsFirstOrderThickening π3]
    [SheafOfModules.RingedSite.IsFirstOrderThickening τ1]
    [SheafOfModules.RingedSite.IsFirstOrderThickening τ2]
    [SheafOfModules.RingedSite.IsFirstOrderThickening τ3]
    [(SheafOfModules.restrictScalars (SheafOfModules.RingedSite.ringSheafMap f)).IsRightAdjoint]
    [(SheafOfModules.restrictScalars (SheafOfModules.RingedSite.ringSheafMap π2)).IsRightAdjoint],
    Type (max u v + 1))

section

open SheafOfModules SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O O_B O1' O2' O3' OB1' OB2' OB3' : Sheaf J CommRingCat.{max u v}}
variable {f : O_B ⟶ O} {π1 : O1' ⟶ O} {π2 : O2' ⟶ O} {π3 : O3' ⟶ O}
variable {τ1 : OB1' ⟶ O_B} {τ2 : OB2' ⟶ O_B} {τ3 : OB3' ⟶ O_B}
variable [IsFirstOrderThickening π1] [IsFirstOrderThickening π2]
variable [IsFirstOrderThickening π3]
variable [IsFirstOrderThickening τ1] [IsFirstOrderThickening τ2]
variable [IsFirstOrderThickening τ3]
variable [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable [(restrictScalars (ringSheafMap π2)).IsRightAdjoint]

#check (SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact.restrictModule :
  FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3 →
    ringedSiteModuleCategory.{u, v, max u v, max u v} J O)

#check (SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact.canonicalTrivialization :
  FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3 → (O ⟶ O1'))

end
