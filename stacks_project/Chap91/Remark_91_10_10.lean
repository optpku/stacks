module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening
import StacksCheckRecall

open CategoryTheory
open SheafOfModules.RingedSite


universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}] [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}}
variable {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {π₃ : O'₃ ⟶ O}
variable [IsFirstOrderThickening π₁] [IsFirstOrderThickening π₂] [IsFirstOrderThickening π₃]

-- After Stacks 08M6 identifies underlying topoi, morphisms of first-order thickenings of a
-- ringed topos are morphisms of same-site projections `πᵢ : O'ᵢ ⟶ O`. The pre-identification
-- packaging is `RingedSite.ToposHom.CommSquare` from 91.9.1.1.

/- Remark 91.10.10 (1): a sequence of morphisms of first-order thickenings of `(Sh(C), O)` is a
complex when the induced `O`-module maps of ideal sheaves `I₃ ⟶ I₂ ⟶ I₁` compose to zero. -/
@[stacks 08ML] #check (SheafOfModules.RingedSite.FirstOrderThickening.IsComplex :
  SheafOfModules.RingedSite.FirstOrderThickening.Hom π₁ π₂ →
    SheafOfModules.RingedSite.FirstOrderThickening.Hom π₂ π₃ → Prop)

/- Remark 91.10.10 (2): if the sequence is a complex, the composite `(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)`
factors uniquely through `(Sh(C), O) ⟶ (Sh(D₃), O'₃)`, so the first-order thickening
`(Sh(D₁), O'₁)` is trivial and comes with a unique canonical trivialization `σ : O ⟶ O'₁`. -/
@[stacks 08ML] #check (SheafOfModules.RingedSite.FirstOrderThickening.existsUnique_canonicalTrivialization :
  (f : SheafOfModules.RingedSite.FirstOrderThickening.Hom π₁ π₂) →
    (g : SheafOfModules.RingedSite.FirstOrderThickening.Hom π₂ π₃) →
    SheafOfModules.RingedSite.FirstOrderThickening.IsComplex f g →
    ∃! σ : O ⟶ O'₁, SheafOfModules.RingedSite.FirstOrderThickening.IsTrivialization σ π₁ ∧
      g.hom ≫ f.hom = π₃ ≫ σ)

/- Remark 91.10.10 (3): a sequence of morphisms of first-order thickenings of `(Sh(C), O)` is a
short exact sequence when `0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` is a short exact sequence of `O`-modules. -/
@[stacks 08ML] #check (SheafOfModules.RingedSite.FirstOrderThickening.IsShortExact :
  SheafOfModules.RingedSite.FirstOrderThickening.Hom π₁ π₂ →
    SheafOfModules.RingedSite.FirstOrderThickening.Hom π₂ π₃ → Prop)

end
