module

public import stacks_project.Chap91.Situation_91_12_4_Diagram
import StacksCheckRecall

open CategoryTheory

universe u v

/- Situation 91.12.4: let `f : (Sh(C), O) ⟶ (Sh(B), O_B)` be a morphism of
ringed topoi. Consider a commutative diagram of first-order thickenings whose
top row is a short exact sequence of first-order thickenings of `(Sh(C), O)`,
whose bottom row is a short exact sequence of first-order thickenings of
`(Sh(B), O_B)`, each `f'_i` restricts to `f`, each pair `(f, f'_i)` is a
strict morphism of thickenings, and each `f'_i` is flat. Let `F'_2` be an
`O'_2`-module flat over `O_{B'_2}` and set `F = F'_2 ⊗ O`, recorded as
`restrictModule` by extending scalars along `π2`. Let `π : O ⟶ O'_1` be the
canonical splitting `canonicalTrivialization` of the top complex
(Remark 91.10.10). After identifying underlying topoi, this is
`FlatMorphismShortExact`. The named top arrow is `h`, the unnamed top arrow
is `g`, and the unnamed bottom arrows are `base` and `base'`. -/
@[stacks 08VX] #check (@SheafOfModules.RingedSite.FirstOrderThickening.FlatMorphismShortExact :
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
