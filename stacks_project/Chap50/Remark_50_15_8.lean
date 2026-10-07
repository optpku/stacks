module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole.CompletionSplit

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Remark 50.15.8: if `S` is locally Noetherian, `X` is locally of finite type over `S`,
`Y ⊂ X` is an effective Cartier divisor, and the completed stalk map
`𝒪_{X,y}^∧ ⟶ 𝒪_{Y,y}^∧` has a section for every `y : Y`, then the de Rham complex of log
poles is defined for `Y ⊂ X` over `S`. -/
@[stacks 0FMZ]
#check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined.of_completion_split :
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [IsEffectiveCartierDivisor i],
    (∀ y : Y, IsSplitEpi (CommRingCat.ofHom (AdicCompletion.mapLocal (i.stalkMap y).hom))) →
      AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined f i)
