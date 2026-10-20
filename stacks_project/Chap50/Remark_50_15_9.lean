module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole.EtaleLocal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.DeRham.LogPole

universe u

/- Remark 50.15.9: if `S` is locally Noetherian, `X` is locally of finite type over `S`,
`Y ⊂ X` is an effective Cartier divisor, and every point of `Y` admits a diagram of
`S`-schemes `X ← U → V` with `φ` étale and the restriction of `ψ` to `φ⁻¹(Y)` étale,
then the relative de Rham complex of logarithmic poles along `Y` is defined. -/
@[stacks 0FN0] #check (AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined.ofEtaleLocal :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
      [IsLocallyNoetherian S] [LocallyOfFiniteType f] [IsEffectiveCartierDivisor i],
      (∀ y : Y,
        ∃ (U V : Scheme.{u}) (φ : U ⟶ X) (ψ : U ⟶ V) (g : V ⟶ S) (u : U),
          Etale φ ∧ φ ≫ f = ψ ≫ g ∧ φ u = i y ∧
            Etale (pullback.fst φ i ≫ ψ)) →
      IsDefined f i)
