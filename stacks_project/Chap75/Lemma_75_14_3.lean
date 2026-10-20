module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward
import StacksCheckRecall

universe u

/- Lemma 75.14.3: Let `S` be a scheme. Let `(U ⊂ X, j : V → X)` be an elementary
distinguished square of algebraic space over `S`. Let `E` be a perfect object of
`D(𝒪_V)` supported on `j⁻¹(T)` where `T = |X| \ |U|`. Then `Rj_*E` is a perfect object
of `D(𝒪_X)`. -/
@[stacks 08HK] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect.pushforwardDerived_of_isSupportedOn :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {U V X : AlgebraicGeometry.AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
      [AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare j f]
      {E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived V},
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect E →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsSupportedOn E
        (AlgebraicGeometry.AlgebraicSpace.Points.map f ⁻¹'
          (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.toOpenSubspace j f).pointsSetᶜ) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect
        ((AlgebraicGeometry.AlgebraicSpace.Modules.moduleDerivedPushforward f).obj E))
