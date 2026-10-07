module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Differentials
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 37.9.9: if both horizontal morphisms in a commutative square of schemes are étale,
then the canonical pullback comparison on relative differentials is an isomorphism. -/
@[stacks 04BX] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.comparison_isIso_of_etale :
    ∀ {X₁ X₂ S₁ S₂ : Scheme.{u}}
      {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁}
      {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂}
      (sq : CommSq f p₂ p₁ g) [Etale f] [Etale g],
      IsIso
        (RingedSpace.Hom.Differentials.comparison
          (sq.map
            (Scheme.forgetToLocallyRingedSpace ⋙
              LocallyRingedSpace.forgetToSheafedSpace))))
