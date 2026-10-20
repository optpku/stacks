module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.Pushforward

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig

universe u

/- The small-to-big étale site square is compatible with base change. -/
#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallBigRelocalizationSiteIso :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    smallEtalePullback f ⋙ relocalizationFunctor (𝟙 T) ≅
      relocalizationFunctor (𝟙 S) ⋙ Over.pullback f)

end
