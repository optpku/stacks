module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.FppfDescent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
universe u

/- Lemma 59.100.4 -/
@[stacks 0DEU] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.fppfSmallIsoCommaFunctor_isEquivalence :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology (Type (u + 1))]
      [HasSheafify Y.smallEtaleTopology (Type (u + 1))]
      [Flat f] [LocallyOfFinitePresentation f] [Surjective f],
      (AlgebraicGeometry.Scheme.Etale.SmallToBig.fppfSmallIsoCommaFunctor f).IsEquivalence)

end
