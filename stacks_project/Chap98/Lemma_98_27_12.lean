module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.RimSchlessinger
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.TangentSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 98.27.12: In the standing contraction situation, the functor of
compatible triples satisfies the Rim-Schlessinger condition. -/
@[stacks 0GI6] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.hasRimSchlessinger :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
      (σ : AlgebraicGeometry.AlgebraicSpace.ContractionSituation S),
      AlgebraicGeometry.Scheme.Over.HasRimSchlessinger σ.functor)
