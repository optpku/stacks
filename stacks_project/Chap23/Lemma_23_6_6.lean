module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.Homology.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

section

variable {R : Type u} [CommRing R]
variable {A B : DividedPowerChainAlgebra.{u, v} R}
variable (f : A ⟶ B)
variable (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
variable (hf : f.Surjective)

/- Lemma 23.6.6 (09PK): compatible divided powers descend to a unique target-local structure on
the canonical graded homology algebra along a degreewise-surjective map from a positive-acyclic
source. -/
@[stacks 09PK "unique target-local divided powers on homology"]
#check (DividedPowerChainAlgebra.Hom.existsUnique_descendsToHomology f hA hf :
  ∃! gammaH : NonnegGradedAlgebra.DividedPowers
      B.toChainDGAlgebra.homologyNonnegativePart,
    B.DescendsToHomology gammaH)

end

#check @ChainDGAlgebra.homologyNonnegativePart
#check @ChainDGAlgebra.Hom.homologyHom
#check @DividedPowerChainAlgebra.gammaHomologyClass
#check @DividedPowerChainAlgebra.DescendsToHomology
#check @DividedPowerChainAlgebra.Hom.dividedPowersOnHomology
#check @DividedPowerChainAlgebra.Hom.descendsToHomology_iff_eq
#check @DividedPowerChainAlgebra.Hom.homologyDPAlgebra
#check @DividedPowerChainAlgebra.Hom.dividedPowersOnHomology_eq
#check @DividedPowerChainAlgebra.Hom.homologyDPAlgebra_eq
#check @DividedPowerChainAlgebra.Hom.homologyDPHom
#check @DividedPowerChainAlgebra.Hom.homologyDPHom_id
#check @DividedPowerChainAlgebra.Hom.homologyDPHom_comp
