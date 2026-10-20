module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.ValuativeCriterion.DVR
import StacksCheckRecall

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.22.1: A separated finite-type morphism to a locally Noetherian
algebraic space is proper if DVR valuative squares factoring generically through
a dense finite-type morphism admit lifts over the original DVR. -/
@[stacks 0CMD] #check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Along.proper_of_separated :
    ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (h : U ⟶ X)
      [IsLocallyNoetherian Y] [FiniteType f] [FiniteType h] [Separated f] [Dominant h],
      ValuativeCriterion.DVR.Along.Existence h f → Proper f)
