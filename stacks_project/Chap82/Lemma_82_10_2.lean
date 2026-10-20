module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Localization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 82.10.2: For a good algebraic space over the fixed base, pushforward
from the reduced closed complement and restriction to an open subspace form
an exact sequence of cycle groups, surjective onto the cycles of the open. -/
@[stacks 0EP9] #check (AlgebraicGeometry.AlgebraicSpace.Hom.Localization.exact :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (U : OpenSubspace X) (k : ℤ),
    (AlgebraicGeometry.AlgebraicSpace.Hom.Localization.complex f δ U k).Exact ∧
      Epi (AlgebraicGeometry.AlgebraicSpace.Hom.Localization.complex f δ U k).g)
