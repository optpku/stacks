module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Limit.Truncation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory.Truncation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 75.5.7: the compatible map from a derived module with quasi-coherent cohomology
to a derived limit of its canonical lower-truncation tower is an isomorphism. -/
@[stacks 08F6] #check
  (AlgebraicGeometry.AlgebraicSpace.lowerTruncationComparison_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : DerivedQCoh X)
      {K : ModuleDerived X} {c : E.obj ⟶ K},
      Lower.Comparison.Exists E.obj c → IsIso c)

end AlgebraicGeometry.AlgebraicSpace
