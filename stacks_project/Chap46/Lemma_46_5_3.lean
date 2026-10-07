module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEquivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace SheafOfModules

/- Lemma 46.5.3 -/
@[stacks 06ZJ] #check (SheafOfModules.affineEvaluationAdequateIsEquivalence :
  ∀ (τ : StandardTopology) (A : CommRingCat.{u}),
    (SheafOfModules.affineEvaluationAdequate τ A).IsEquivalence)

end SheafOfModules
