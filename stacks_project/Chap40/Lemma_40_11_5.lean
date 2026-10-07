module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.Range.LocallyClosed

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/- Lemma 40.11.5: in the setup of Situation 40.11.1, if the image of the arrow morphism
is locally closed, then it is closed. -/
@[stacks 04Q9] #check
  (AlgebraicGeometry.GroupoidScheme.Hom.isClosed_range_of_isLocallyClosed :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
      (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
      (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU),
      IsLocallyClosed (Set.range f.arrow.left) → IsClosed (Set.range f.arrow.left))

end AlgebraicGeometry.GroupoidScheme.Hom
