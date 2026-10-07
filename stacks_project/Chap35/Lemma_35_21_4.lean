module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.RegularLocal
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry

/- Lemma 35.21.4: for an étale morphism `f : U ⟶ V`, the stalk at `u : U` is a regular
local ring if and only if the stalk at `f u` is a regular local ring. -/
@[stacks 0AH7] #check
  (AlgebraicGeometry.Etale.isRegularLocalRing_stalk_iff :
    ∀ {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U),
      IsRegularLocalRing (U.presheaf.stalk u) ↔
        IsRegularLocalRing (V.presheaf.stalk (f u)))

end AlgebraicGeometry
