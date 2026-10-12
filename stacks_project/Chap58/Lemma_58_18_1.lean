/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Pushout
namespace IsAdmissibleSpan

/- Lemma 58.18.1: In More on Morphisms, Situation 37.67.1, finite étale schemes
over an admissible pushout are equivalent to compatible finite étale schemes over
the two components. -/
@[stacks 0EK4] #check
  (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.finiteEtaleBaseChangeIsEquivalence :
    ∀ {S : Scheme.{u}} {Z X Y : Over S} (i : Z ⟶ X) (j : Z ⟶ Y) [IsAdmissibleSpan i j],
      Functor.IsEquivalence
        (Scheme.Pushout.baseChange Scheme.finiteEtaleMorphism i.left j.left))

end IsAdmissibleSpan
end Pushout
end Scheme
end AlgebraicGeometry
