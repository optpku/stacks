module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.FiniteType

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Pushout
namespace IsAdmissibleSpan

/- Lemma 37.67.5: the canonical structure morphism from the pushout of an admissible
span is locally of finite type over a locally Noetherian base when each object in the
span is locally of finite type over the base. -/
@[stacks 0E27]
#check (AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.instToBaseLocallyOfFiniteType :
  ∀ {S : Scheme.{u}} {Z X Y : Over S} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsAdmissibleSpan i j] [IsLocallyNoetherian S]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom], LocallyOfFiniteType (toBase i j))

end IsAdmissibleSpan
end Pushout
end Scheme
end AlgebraicGeometry
