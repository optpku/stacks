module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.FiniteType
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 29.18.1 (1): a scheme locally of finite type over a Nagata scheme is Nagata. -/
@[stacks 035A] #check
  (AlgebraicGeometry.Scheme.nagata_of_locallyOfFiniteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [Nagata S], Nagata X)

/- Lemma 29.18.1 (2): a scheme locally of finite type over a universally Japanese scheme is
universally Japanese. -/
@[stacks 035A] #check
  (AlgebraicGeometry.Scheme.universallyJapanese_of_locallyOfFiniteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [UniversallyJapanese S],
      UniversallyJapanese X)

end AlgebraicGeometry.Scheme
