module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/- Lemma 38.32.4: for a quasi-compact quasi-separated scheme `S`, the open-part functor
identifies compactifiable schemes over `S` with compactifications localized at the morphisms
inducing isomorphisms on their open parts. -/
@[stacks 0ATW] #check
  (AlgebraicGeometry.Scheme.Compactification.toCompactifiableIsLocalization :
    ∀ (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S],
      (toCompactifiable S).IsLocalization (interiorIsomorphisms S))

end AlgebraicGeometry.Scheme.Compactification
