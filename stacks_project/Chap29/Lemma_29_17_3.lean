module

import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Stalk
import StacksCheckRecall

universe u

/- Lemma 29.17.3: For a locally Noetherian scheme, universal catenarity is equivalent to
universal catenarity of every stalk ring. -/
@[stacks 02JA] #check
  (AlgebraicGeometry.UniversallyCatenary.iff_forall_stalk :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian S],
      AlgebraicGeometry.UniversallyCatenary S ↔
        ∀ s : S, UniversallyCatenaryRing.{u, u} (S.presheaf.stalk s))
