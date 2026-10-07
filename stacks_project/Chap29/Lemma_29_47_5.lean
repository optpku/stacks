module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Seminormal

universe u

/- Lemma 29.47.5 (1): a seminormal ring is reduced. -/
@[stacks 0EUQ] #check (isReduced_of_seminormalRing :
  ∀ (A : Type u) [CommRing A] [SeminormalRing A], IsReduced A)

/- Lemma 29.47.5 (2): an absolutely weakly normal ring is reduced. -/
@[stacks 0EUQ] #check (isReduced_of_absolutelyWeaklyNormalRing :
  ∀ (A : Type u) [CommRing A] [AbsolutelyWeaklyNormalRing A], IsReduced A)

/- Lemma 29.47.5 (3): a seminormal scheme is reduced. -/
@[stacks 0EUQ] #check (AlgebraicGeometry.Scheme.isReduced_of_seminormal :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.Seminormal X],
    AlgebraicGeometry.IsReduced X)

/- Lemma 29.47.5 (4): an absolutely weakly normal scheme is reduced. -/
@[stacks 0EUQ] #check (AlgebraicGeometry.Scheme.isReduced_of_absolutelyWeaklyNormal :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal X],
    AlgebraicGeometry.IsReduced X)
