module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Unbounded derived pullback

The reusable API is stated for bundled morphisms of commutative ringed sites.  This is the
site-presented specialization currently supported by ReasLib; the source's presentation-
independent statement for arbitrary morphisms of ringed topoi requires a future ringed-topos
module-pullback layer.
-/

/- Lemma 21.18.2 (06YY), site-presented commutative form: module pullback admits an unbounded
total left derived functor.  It is exact, is computed by ordinary pullback on K-flat complexes
with flat terms, and in particular on bounded-above complexes with flat terms. -/
@[stacks 06YY]
#check @RingedSite.Hom.modulePullbackToDerived.hasLeftDerived

#check @RingedSite.Hom.modulePullbackDerived.isTriangulated
#check @RingedSite.Hom.modulePullbackDerived.KFlat.objIso
#check @RingedSite.Hom.modulePullbackToDerived.isInvertedBy
#check @RingedSite.Hom.modulePullbackToDerived.computesAt
