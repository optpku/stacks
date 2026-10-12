/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Cartesian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation.Hom

/- Lemma 39.20.7: a cartesian morphism of equivalence relations induces a pullback square
between the represented object sheaves and their quotient sheaves for each standard
topology. -/
@[stacks 07S3]
#check (AlgebraicGeometry.Scheme.PreRelation.Hom.quotientSquare_isPullback :
  ∀ {S : Scheme.{u}} (tau : StandardTopology) {U U' : Over S}
    {P : PreRelation U} {Q : PreRelation U'}
    [IsEquivalenceRelation P.t P.s] [IsEquivalenceRelation Q.t Q.s]
    (f : Hom P Q) (_ : f.IsCartesian),
    IsPullback (P.quotientMap (tau.overTopology S))
      ((tau.overTopology S).uliftYoneda.{u + 1}.map f.obj)
      (f.quotientSheafMap (tau.overTopology S))
      (Q.quotientMap (tau.overTopology S)))

end AlgebraicGeometry.Scheme.PreRelation.Hom
