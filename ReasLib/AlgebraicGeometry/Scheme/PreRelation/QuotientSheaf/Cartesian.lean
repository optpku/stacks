/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Functoriality
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.LocalSurjectivity

/-!
# Cartesian morphisms and quotient sheaves

This module records the pullback property of quotient sheaves induced by cartesian morphisms
of equivalence relations on schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation.Hom

/-- A cartesian morphism of equivalence relations induces a pullback square from the
represented object sheaves to their quotient sheaves for every standard topology. -/
theorem quotientSquare_isPullback {S : Scheme.{u}} (tau : StandardTopology)
    {U U' : Over S} {P : PreRelation U} {Q : PreRelation U'}
    [IsEquivalenceRelation P.t P.s] [IsEquivalenceRelation Q.t Q.s]
    (f : Hom P Q) (hf : f.IsCartesian) :
    IsPullback (P.quotientMap (tau.overTopology S))
      ((tau.overTopology S).uliftYoneda.{u + 1}.map f.obj)
      (f.quotientSheafMap (tau.overTopology S))
      (Q.quotientMap (tau.overTopology S)) := sorry

end AlgebraicGeometry.Scheme.PreRelation.Hom
