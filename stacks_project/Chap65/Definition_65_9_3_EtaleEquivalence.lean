/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.PreRelation.IsEtaleEquivalenceRelation :
  {S : AlgebraicGeometry.Scheme.{u}} → {U : CategoryTheory.Over S} →
    AlgebraicGeometry.Scheme.PreRelation U → Prop)
