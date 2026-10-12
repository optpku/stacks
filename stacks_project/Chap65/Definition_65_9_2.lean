/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 65.9.2: for a scheme `S` and a scheme `U` over `S`, an étale
equivalence relation on `U` over `S` is an equivalence relation `j : R ⟶ U ⨯ U`
whose projections `s, t : R ⟶ U` are étale morphisms of schemes. -/
@[stacks 02WS] #check (AlgebraicGeometry.Scheme.PreRelation.IsEtaleEquivalenceRelation :
  {S : AlgebraicGeometry.Scheme.{u}} → {U : CategoryTheory.Over S} →
    AlgebraicGeometry.Scheme.PreRelation U → Prop)
