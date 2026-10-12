/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.Faithful

@[expose] public section

open CategoryTheory

universe u

/- Lemma 41.20.1: if `f : X ⟶ S` is surjective, then the canonical functor from schemes
étale over `S` to singleton étale descent data relative to `f` is faithful. -/
@[stacks 0BTJ] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor.faithful_of_surjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Surjective f],
      (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor f).Faithful)
