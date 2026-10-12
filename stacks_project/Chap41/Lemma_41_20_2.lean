/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.FullyFaithful

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 41.20.2: if `f : X ⟶ S` is submersive and every étale base change is submersive,
then the canonical functor to étale descent data relative to `f` is fully faithful. -/
@[stacks 0BTK] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor.fullyFaithful_of_submersive_etaleBaseChange :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Submersive f],
      (∀ U : S.Etale, AlgebraicGeometry.Submersive (pullback.snd f U.hom)) →
        Nonempty
          (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor f).FullyFaithful)
