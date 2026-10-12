/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.FullyFaithful

@[expose] public section

open CategoryTheory

universe u

/- Lemma 41.20.3 (1): If `f : X ⟶ S` is surjective and universally closed, then the
canonical functor to étale descent data relative to `f` is fully faithful. This applies in
particular when `f` is finite, integral, or proper. -/
@[stacks 0BTL] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor.fullyFaithful_of_surjective_universallyClosed :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.UniversallyClosed f],
      Nonempty
        (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor f).FullyFaithful)

/- Lemma 41.20.3 (2): If `f : X ⟶ S` is surjective and universally open, then the
canonical functor to étale descent data relative to `f` is fully faithful. This applies in
particular when `f` is flat and locally of finite presentation, smooth, or étale. -/
@[stacks 0BTL] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor.fullyFaithful_of_surjective_universallyOpen :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.UniversallyOpen f],
      Nonempty
        (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor f).FullyFaithful)

/- Lemma 41.20.3 (3): If `f : X ⟶ S` is surjective, quasi-compact, and flat, then the
canonical functor to étale descent data relative to `f` is fully faithful. -/
@[stacks 0BTL] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor.fullyFaithful_of_surjective_quasiCompact_flat :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.QuasiCompact f]
      [AlgebraicGeometry.Flat f],
      Nonempty
        (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor f).FullyFaithful)
