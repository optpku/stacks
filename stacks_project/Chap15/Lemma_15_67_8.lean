/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Termwise

/-!
# Lemma 15.67.8

@stack 066H

The source result is represented by the canonical bounded cochain-complex owner.  The current
derived tensor facade gives the commutative-ring specialization of the source's ring statement.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

/- Lemma 15.67.8 (066H) (1): bounded termwise Tor-amplitude. -/
@[stacks 066H "bounded termwise Tor amplitude"]
#check fun {R : Type u} [CommRing R] (a b : ℤ)
    (K : CochainComplex.Bounded (ModuleCat R))
    (hterm : ∀ i : ℤ, DerivedCategory.HasTorAmplitudeIn R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (K.obj.X i)) (a - i) (b - i)) ↦
  (DerivedCategory.HasTorAmplitudeIn.of_bounded_of_termwise a b K hterm :
    DerivedCategory.HasTorAmplitudeIn R (DerivedCategory.Q.obj K.obj) a b)

/- Lemma 15.67.8 (066H) (2): the finite-Tor-dimension consequence. -/
@[stacks 066H "bounded termwise finite Tor dimension"]
#check fun {R : Type u} [CommRing R] (K : CochainComplex.Bounded (ModuleCat R))
    (hfinite : ∀ i : ℤ, ModuleCat.HasFiniteTorDimension R (K.obj.X i)) ↦
  (DerivedCategory.HasFiniteTorDimension.of_bounded_of_termwise R K.obj K.property hfinite :
    DerivedCategory.HasFiniteTorDimension R (DerivedCategory.Q.obj K.obj))

#check @DerivedCategory.HasTorAmplitudeIn.of_isZero
