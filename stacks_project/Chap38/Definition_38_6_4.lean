/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.Devissage.CompleteAt

universe u

/- Definition 38.6.4: A complete dévissage at `q` is a complete dévissage over `r`
together with its uniquely determined lifted primes, contraction chain, purely transcendental
residue-field extensions, and relative-dimension equalities. -/
@[stacks 05HZ] #check (Module.Devissage.CompleteAt :
  (R : Type u) → [CommRing R] → (S : FGAlgCat.{u} R) →
    (N : FGModuleCat.{u} S.obj) → (r : PrimeSpectrum R) →
      (q : PrimeSpectrum S.obj) →
        r.asIdeal = q.asIdeal.comap (algebraMap R S.obj) → Type (u + 1))
