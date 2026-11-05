/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.Devissage.CompleteAt

universe u

/- Definition 38.6.4: A complete dévissage at `q` is a complete dévissage over `r`
together with its uniquely determined lifted primes, contraction chain, purely transcendental
residue-field extensions, and relative-dimension equalities in the actual residue-field fibers. -/
@[stacks 05HZ] #check (Module.Devissage.CompleteAt :
  (R : Type u) → [CommRing R] → (S : FGAlgCat.{u} R) →
    (N : FGModuleCat.{u} S.obj) → (r : PrimeSpectrum R) →
      (q : PrimeSpectrum S.obj) →
        r.asIdeal = q.asIdeal.comap (algebraMap R S.obj) → Type (u + 1))

/- The distinguished support point is a point of the residue-field fiber, rather than of
`Spec Bᵢ`; the relative dimension on the left remains the global relative dimension. -/
#check @Module.Devissage.Stage.residueBaseChange
#check @Module.Devissage.CompleteAt.supportPoint
#check @Module.Devissage.CompleteAt.supportPoint_comap
#check @Module.Devissage.CompleteAt.dimension_spec
