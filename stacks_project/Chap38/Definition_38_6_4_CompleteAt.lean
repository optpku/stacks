/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Devissage.CompleteAt

@[expose] public section

universe u

/- The shared complete dévissage-at-a-prime structure has the expected dependent type. -/
#check (Module.Devissage.CompleteAt :
  (R : Type u) → [CommRing R] → (S : FGAlgCat.{u} R) →
    (N : FGModuleCat.{u} S.obj) → (r : PrimeSpectrum R) →
      (q : PrimeSpectrum S.obj) →
        r.asIdeal = q.asIdeal.comap (algebraMap R S.obj) → Type (u + 1))
