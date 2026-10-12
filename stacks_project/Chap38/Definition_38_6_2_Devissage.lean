/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Devissage.Complete

universe u

#check (Module.Devissage.Complete :
  (R : Type u) → [CommRing R] → (S : FGAlgCat.{u} R) →
    FGModuleCat.{u} S.obj → PrimeSpectrum R → Type (u + 1))
