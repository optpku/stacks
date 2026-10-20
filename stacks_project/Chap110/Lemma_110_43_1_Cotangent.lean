/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Basic

@[expose] public section

universe u

#check (RingHom.cotangentComplex :
  ∀ {R S : Type u} [CommRing R] [CommRing S],
    (R →+* S) → CochainComplex (ModuleCat.{u} S) ℤ)
