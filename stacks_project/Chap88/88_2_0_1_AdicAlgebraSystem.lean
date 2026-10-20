/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicAlgebraSystem

@[expose] public section

universe u

#check (AdicAlgebraSystem.{u} : ∀ (A : Type u) [CommRing A], Ideal A → Type (u + 1))
