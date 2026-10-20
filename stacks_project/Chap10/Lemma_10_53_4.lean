/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Artinian.Ring
import StacksCheckRecall

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsArtinianRing R]

/-!
Lemma 10.53.4: the Jacobson radical of an Artinian ring is a
nilpotent ideal.

@stack 00J8
-/
@[stacks 00J8]
#check (IsSemiprimaryRing.isNilpotent (R := R) :
  IsNilpotent (Ring.jacobson R))

@[stacks 00J8 "Artinian Jacobson radical criterion"]
#check (IsArtinianRing.isNilpotent_jacobson_bot (R := R) :
  IsNilpotent (Ideal.jacobson (⊥ : Ideal R)))
