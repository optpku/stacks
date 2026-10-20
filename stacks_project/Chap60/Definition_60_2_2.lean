/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.«60_2_2_1_Envelope»
import StacksCheckRecall

@[expose] public section

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
variable {I : Ideal A} (γ : DividedPowers I)
variable (f : A →+* B) (J : Ideal B)
variable (hIJ : Ideal.map f I ≤ J)

/- Definition 60.2.2: the divided-power envelope of `J` in `B` relative to
the divided-power ring `(A, I, γ)` is represented by the constructed envelope
owner `DividedPowerEnvelope I γ f J hIJ`. -/
@[stacks 07H9] #check (DividedPowerEnvelope I γ f J hIJ : Type (u + 1))
